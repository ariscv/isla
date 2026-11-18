#!/usr/bin/env ruby

require 'open3'
require 'optparse'
require 'shellwords'
require 'tmpdir'
include Process

$TEST_DIR = File.expand_path(File.dirname(__FILE__))

$options = {}
OptionParser.new do |opts|
  opts.banner = "Usage: run_tests.rb [options]"

  opts.on("-c", "--config [PATH]", String, "Set config for RISC-V concurrency tests") do |c|
    $options[:config] = File.expand_path c
  end

  opts.on("-m", "--mode [MODE]", String, "Set isarch test mode: all (default) or quick") do |m|
    $options[:mode] = m
  end

  opts.on("-t", "--timeout [SECONDS]", Integer, "Set per-test execution timeout in seconds (default: 60)") do |t|
    $options[:timeout] = t
  end
  opts.on("--property-filter REGEXP", "只运行匹配的 property 文件") do |pattern|
    $options[:property_filter] = Regexp.new(pattern)
  end

  opts.on("--property-bin-dir PATH", "使用已构建的 property 二进制，跳过其他构建") do |dir|
    $options[:property_bin_dir] = File.expand_path(dir)
  end
end.parse!

class String
  def colorize(color_code)
    "\e[#{color_code}m#{self}\e[0m"
  end

  def red
    colorize(91)
  end

  def green
    colorize(92)
  end

  def yellow
    colorize(93)
  end

  def blue
    colorize(94)
  end

  def cyan
    colorize(96)
  end
end

class Dir
  def self.chunks(dir, n, &block)
    passed = true
    Dir.entries(dir).sort.each_slice(n).each do |chunk|
      chunk.each { |file| fork { yield file } }
      passed = Process.waitall.all? { |_, status| status.success? } && passed
    end
    passed
  end
end

def step(str, *extra, timeout: nil, show_output: false, expected_line: nil, assertion_exit: nil)
  expected = extra.fetch(0, 0)
  if timeout then
    # Insert timeout after leading env-var assignments (e.g. LD_LIBRARY_PATH=...)
    cmd = str.sub(/\A((?:[A-Za-z_]\w*=\S+\s+)*)(.*)/, "\\1timeout #{timeout} \\2")
  else
    cmd = str
  end
  stdout, stderr, status = Open3.capture3(cmd)
  if timeout && [124, 137].include?(status.exitstatus) then
    puts <<OUTPUT
#{"Timeout".red} (limit: #{timeout}s): #{str}
#{"stdout".cyan}: #{stdout}
#{"stderr".blue}: #{stderr}
OUTPUT
    exit 1
  end
  mismatch = assertion_exit && status.exitstatus == assertion_exit
  line_matches = !expected_line || stdout.lines.map(&:strip).include?(expected_line)
  unless (status.exitstatus == expected || mismatch) && line_matches
    puts <<OUTPUT
#{"Failed".red} (expected #{expected}, got: #{status}): #{str}
#{"stdout".cyan}: #{stdout}
#{"stderr".blue}: #{stderr}
OUTPUT
    exit 1
  end
  print stdout if show_output || mismatch
  warn stderr if mismatch && !stderr.empty?
  !mismatch
end

# For .timeout tests: pass if timeout (124/137), fail if completed normally
def step_timeout(str, timeout)
  cmd = str.sub(/\A((?:[A-Za-z_]\w*=\S+\s+)*)(.*)/, "\\1timeout #{timeout} \\2")
  stdout, stderr, status = Open3.capture3(cmd)
  if [124, 137].include?(status.exitstatus) then
    return
  end
  puts <<OUTPUT
#{"Failed".red} (expected timeout, but completed with #{status}): #{str}
#{"stdout".cyan}: #{stdout}
#{"stderr".blue}: #{stderr}
OUTPUT
  exit 1
end

def step_print(str)
  if !system str then
    puts <<OUTPUT
#{"Failed".red}: #{str}
OUTPUT
    exit 1
  end
end

def chdir_relative(path)
  Dir.chdir(File.expand_path(File.join($TEST_DIR, path)))
end

def wget(url, file)
  return if File.file?(file)

  system "wget -O #{file} #{url}"
end

def run_property_variant(binary, basename, args, shape)
  config_index = args.index("-C") || args.index("--config")
  config = config_index ? args.slice!(config_index, 2) : ["-C", "../../configs/plain.toml"]
  command = [binary, "-A", "#{basename}.ir", "-p", "prop", "-T", "2", *config, *args]
  shell = 'LD_LIBRARY_PATH=..:$LD_LIBRARY_PATH '
  test_timeout = $options[:timeout] || 60
  if File.extname(basename) == ".timeout"
    step_timeout(shell + Shellwords.join(command), $options[:timeout] || 1)
    return true
  end
  expected = File.extname(basename) == ".unsat" ? 0 : 1
  flags = args.map { |arg| arg.split("=", 2).first }
  count_exit = 2 if flags.include?("--expect-paths")
  expected_line = expected.zero? ? "ok" : "fail"
  unless shape
    diagnostics = (flags & %w[--expect-paths --print-paths --dump-paths]).any?
    return step(shell + Shellwords.join(command), expected, timeout: test_timeout, show_output: diagnostics,
                expected_line: diagnostics ? expected_line : nil, assertion_exit: count_exit)
  end
  Dir.mktmpdir("isla-property-") do |dir|
    dump = File.join(dir, "paths.json")
    count_passed = step(shell + Shellwords.join(command + ["--dump-paths", dump]), expected, timeout: test_timeout,
                        show_output: true, expected_line: expected_line, assertion_exit: count_exit)
    checker = File.join($TEST_DIR, "property/include/check_paths.rb")
    shape_passed = step(Shellwords.join(["ruby", checker, dump, shape]), timeout: test_timeout,
                        show_output: true, assertion_exit: 2)
    count_passed && shape_passed
  end
end

def run_tests()
  chdir_relative "../isla-sail"
  exit 1 unless system "make"
  isla_sail = File.expand_path(File.join($TEST_DIR, "../isla-sail/plugin.cmxs"))
  exit 1 unless File.file?(isla_sail)

  bin_dir = $options[:property_bin_dir]
  unless bin_dir
    chdir_relative "../isla-litmus"
    exit 1 unless system "make"
    exit 1 unless File.file?(File.join($TEST_DIR, "../isla-litmus/isla-litmus"))
    chdir_relative ".."
    exit 1 unless system "cargo build --release"
    bin_dir = File.expand_path(File.join($TEST_DIR, "../target/release"))
  end

  chdir_relative "property"
  filter = $options[:property_filter]
  if filter && Dir.glob("*.sail").none? { |file| filter.match?(file) }
    abort "没有匹配的 property 文件"
  end
  passed = true
  ["", "129"].each do |suffix|
    isla_property = File.join(bin_dir, "isla-property#{suffix}")
    exit 1 unless File.file?(isla_property)

    puts "Running tests [#{suffix}]:".blue

    group_passed = Dir.chunks ".", 12 do |file|
      next unless file.end_with?(".sail") && (!filter || filter.match?(file))

      basename = File.basename(file, ".sail")
      sail_opts_file = "#{basename}.sail_opts"
      sail_opts = File.file?(sail_opts_file) ? File.read(sail_opts_file) : ""
      building = Process.clock_gettime(Process::CLOCK_MONOTONIC)
      step("sail -plugin #{Shellwords.escape(isla_sail)} -isla #{Shellwords.escape(file)} include/config.sail -o #{Shellwords.escape(basename)} #{sail_opts}")
      built = Process.clock_gettime(Process::CLOCK_MONOTONIC)

      variants = Dir.glob("#{basename}.*.opts").sort
      base_opts = "#{basename}.opts"
      variants.unshift(base_opts) if variants.empty? || File.file?(base_opts)
      variants_passed = true
      variants.each do |options_file|
        variant = options_file.delete_suffix(".opts")
        args = File.file?(options_file) ? Shellwords.split(File.read(options_file)) : []
        shape = ["#{variant}.shape", "#{basename}.shape"].uniq.find { |path| File.file?(path) }
        marker = "#{variant}.xfail"
        xfail = File.file?(marker) ? File.read(marker).strip : nil
        abort "#{marker} 必须说明预期失败原因" if xfail&.empty?
        label = (file + variant.delete_prefix(basename)).ljust(48) + " "
        start = Process.clock_gettime(Process::CLOCK_MONOTONIC)
        pid = fork { exit(run_property_variant(isla_property, basename, args, shape) ? 0 : 2) }
        _, status = Process.wait2(pid)
        ending = Process.clock_gettime(Process::CLOCK_MONOTONIC)
        build_ms = ((built - building) * 1000).to_i
        run_ms = ((ending - start) * 1000).to_i
        timing = "(#{build_ms}ms/#{run_ms}ms)"
        if xfail && status.exitstatus == 2
          puts "#{label}#{"XFAIL".yellow} #{timing} #{xfail}"
        elsif xfail && status.success?
          puts "#{label}#{"XPASS".red} #{timing} 请删除 #{marker}"
          variants_passed = false
        elsif status.success?
          puts "#{label}#{"ok".green} #{timing} #{Shellwords.join(args)}"
        else
          puts "#{label}#{"Failed".red} #{timing} (#{status})"
          variants_passed = false
        end
      end
      exit 1 unless variants_passed
    end
    passed = group_passed && passed

    if suffix.empty? && !filter && !$options[:property_bin_dir] && passed
      generated_ir = Shellwords.escape(File.expand_path("source_region_foreach_match.unsat.ir"))
      manifest = Shellwords.escape(File.expand_path("../../Cargo.toml"))
      step(
        "ISLA_SOURCE_REGION_TEST_IR=#{generated_ir} cargo test --manifest-path #{manifest} -p isla-lib source_region_generated_ir_matches_fixture --lib"
      )
    end
  end
  exit 1 unless passed

  # isla_axiomatic = File.expand_path(File.join($TEST_DIR, "../target/release/isla-axiomatic"))
  # exit 1 if !File.file?(isla_axiomatic)

  # chdir_relative "."

  # axiomatic = File.expand_path(File.join($TEST_DIR, "/axiomatic"))
  # arch = "#{axiomatic}/riscv64.ir"
  # wget("https://raw.githubusercontent.com/rems-project/isla-snapshots/master/riscv64.ir", arch)
  # system "md5sum #{arch}"


  # riscv_cat = File.expand_path(File.join($TEST_DIR, "../web/client/dist/riscv.cat"))

  # step_print("LD_LIBRARY_PATH=..:$LD_LIBRARY_PATH #{isla_axiomatic} -A #{arch} -C #{$options[:config]} -m #{riscv_cat} -t #{axiomatic}/tests --refs #{axiomatic}/refs")
end

def run_isarch_tests
  isarch_bin = File.expand_path(File.join($TEST_DIR, "../target/release/isarch"))
  if !File.file?(isarch_bin) then
    puts "Skipping isarch tests (binary not found)".yellow
    return
  end

  repo_root = File.expand_path(File.join($TEST_DIR, ".."))
  config = $options[:config] || File.expand_path(File.join(repo_root, "configs/riscv64.toml"))

  puts "Running isarch tests:".blue

  env = {
    "ISARCH_BIN"  => isarch_bin,
    "IR_FILE"     => File.expand_path(File.join(repo_root, "rv64d.ir")),
    "CONFIG_FILE" => config,
  }

  test_script = File.expand_path(File.join($TEST_DIR, "isarch/test_isarch.sh"))

  mode = $options[:mode] || "all"
  stdout, stderr, status = Open3.capture3(env, "bash #{test_script} #{mode}")
  puts stdout
  if status.exitstatus != 0 then
    puts "isarch tests #{"Failed".red}"
    puts "stderr: #{stderr}" if !stderr.empty?
    exit 1
  end
  puts "isarch tests #{"ok".green}"
end

run_tests
# run_isarch_tests

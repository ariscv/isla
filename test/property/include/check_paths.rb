# 比较实际 SMT 守卫与预期谓词在指定有限输入域上的投影。
require 'json'
require 'open3'

dump_file, shape_file = ARGV
expected = File.readlines(shape_file, chomp: true).map(&:strip).reject { |line| line.empty? || line.start_with?(";") }
inputs = {}
while (declaration = expected.first&.match(/\A\(declare-const (\w+) \(_ BitVec ([1-9][0-9]*)\)\)\z/))
  inputs[declaration[1]] = Integer(declaration[2])
  expected.shift
end
abort "#{shape_file} 需要声明输入和至少一个谓词" if inputs.empty? || expected.empty?
tuples = inputs.values.map { |width| (0...(1 << width)).to_a }
tuples = tuples.first.product(*tuples.drop(1))

def covered_inputs(guard, names, widths, tuples)
  queries = tuples.map do |tuple|
    equalities = names.zip(widths, tuple).map { |name, width, value| "(= #{name} (_ bv#{value} #{width}))" }
    "(push 1)\n(assert (and #{equalities.join(' ')}))\n(check-sat)\n(pop 1)"
  end
  stdout, stderr, status = Open3.capture3("z3", "-in", "-smt2", stdin_data: ([guard] + queries).join("\n"))
  replies = stdout.lines.map(&:strip)
  unless status.success? && replies.length == tuples.length && replies.all? { |reply| %w[sat unsat].include?(reply) }
    abort "Z3 守卫重放失败\n#{stdout}#{stderr}"
  end
  tuples.select.with_index { |_, i| replies[i] == "sat" }
end

declarations = inputs.map { |name, width| "(declare-const #{name} (_ BitVec #{width}))" }
wanted = expected.map do |predicate|
  covered_inputs((declarations + ["(assert #{predicate})"]).join("\n"), inputs.keys, inputs.values, tuples)
end.sort
actual = JSON.parse(File.read(dump_file)).map do |path|
  registers = path.fetch("register_writes")
  expressions = inputs.keys.map { |name| registers.fetch(name) }
  covered_inputs(path.fetch("guard_smtlib"), expressions, inputs.values, tuples)
end.sort
abort "形状不符（#{inputs.keys.join(', ')}）\n期望 #{wanted.inspect}\n实际 #{actual.inspect}" unless wanted == actual

puts "形状通过（#{inputs.keys.join(', ')}） #{actual.inspect}"

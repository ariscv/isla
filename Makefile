.PHONY: all run isla-sail isla-litmus isla web test fmt clean install uninstall update

RUN_BASE_ENV = \
	RUST_BACKTRACE=1 \
	RUSTFLAGS=-Awarnings

RUN_PROFILE_ENV = \
	ISLA_RISCV_PROFILE_FORKS=1

RUN_VMEM_ENV = \
	ISLA_RISCV_VMEM_BUILTIN_MODE=on \
	ISLA_RISCV_VMEM_ASSUME_ALIGNED=1

RUN_ACCESS_ENV = \
	ISLA_RISCV_ASSUME_PMP_OFF=1 \
	ISLA_RISCV_BUILTIN_PMP_CHECK=1 \
	ISLA_RISCV_BUILTIN_PMA_CHECK=1 \
	ISLA_RISCV_BUILTIN_PHYS_ACCESS_CHECK=1

RUN_MMIO_ENV = \
	ISLA_RISCV_BUILTIN_WITHIN_MMIO=1 \
	ISLA_RISCV_BUILTIN_CLINT_LOAD=0 \
	ISLA_RISCV_ASSUME_CLINT_OFF=1

RUN_TEST_ENV = \
	ISLA_RISCV_TEST_ZSTORE_WIDTH=4 \
	ISLA_RISCV_TEST_ZLOAD_WIDTH=4

RUN_RISCV_ENV = \
	$(RUN_PROFILE_ENV) \
	$(RUN_VMEM_ENV) \
	$(RUN_ACCESS_ENV) \
	$(RUN_MMIO_ENV) \
	$(RUN_TEST_ENV)

RUN_ISARCH_ARGS = \
	-A ./rv64d.ir \
	-C ./configs/riscv64_difftest.toml \
	--verbose --probe-all --trace-all \
	-I cur_privilege=Supervisor \
	list-instructions

run:
	cargo fmt && cp log log.1 \
		&& env $(RUN_BASE_ENV) $(RUN_RISCV_ENV) bash -c "cargo run --quiet --bin isarch --release \
		-- $(RUN_ISARCH_ARGS) >log 2> >(tee -a log >&2) "

all: isla

isla:
	cargo build --release

check:
	cargo check --release

isla-sail:
	$(MAKE) -C isla-sail isla-sail

isla-litmus:
	$(MAKE) -C isla-litmus isla-litmus

web:
	$(MAKE) -C web all

test:
	test/run_tests.rb --config configs/riscv64.toml
	$(MAKE) -C isla-lib test
	$(MAKE) -C isla-cat test
	$(MAKE) -C isla-elf test
	$(MAKE) -C isla-axiomatic test

test-github:
	test/run_tests.rb --config configs/riscv64_ubuntu.toml
	$(MAKE) -C isla-lib test
	$(MAKE) -C isla-cat test
	$(MAKE) -C isla-axiomatic test

fmt:
	$(MAKE) -C isla-lib fmt
	$(MAKE) -C isla-cat fmt
	$(MAKE) -C isla-axiomatic fmt
	$(MAKE) -C isla-mml fmt
	$(MAKE) -C isla-elf fmt
	$(MAKE) -C web fmt
	cargo fmt

clean:
	-$(MAKE) -C isla-sail clean
	-$(MAKE) -C isla-litmus clean
	-$(MAKE) -C isla-cat clean
	-$(MAKE) -C isla-elf clean
	-$(MAKE) -C web clean
	-cargo clean

install: all
	@cargo install --locked --path .

uninstall:
	@cargo uninstall isla

update: uninstall install

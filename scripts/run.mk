ALL=ADDIW AES32DSI AES32DSMI AES32ESI AES32ESMI AES64DS AES64DSM \
AES64ES AES64ESM AES64IM AES64KS1I AES64KS2 AMO BITYPE BREV8 BTYPE \
CLMUL CLMULH CLMULR CLZ CLZW CPOP CPOPW CSRImm CSRReg CTZ CTZW C_ADD \
C_ADDI C_ADDI16SP C_ADDI4SPN C_ADDIW C_ADDW C_AND C_ANDI C_BEQZ \
C_BNEZ C_EBREAK C_FLD C_FLDSP C_FLW C_FLWSP C_FSD C_FSDSP C_FSW \
C_FSWSP C_ILLEGAL C_J C_JAL C_JALR C_JR C_LBU C_LD C_LDSP C_LH \
C_LHU C_LI C_LUI C_LW C_LWSP C_MUL C_MV C_NOP C_NOT C_NTL C_OR \
C_SB C_SD C_SDSP C_SEXT_B C_SEXT_H C_SH C_SLLI C_SRAI C_SRLI \
C_SUB C_SUBW C_SW C_SWSP C_XOR C_ZEXT_B C_ZEXT_H C_ZEXT_W DIV \
DIVW EBREAK ECALL FCVTMOD_W_D FCVT_BF16_S FCVT_S_BF16 FENCE \
FENCEI FENCE_TSO FLEQ_D FLEQ_H FLEQ_S FLI_D FLI_H FLI_S FLTQ_D \
FLTQ_H FLTQ_S FMAXM_D FMAXM_H FMAXM_S FMINM_D FMINM_H \
FMINM_S FMVH_X_D FMVP_D_X FROUNDNX_D FROUNDNX_H FROUNDNX_S \
FROUND_D FROUND_H FROUND_S FVFMATYPE FVFMTYPE FVFTYPE FVVMATYPE \
FVVMTYPE FVVTYPE FWFTYPE FWVFMATYPE FWVFTYPE FWVTYPE FWVVMATYPE \
FWVVTYPE F_BIN_F_TYPE_D F_BIN_F_TYPE_H F_BIN_RM_TYPE_D \
F_BIN_RM_TYPE_H F_BIN_RM_TYPE_S F_BIN_TYPE_F_S F_BIN_TYPE_X_S \
F_BIN_X_TYPE_D F_BIN_X_TYPE_H F_MADD_TYPE_D F_MADD_TYPE_H \
F_MADD_TYPE_S F_UN_F_TYPE_D F_UN_F_TYPE_H F_UN_RM_FF_TYPE_D \
F_UN_RM_FF_TYPE_H F_UN_RM_FF_TYPE_S F_UN_RM_FX_TYPE_D \
F_UN_RM_FX_TYPE_H F_UN_RM_FX_TYPE_S F_UN_RM_XF_TYPE_D \
F_UN_RM_XF_TYPE_H F_UN_RM_XF_TYPE_S F_UN_TYPE_F_S F_UN_TYPE_X_S \
F_UN_X_TYPE_D F_UN_X_TYPE_H ILLEGAL ITYPE JAL JALR LOAD LOADRES \
LOAD_FP LPAD MASKTYPEI MASKTYPEV MASKTYPEX MMTYPE MOVETYPEI \
MOVETYPEV MOVETYPEX MRET MUL MULW MVVCOMPRESS MVVMATYPE MVVTYPE \
MVXMATYPE MVXTYPE NISTYPE NITYPE NTL NVSTYPE NVTYPE NXSTYPE \
NXTYPE ORCB PAUSE REM REMW REV8 RFVVTYPE RFWVVTYPE RIVVTYPE \
RMVVTYPE RORI RORIW RTYPE RTYPEW SFENCE_INVAL_IR SFENCE_VMA \
SFENCE_W_INVAL SHA256SIG0 SHA256SIG1 SHA256SUM0 SHA256SUM1 \
SHA512SIG0 SHA512SIG0H SHA512SIG0L SHA512SIG1 SHA512SIG1H \
SHA512SIG1L SHA512SUM0 SHA512SUM0R SHA512SUM1 SHA512SUM1R \
SHIFTIOP SHIFTIWOP SINVAL_VMA SLLIUW SM3P0 SM3P1 SM4ED SM4KS \
SRET STORE STORECON STORE_FP UNZIP UTYPE VABS_V VAESDF VAESDM \
VAESEF VAESEM VAESKF1_VI VAESKF2_VI VAESZ_VS VANDN_VV VANDN_VX \
VBREV8_V VBREV_V VCLMULH_VV VCLMULH_VX VCLMUL_VV VCLMUL_VX \
VCLZ_V VCPOP_M VCPOP_V VCTZ_V VEXTTYPE VFIRST_M VFMERGE VFMV \
VFMVFS VFMVSF VFNCVTBF16_F_F_W VFNUNARY0 VFUNARY0 VFUNARY1 \
VFWCVTBF16_F_F_V VFWMACCBF16_VF VFWMACCBF16_VV VFWUNARY0 \
VGHSH_VV VGMUL_VV VICMPTYPE VID_V VIMCTYPE VIMSTYPE VIMTYPE \
VIOTA_M VISG VITYPE VLRETYPE VLSEGFFTYPE VLSEGTYPE VLSSEGTYPE \
VLXSEGTYPE VMSBF_M VMSIF_M VMSOF_M VMTYPE VMVRTYPE VMVSX VMVXS \
VREV8_V VROL_VV VROL_VX VROR_VI VROR_VV VROR_VX VSETIVLI VSETVL \
VSETVLI VSHA2MS_VV VSM3C_VI VSM3ME_VV VSM4K_VI VSRETYPE \
VSSEGTYPE VSSSEGTYPE VSXSEGTYPE VVCMPTYPE VVMCTYPE VVMSTYPE \
VVMTYPE VVTYPE VWSLL_VI VWSLL_VV VWSLL_VX VXCMPTYPE VXMCTYPE \
VXMSTYPE VXMTYPE VXSG VXTYPE WFI WMVVTYPE WMVXTYPE WRS WVTYPE \
WVVTYPE WVXTYPE WXTYPE XPERM4 XPERM8 ZBA_RTYPE ZBA_RTYPEUW \
ZBB_EXTOP ZBB_RTYPE ZBB_RTYPEW ZBKB_PACKW ZBKB_RTYPE ZBS_IOP \
ZBS_RTYPE ZCMOP ZICBOM ZICBOP ZICBOZ ZICOND_RTYPE ZIMOP_MOP_R \
ZIMOP_MOP_RR ZIP ZVABDTYPE ZVKSHA2TYPE ZVKSM4RTYPE ZVWABDATYPE 

# FD/浮点相关的 clause 先单独放在这里，默认 solve 不跑。
FD_FLOAT=C_FLD C_FLDSP C_FLW C_FLWSP C_FSD C_FSDSP C_FSW C_FSWSP \
FCVTMOD_W_D FCVT_BF16_S FCVT_S_BF16 FLEQ_D FLEQ_H FLEQ_S FLI_D \
FLI_H FLI_S FLTQ_D FLTQ_H FLTQ_S FMAXM_D FMAXM_H FMAXM_S \
FMINM_D FMINM_H FMINM_S FMVH_X_D FMVP_D_X FROUNDNX_D FROUNDNX_H \
FROUNDNX_S FROUND_D FROUND_H FROUND_S FVFMATYPE FVFMTYPE FVFTYPE \
FVVMATYPE FVVMTYPE FVVTYPE FWFTYPE FWVFMATYPE FWVFTYPE FWVTYPE \
FWVVMATYPE FWVVTYPE F_BIN_F_TYPE_D F_BIN_F_TYPE_H F_BIN_RM_TYPE_D \
F_BIN_RM_TYPE_H F_BIN_RM_TYPE_S F_BIN_TYPE_F_S F_BIN_TYPE_X_S \
F_BIN_X_TYPE_D F_BIN_X_TYPE_H F_MADD_TYPE_D F_MADD_TYPE_H \
F_MADD_TYPE_S F_UN_F_TYPE_D F_UN_F_TYPE_H F_UN_RM_FF_TYPE_D \
F_UN_RM_FF_TYPE_H F_UN_RM_FF_TYPE_S F_UN_RM_FX_TYPE_D \
F_UN_RM_FX_TYPE_H F_UN_RM_FX_TYPE_S F_UN_RM_XF_TYPE_D \
F_UN_RM_XF_TYPE_H F_UN_RM_XF_TYPE_S F_UN_TYPE_F_S F_UN_TYPE_X_S \
F_UN_X_TYPE_D F_UN_X_TYPE_H LOAD_FP RFVVTYPE RFWVVTYPE STORE_FP \
VFMERGE VFMV VFMVFS VFMVSF VFNCVTBF16_F_F_W VFNUNARY0 VFUNARY0 \
VFUNARY1 VFWCVTBF16_F_F_V VFWMACCBF16_VF VFWMACCBF16_VV VFWUNARY0

# 内存符号化支持尚不完整，默认 solve 先跳过实际访存、缓存块、fence/TLB 类 clause。
MEMORY=AMO LOAD LOADRES STORE STORECON \
C_LBU C_LD C_LDSP C_LH C_LHU C_LW C_LWSP C_SB C_SD C_SDSP C_SH \
C_SW C_SWSP C_FLD C_FLDSP C_FLW C_FLWSP C_FSD C_FSDSP C_FSW C_FSWSP \
LOAD_FP STORE_FP VLRETYPE VLSEGFFTYPE VLSEGTYPE VLSSEGTYPE VLXSEGTYPE \
VMTYPE VSRETYPE VSSEGTYPE VSSSEGTYPE VSXSEGTYPE ZICBOM ZICBOP ZICBOZ \
FENCE FENCEI FENCE_TSO SFENCE_INVAL_IR SFENCE_VMA SFENCE_W_INVAL SINVAL_VMA

ACTIVE_ALL=$(filter-out $(FD_FLOAT) $(MEMORY),$(ALL))

# 进度计数器：make solve 开始时重置为 0，每个 solve-% 启动时用 flock 原子自增取号，
# 配合下面的 TOTAL 打印形如 [3/243] solve-REM 的进度（类似 ninja/cmake 的 [n/total]）。
COUNTER=output/.solve_progress_counter
# isarch 多线程执行的工作线程数（-T），默认 64；单测可 `make solve-X THREADS=110` 覆盖
THREADS ?= 64
# solve 使用的 IR；默认的 ./rv64d.ir 已是 VLEN=128、ELEN=64，其 SHA-256 与
# configs/workarounds/vvtype.toml 的 ir_sha256 对应，换 IR 时两者必须同步更新。
IR_FILE ?= ./rv64d.ir
# solve 使用的 Isla 运行时配置；实验扩展 clause 可通过 target-specific value 覆盖。
ISA_CONFIG ?= ./configs/riscv64_difftest.toml
# itrace 默认关闭；需要调试时使用 `make solve-XXX ITRACE=1` 开启。
ITRACE ?= 0
CARGO_ITRACE_FEATURE = $(if $(filter 1 yes true on,$(ITRACE)),--features itrace,)
# solve 使用 Homebrew 的 Z3。z3-sys 直接以 -lz3 链接，故必须同时提供链接搜索路径
# 与运行时 rpath；否则系统 libz3 会在 `make` 重建 isarch 时覆盖手工验证的 Brew Z3。
Z3_PREFIX ?= /home/linuxbrew/.linuxbrew/opt/z3
Z3_RUSTFLAGS = -L native=$(Z3_PREFIX)/lib -C link-arg=-Wl,-rpath,$(Z3_PREFIX)/lib
# 可选 Z3 tactic；例如 `make solve-VVTYPE TASTIC=qfaufbv`。
TASTIC ?=
# 可选的独立 execution-limit TOML；下方有局部路径爆炸的 clause 加载各自的 workaround。
EXECUTION_LIMITS_CONFIG ?=
solve-VVTYPE: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vvtype.toml
solve-MASKTYPEI: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/masktypei.toml
solve-MASKTYPEV: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/masktypev.toml
solve-MASKTYPEX: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/masktypex.toml
solve-MVVTYPE: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/mvvtype.toml
solve-MVXTYPE: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/mvxtype.toml
solve-VXTYPE: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vxtype.toml
solve-VXTYPE: OUTER_TIMEOUT = 90m
solve-VXTYPE: SOLVE_TIMEOUT = 85m
solve-MVXMATYPE: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/mvxmatype.toml
solve-NISTYPE: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/nistype.toml
solve-NITYPE: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/nitype.toml
solve-VITYPE: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vitype.toml
solve-VIMSTYPE: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vimstype.toml
solve-VICMPTYPE: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vicmptype.toml
solve-VVCMPTYPE: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vvcmptype.toml
solve-VXCMPTYPE: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vxcmptype.toml
solve-VXMTYPE: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vxmtype.toml
solve-VXSG: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vxsg.toml
solve-NVTYPE: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/nvtype.toml
solve-NXSTYPE: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/nxstype.toml
solve-NXTYPE: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/nxtype.toml
solve-VIMTYPE: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vimtype.toml
solve-VIMCTYPE: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vimctype.toml
solve-VVMCTYPE: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vvmctype.toml
solve-VXMCTYPE: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vxmctype.toml
solve-VXMSTYPE: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vxmstype.toml
solve-VVMSTYPE: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vvmstype.toml
solve-VVMTYPE: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vvmtype.toml
solve-VMTYPE: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vmtype.toml
solve-VISG: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/visg.toml
solve-MVVCOMPRESS: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/mvvcompress.toml
solve-VMVRTYPE: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vmvrtype.toml
solve-VEXTTYPE: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vexttype.toml
solve-RIVVTYPE: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/rivvtype.toml
solve-RMVVTYPE: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/rmvvtype.toml
solve-VANDN_VV: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vandn_vv.toml
solve-VANDN_VX: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vandn_vx.toml
solve-VCLMULH_VV: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vclmulh_vv.toml
solve-VCLMULH_VX: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vclmulh_vx.toml
solve-VCLMUL_VV: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vclmul_vv.toml
solve-VCLMUL_VX: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vclmul_vx.toml
solve-VBREV_V: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vbrev_v.toml
solve-VBREV8_V: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vbrev8_v.toml
solve-VREV8_V: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vrev8_v.toml
solve-VCLZ_V: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vclz_v.toml
solve-VCTZ_V: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vctz_v.toml
solve-VROL_VV: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vrol_vv.toml
solve-VROL_VX: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vrol_vx.toml
solve-VROR_VI: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vror_vi.toml
solve-VROR_VV: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vror_vv.toml
solve-VROR_VX: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vror_vx.toml
solve-VWSLL_VI: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vwsll_vi.toml
solve-VWSLL_VV: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vwsll_vv.toml
solve-VWSLL_VX: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vwsll_vx.toml
solve-VAESDF: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vaesdf.toml
solve-VAESDM: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vaesdm.toml
solve-VAESEF: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vaesef.toml
solve-VAESEM: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vaesem.toml
solve-VAESKF1_VI: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vaeskf1_vi.toml
solve-VAESKF2_VI: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vaeskf2_vi.toml
solve-VGHSH_VV: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vghsh_vv.toml
solve-VGMUL_VV: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vgmul_vv.toml
solve-VSM3C_VI: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vsm3c_vi.toml
solve-VSM3ME_VV: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vsm3me_vv.toml
solve-VSM4K_VI: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vsm4k_vi.toml
solve-VSHA2MS_VV: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vsha2ms_vv.toml
solve-ZVKSHA2TYPE: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/zvksha2type.toml
solve-ZVKSM4RTYPE: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/zvksm4rtype.toml
solve-ZVABDTYPE: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/zvabdtype.toml
solve-ZVABDTYPE: ISA_CONFIG = ./configs/riscv64_difftest_vabs_v.toml
solve-ZVWABDATYPE: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/zvwabdatatype.toml
solve-ZVWABDATYPE: ISA_CONFIG = ./configs/riscv64_difftest_vabs_v.toml
solve-VFMERGE: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vfmerge.toml
solve-VFMERGE: ISA_CONFIG = ./configs/riscv64_difftest_fd.toml
solve-VFMV: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vfmv.toml
solve-VFMV: ISA_CONFIG = ./configs/riscv64_difftest_fd.toml
solve-VFMVFS: ISA_CONFIG = ./configs/riscv64_difftest_fd.toml
solve-VFMVSF: ISA_CONFIG = ./configs/riscv64_difftest_fd.toml
solve-VCPOP_V: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vcpop_v.toml
solve-VCPOP_M: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vcpop_m.toml
solve-VFIRST_M: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vfirst_m.toml
solve-VMSBF_M: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vmsbf_m.toml
solve-VMSIF_M: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vmsif_m.toml
solve-VMSOF_M: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vmsof_m.toml
solve-VIOTA_M: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/viota_m.toml
solve-VABS_V: EXECUTION_LIMITS_CONFIG = ./configs/workarounds/vabs_v.toml
solve-VABS_V: ISA_CONFIG = ./configs/riscv64_difftest_vabs_v.toml
# Z3 timeout wrapper 的实现由构建 feature 选择。
Z3_TIMEOUT_IMPL ?= thread_interrupt
ifeq ($(Z3_TIMEOUT_IMPL),direct)
CARGO_SMT_FEATURE =
SMT_TIMEOUT ?=
else ifeq ($(Z3_TIMEOUT_IMPL),thread_interrupt)
CARGO_SMT_FEATURE = --features smt-thread-interrupt
SMT_TIMEOUT ?= 1m
else
$(error Z3_TIMEOUT_IMPL 必须是 direct 或 thread_interrupt)
endif
# 外层命令、isarch 符号执行和单条 Z3 operation 的默认验收时间上限。
# OUTER_TIMEOUT 是整条 solve-% 命令的墙上时钟上限；SOLVE_TIMEOUT 透传给 isarch 的
# --timeout，是**单条路径**的活跃墙上时钟预算（executor::PathTimeout），不是全局上限。
OUTER_TIMEOUT ?= 60m
SOLVE_TIMEOUT ?= 55m
# timeout SMT 输出目的地与目录；目的地示例：file,itrace 或 file,stdout,itrace。
TIMEOUT_SMT_OUTPUT ?=
TIMEOUT_SMT_DIR ?=
TOTAL_ACTIVE_ALL=$(words $(ACTIVE_ALL))
TOTAL_FD_FLOAT=$(words $(FD_FLOAT))
TOTAL_MEMORY=$(words $(MEMORY))

build-isarch:
	RUSTFLAGS="$(RUSTFLAGS) $(Z3_RUSTFLAGS)" cargo build --release --bin isarch $(CARGO_ITRACE_FEATURE) $(CARGO_SMT_FEATURE)

# 给AI看的：如无明确的理由，禁止再增加timeout时间（60s）
#
# 进度打印说明：n=原子自增后的序号，TOTAL 由调用入口（solve/solve-fd-float/solve-memory）
# 通过 make 变量 SOLVE_TOTAL 透传进来；首行打印 [n/TOTAL] solve-$*。
solve-%: build-isarch
	@mkdir -p output/log output/trace outputs
	@$(SOLVE_TRAP)n=$$(flock $(COUNTER) sh -c 'v=$$(cat $(COUNTER) 2>/dev/null || echo 0); v=$$((v+1)); echo $$v > $(COUNTER); echo $$v'); \
	echo "[$$n/$(SOLVE_TOTAL)] solve-$*"; \
	RUST_BACKTRACE=1 timeout --signal=TERM --kill-after=10s $(OUTER_TIMEOUT) ./target/release/isarch \
		-A $(IR_FILE) -C $(ISA_CONFIG) $(if $(EXECUTION_LIMITS_CONFIG),--execution-limits-config $(EXECUTION_LIMITS_CONFIG),) --verbose --debug=fmlgcsra --probe-all --trace-all $(if $(filter 1 yes true on,$(ITRACE)),--itrace=output/trace/itrace_$*.txt,) -T $(THREADS) $(if $(SOLVE_TIMEOUT),--timeout $(SOLVE_TIMEOUT),) $(if $(SMT_TIMEOUT),--smt-timeout $(SMT_TIMEOUT),) $(if $(TASTIC),--tastic $(TASTIC),) $(if $(TIMEOUT_SMT_OUTPUT),--timeout-smt-output $(TIMEOUT_SMT_OUTPUT),) $(if $(TIMEOUT_SMT_DIR),--timeout-smt-dir $(TIMEOUT_SMT_DIR),) solve-state --clause=$* \
		> output/log/$*.log 2>&1; \
	status=$$?; \
	if [ $$status -eq 124 ]; then \
		echo "$* timeout" >> output/status.timeout.log; \
	elif [ $$status -eq 0 ]; then \
		echo "$* intime" >> output/status.intime.log; \
	else \
		echo "$* failed ($$status)" >> output/status.failed.log; \
	fi; \
	exit $$status

SOLVE_TARGETS=$(addprefix solve-,$(ACTIVE_ALL))
FD_FLOAT_SOLVE_TARGETS=$(addprefix solve-,$(FD_FLOAT))
MEMORY_SOLVE_TARGETS=$(addprefix solve-,$(MEMORY))

.PHONY: build-isarch solve solve-fd-float solve-memory
# Ctrl-C 清理是【可选插件】：scripts/run_ctrl_c.mk 若存在，会给 solve-% 注入 Ctrl-C 清理逻辑
# （pkill 掉后台 isarch）；缺失则不影响。-include 保证缺失不报错。
-include scripts/run_ctrl_c.mk

# solve-pre 作为所有 solve-XXX 的【真前置依赖】：make 的拓扑顺序保证它先跑完（重置进度
# 计数器、建目录），其后才并行跑各 solve-%，避免计数器竞态，且不阻塞并行。
$(SOLVE_TARGETS) $(FD_FLOAT_SOLVE_TARGETS) $(MEMORY_SOLVE_TARGETS): solve-pre
solve-pre:
	@mkdir -p output/log output/trace outputs && echo 0 > $(COUNTER)
.PHONY: solve-pre

# 三个入口各自把对应的 SOLVE_TOTAL 作为 target-specific 变量传给依赖的 solve-% pattern rule，
# 然后【直接依赖】目标——单 make 进程并行跑（-j 正常生效、jobserver 不丢），无需递归 make。
# （此前用“递归 make 注入 SOLVE_TOTAL”的写法会断 jobserver、降级串行，故弃用。）
solve: SOLVE_TOTAL := $(TOTAL_ACTIVE_ALL)
solve: $(SOLVE_TARGETS)
solve-fd-float: SOLVE_TOTAL := $(TOTAL_FD_FLOAT)
solve-fd-float: $(FD_FLOAT_SOLVE_TARGETS)
solve-memory: SOLVE_TOTAL := $(TOTAL_MEMORY)
solve-memory: $(MEMORY_SOLVE_TARGETS)

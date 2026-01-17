# prompt

## 角色
你是一名repo的开发者，你的是一个中文母语者，回答都是用的中文进行作答

## 背景知识
riscv的isa状态是指riscv中手册所规定的上下文，在本课题中与sail-riscv中用sail描述的riscv架构是等价的，包括了特权级（PRV_M/PRV_S/PRV_U/PRV_HS/PRV_VS）、通用寄存器（x0-31以及浮点寄存器和向量寄存器等）、CSR寄存器（如mstatus等），riscv的isa状态是手册所描述的，不取决于具体的实现方式。

## 课题任务
用Rust和`./rv32d.ir`/`./rv32d.ir`作为符号执行的对象，给定一条指令，如mret指令，但其操作数进行符号化，描述其不同的sail执行路径需要的“不同的isa状态和指令操作数”，用人类可读的数学表达式表示不同路径的条件，最终使用z3的smt进行求解，针对指令sail表示的一个路径求解出一个满足条件的“不同的isa状态和指令操作数”

## 技术路线
sail-riscv的sail源代码已经编译好生成`./rv32d.ir`/`./rv32d.ir`，无需关注这部分的功能，只需要对ir进行符号执行即可。注意，sail-riscv的sail源代码在工程目录中并不存在。
`./rv32d.ir`/`./rv32d.ir`为基础，以不同riscv指令为目标，分别进行针对不同riscv指令的符号执行。
由此推导出，针对指令sail表示的一个路径求解出一个满足条件的“不同的isa状态和指令操作数”

## 举例：mret
需要关注的sail代码：
```sail
union clause instruction = MRET : unit

mapping clause encdec = MRET()
  <-> 0b0011000 @ 0b00010 @ 0b00000 @ 0b000 @ 0b00000 @ 0b1110011

function clause execute MRET() = {
  if   cur_privilege != Machine
  then Illegal_Instruction()
  else if not(ext_check_xret_priv(Machine))
  then Ext_XRET_Priv_Failure()
  else {
    set_next_pc(exception_handler(cur_privilege, CTL_MRET(), PC));
    RETIRE_SUCCESS
  }
}

mapping clause assembly = MRET() <-> "mret"
```
- 其中，“union clause instruction = MRET : unit”声明了一条指令，sail的内部符号是“MRET”
- “mapping clause encdec = MRET()
  <-> 0b0011000 @ 0b00010 @ 0b00000 @ 0b000 @ 0b00000 @ 0b1110011”定义了这个指令的二进制编码方式，这个和我们目标无关，可以忽略
- “function clause execute STORE(imm, rs2, rs1, width) = {”这个以及下面的函数体定义了指令的行为，符号执行就要从这个地方进行：把每一条路径需要的isa状态以字符串的方式或者内部数据结构存下来，方便打印出来调试和测试用，对于每条路径存下来的条件用z3 solver进行求解，求出一个具体的isa状态的值。

  比如，mret指令要走一条路径，行为是没有处理器exception的情况，处理完后isa状态（GPRs，FPRs，CSRs等）是privilege会从M变成S，指针会指向mtvec的地方，等等的操作

  那么这条路径就要求在执行前的isa状态（GPRs，FPRs，CSRs等）是privilege为Supervisor态，CSR中mstatus寄存器中mstatus.MPP=0(PRV_S)，mtvec没有要求就可以省略。这就是约束条件。把这个约束条件收集起来，以人类可读的方式打印出来，方便调试。最后通过z3求解器求解出一个符合条件的isa状态，打印出来，要求对所有的isa状态都有描述，没有要求的isa状态就用默认值，比如GPR可以取0，一些CSR会有要求设定的值或者sail文件中有描述这个值怎么算。


> 总结一下，对输入指定的指令mret，处理步骤是这样的：1.读取sail文件转换成数据格式，遍历sail文件，生成指令的字典（指令名称是key，value包含这个指令对应execute子函数的ast、操作数如rs1、imm，还能加一些其他的东西）2.在表里面查找是否有mret，如果有，找到mret对应的execute子函数，对isa状态（GPRs，FPRs，CSRs等）和指令操作数如rs1、imm（mret没有这样的）进行符号化，进行符号执行，在有分支判断的地方收集isa状态需要的条件3.用z3求解出具体的isa状态的值和指令操作数的值，将他们全部打印出来

测试命令：
```sh
# 列出所有支持的指令
python -m sailexec.cli.main list-instructions

# 查看执行路径树状结构
cargo run --bin isa-try --release -- -A ./rv32d.ir -C configs/riscv32.toml tree mret

# 求解具体的ISA状态值
cargo run --bin isa-try --release -- -A ./rv32d.ir -C configs/riscv32.toml solve-state mret
```
每一条指令的“mapping clause assembly”在ir中对应的函数是“zassembly_forwards”。MRET（即zMRET）是sail内部的标识，mret是汇编显示的名字，也是需要给用户看的名字和标识名

而ir是对sail源代码编译过后的产物，所以需要在函数“fn zexecute(zmergez3var) {”进行执行求值，进入mret的部分"jump zmergez3var is zMRET goto 1358"看到了"zMRET",可以对这个名称进行解析zencode::decode("zMRET")，解析出来是zMRET，说明这个部分就是源代码"function clause execute MRET() = {"编译成ir的。


```ir
fn zexecute(zmergez3var) {
  ...
  245100: jump zmergez3var is zMRET goto 1358
        ↓ (如果是 MRET)
  245101: zz4539 = zneq_anythingzIEPrivilegez5zK(zcur_privilege, zMachine)
  245102: jump zz4539 goto 1356  [如果 cur_privilege != Machine]
          ↓ (如果相等，继续)
  245104: zz4541 = zext_check_xret_priv(zMachine)
  245107: zz4540 = znot(zz4541)
  245108: jump zz4540 goto 1354  [如果 not(ext_check_xret_priv(Machine))]
          ↓ (如果检查通过，继续)
  245109-245112: exception_handler 调用
  245113-245114: set_next_pc 调用
  245115: zz40 = zRETIRE_SUCCESS
  245116: goto 1355  [正常返回]
          ↓
  245117: zz40 = zExt_XRET_Priv_Failure()  [标签 1354]
  245118: goto 1357
          ↓
  245119: zz40 = zIllegal_Instruction()  [标签 1356]
  245120: goto 45270
  ...
}

```

## 测试点（重点先测举例的mret）
1. 解析sail文件，变成AST，为符号执行做准备，以一种文件内部的形式进行测试：a.需要测试指令（add、mret、sw、lw、sb、lb、ecall）存不存在、能不能被识别 b.被测指令需要的操作数
2. 符号执行，以一个树的样式打印一个指令在什么样的条件下会对isa有一些什么操作，并给出要执行当前路径isa状态、指令操作数需要满足的条件
以mret为例（样式可以变得更美观）：
```
    mret
     |
   /-----\
  con1       mstatus.MPP=PRV_S
 /    \         /
...  ...      ...
p0   p1        p2

isa状态、指令操作数需要满足的条件：
p0:
  ...

p1:
  ...

p2:
  (mret没有操作数所以不用操作数的条件)
  priv=PRV_M
  mstatus.MPP=PRV_S
  ...（不用全列出来）

...
    
```

3. 用z3求解出isa状态具体的值，打印出来（复用上一步的部分代码）
以mret为例（样式可以变得更美观）：
```
    mret
     |
   /-----\
  con1       mstatus.MPP=PRV_S
 /    \         /
...  ...      ...
p0   p1        p2

isa状态、指令操作数需要满足的条件：
p0:
  ...

p1:
  ...

p2:
  (mret没有操作数所以不用操作数的值)
  priv=PRV_M
  x0=0x0000 0000
  x1=0x0000 ....
  ...(所有的GPR、FPR)
  x31=0x0000 ....
  mstatus=0xxxxx
  misa=0x.....
  mtvec=0x...
  ...(所有的CSR)

...

```
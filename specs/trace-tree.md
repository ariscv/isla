# ExecutionTree 机制技术报告

## 1. 背景与问题

Isla 原始的 Trace 采用的是线性链表式结构。每个 Solver 持有一个 Trace，而 Trace 本质上是一串 Event，随着执行推进不断向末尾追加。

当执行遇到符号分支并发生 fork 时，旧实现通常需要先做 checkpoint，再复制 Trace，随后让两个分支各自继续追加事件。这个模型在单路径推进时很直接，但一旦分叉，问题就会迅速暴露出来。

主要痛点有三点。

1. fork 时 replay 开销大。分支恢复时往往要重放从 checkpoint 以来的事件，路径越长，代价越高。
2. Trace 只能表达单条路径，无法自然表达整个执行过程的全局结构，更难直接呈现“谁从谁 fork 出来”这种关系。
3. 线性 Trace 不适合做 CFG 输出。它记录的是路径片段，不是分支树，后处理时必须额外拼接语义关系。

为了解决这些问题，Isla 将 Trace 机制重构为基于 petgraph 的执行树。新的目标不是让 Trace 再保存一条完整事件链，而是把它变成“树上的路径视图”：

```
旧模型
Solver -> Trace -> Event -> Event -> Event

新模型
Solver -> Trace(路径视图) -> ExecutionTree
                          ├── 拓扑结构
                          └── 节点事件数据
```

这个改造把“事件记录”和“执行拓扑”拆开了。事件继续按节点累积，fork 则体现在树边上。这样既保留了路径语义，也把全局结构显式化了。

**源码位置**：
- `isla-lib/src/execution_tree.rs`
- `isla-lib/src/smt.rs:515-588`
- `isla-lib/src/smt.rs:188-215`

---

## 2. 整体架构

ExecutionTree 的核心思路，是把“图拓扑”和“节点数据”分层管理。

```
ExecutionTree<B>
├── graph: RwLock<DiGraph<(), TreeEdge>>
│   └── 只保存拓扑关系，节点本身无权重，边携带 fork 信息
└── nodes: RwLock<HashMap<NodeIndex, Arc<NodeData<B>>>>
    └── 每个 NodeIndex 对应一份独立节点数据
```

这样的分层并不是纯粹的结构美化，而是直接服务于并发性能。

- 图拓扑变化只发生在 fork 和建节点时，频率远低于事件追加。
- 节点事件追加是热路径，必须尽量减少锁竞争。
- Trace 读取当前节点时，最好能直接缓存节点数据，避免每次都去 HashMap 查找。

### 2.1 节点与边的数据结构

NodeData 保存的是某个树节点上的本地事件和标记信息。

```rust
pub struct NodeData<B> {
    events: Mutex<Vec<Event<B>>>,
    source_loc: Option<SourceLoc>,
    tag: Mutex<Option<String>>,
}
```

TreeEdge 保存的是 fork 关系本身。

```rust
pub struct TreeEdge {
    fork_id: u32,
    condition: Option<Sym>,
    condition_expr: Option<String>,
    taken: bool,
    source_loc: SourceLoc,
}
```

这里有两个值得注意的设计点。

第一，`events` 和 `tag` 都放进各自独立的 `Mutex`，因为它们的写入节奏不同，且都是节点局部状态。

第二，边上保存的是 fork 相关信息，而不是事件列表。这样树的结构就能直接回答“哪个分支是哪个条件、在哪个源码位置、是 taken 还是 untaken”。

**源码位置**：
- `isla-lib/src/execution_tree.rs:40-74`

---

## 3. 分层设计的理由

ExecutionTree 的分层设计，本质上是在“读写锁粒度”和“查询成本”之间做平衡。

### 3.1 图拓扑与节点数据分离

如果把节点数据和图拓扑放在同一把锁里，任何一次 `push_event()` 都可能和 fork、遍历、CFG 导出互相阻塞。执行引擎里最频繁的操作恰恰是事件追加，这会让整体吞吐量很难看。

分层以后，热路径只需要锁当前节点的事件队列：

```
push_event()
  -> 仅锁 current_data.events
  -> 不碰整张图
```

fork 时才需要写图锁：

```
fork()
  -> 写锁 graph
  -> 新建两个节点
  -> 追加两条边
  -> 写锁 nodes 插入新 NodeData
```

这意味着，普通事件追加和树结构修改可以并行推进，互相干扰明显更小。

### 3.2 Trace 缓存 NodeData

Trace 内部不再“拥有”事件数据，而是缓存当前节点的 `Arc<NodeData<B>>`。

这样做的好处很直接：`push_event()` 不需要先通过 `NodeIndex` 去 HashMap 查找节点，再拿锁，再追加。Trace 已经握住了当前节点的直接引用。

```
Trace
├── current_node: NodeIndex
└── current_data: Arc<NodeData<B>>
```

这一步把频繁查找从热路径里拿掉了。

**源码位置**：
- `isla-lib/src/execution_tree.rs:83-135`
- `isla-lib/src/smt.rs:521-588`

---

## 4. Trace 作为路径视图

新的 Trace 不再保存一条完整的事件链，它只表示“当前走到了树上的哪个节点”。事件数据留在节点上，Trace 负责把这些节点串成路径视图。

```rust
pub struct Trace<B> {
    tree: Arc<ExecutionTree<B>>,
    current_node: NodeIndex,
    current_data: Arc<NodeData<B>>,
}
```

### 4.1 push_event

`push_event()` 的行为变得非常直接，它只往当前节点的事件列表里追加：

```rust
pub fn push_event(&self, event: Event<B>) {
    self.current_data.events.lock().unwrap().push(event)
}
```

这就是路径视图的关键含义。事件属于节点，不属于 Trace 本身。Trace 只是当前节点的访问入口。

### 4.2 to_vec

`to_vec()` 需要从当前节点向上遍历祖先链，收集每一层节点的事件，然后按根到叶的顺序重新拼回去。

这是这种设计的代价，也是它的语义所在。

```
current node
   ↑
 parent
   ↑
 grandparent
   ↑
 root
```

因为 Trace 只是“路径视图”，所以它天然不持有一份扁平化副本。调用 `to_vec()` 时做一次路径展开，就能恢复出当前路径的完整事件序列。

### 4.3 fork_checkpoint

fork 时，当前 Trace 会在树上创建两个子节点，其中 true 分支继续留在当前 Trace 上，false 分支被打包成 checkpoint 返回出去。

这和旧实现最大的不同在于，checkpoint 不再需要复制事件链，只需要记住“树上的哪个节点”。

**源码位置**：
- `isla-lib/src/smt.rs:548-588`

---

## 5. Checkpoint 机制

新的 Checkpoint 也是围绕“树节点引用”来设计的。

```rust
pub struct Checkpoint<B> {
    num: usize,
    tree: Arc<ExecutionTree<B>>,
    node: NodeIndex,
    next_var: u32,
}
```

可以看到，它不再携带事件副本，也不再携带独立 Trace。它保存的是：

1. 共享同一棵树的 `Arc`
2. 当前指向的节点索引
3. 求解器变量计数 `next_var`

这套结构支持多个分支共享同一棵执行树。fork 后，不同分支只是在树上指向不同节点，树本身由 `Arc` 统一管理。

```
          Arc<ExecutionTree>
                 │
     ┌───────────┼───────────┐
     │           │           │
  checkpoint A checkpoint B checkpoint C
     │           │           │
   node X      node Y      node Z
```

这种设计的一个直接收益，是 checkpoint 的复制成本很低。它只是一个轻量指针集合，不再背负事件历史。

**源码位置**：
- `isla-lib/src/smt.rs:189-215`

---

## 6. 增量 Checkpoint Replay

旧的 checkpoint 恢复方式更接近全路径 replay。新方案在同一棵树内部引入了增量恢复：`enter_checkpoint_incremental`。

### 6.1 核心思路

当当前 solver 和目标 checkpoint 都来自同一棵 ExecutionTree 时，不必从头重放整条路径，只要找出两者的最近公共祖先 LCA，然后只重放 LCA 到目标节点之间的增量事件即可。

流程如下：

```
当前 solver 在节点 A，需要切换到节点 B
1. 计算 LCA(A, B)
2. pop Z3 scope 回到 LCA 的深度
3. 沿 LCA -> B 的路径逐节点 push scope + replay events
4. 更新 trace 指向 B
```

### 6.2 退化路径

如果 checkpoint 来自不同的树，`Arc` 指针不相等，就无法共享同一条祖先链。这时增量优化失效，系统退化为 `from_checkpoint`，重新构建 solver 并 replay 全路径事件。

这是必要的保守策略，因为不同树意味着求解上下文根本不是同一份历史。

### 6.3 为什么可行

增量 replay 能成立，靠的是 ExecutionTree 的路径语义非常明确。每个节点只对应一段局部事件，路径上的祖先顺序就是约束加入的顺序。LCA 之前的约束已经在当前 solver 里，真正需要补的只是分叉后新增的那一小段。

**源码位置**：
- `isla-lib/src/smt.rs:2440-2461`

---

## 7. Executor 的 fork 适配

Executor 在 fork 时已经切换到了树模型。相关逻辑位于 `executor.rs:1249-1284`。

### 7.1 fork 流程

fork 的关键步骤可以概括为下面几步：

1. `solver.fork_trace_checkpoint()` 在树上创建 true 和 false 两个子节点
2. 当前 solver 切到 true 子节点，继续沿当前执行流推进
3. false 分支打包成 Task，checkpoint 指向 false 子节点，进入队列等待调度

```
parent node
   ├── true  -> 当前 worker 继续执行
   └── false -> 生成 Task 入队
```

这与旧模型的最大差别，是分支信息现在直接体现在树结构里，而不是靠外部拼接。

### 7.2 终止路径标记

Run::Dead 和 Concretize 路径也被映射到了节点标签上。

- `solver.tag_current_node("dead")` 用于标记死节点
- `solver.tag_current_node("concretize")` 用于标记具体化节点

这些标签并不改变树的拓扑，但会影响后续 CFG 输出的节点样式。

**源码位置**：
- `isla-lib/src/executor.rs:1249-1284`
- `isla-lib/src/smt.rs:2494-2496`

---

## 8. CFG 输出

ExecutionTree 的一个重要价值，是它可以直接作为 CFG 输出的数据源。执行完成后，系统从 Solver 提取整棵树，再做后处理生成 DOT 或 JSON。

### 8.1 DOT 输出

DOT 图里，节点和边的含义都更清楚了。

```
node: 事件摘要
edge: fork_id + 条件表达式 + taken / untaken
```

节点样式根据 tag 区分：

- `dead` 节点灰色
- `concretize` 节点虚线橙色
- 其他节点默认白色

边标签则会显示 fork 编号、条件和分支方向。如果启用 `--expand-fork-condition`，条件中的 `Sym` 会被展开成更可读的表达式。

### 8.2 JSON 输出

JSON 输出分成两个数组：

- `nodes`，包含 `id`、`events`、`type`
- `edges`，包含 `from`、`to`、`fork_id`、`condition`、`condition_expr`、`taken`

这种结构更适合后续程序消费，也更容易做可视化或二次分析。

### 8.3 条件展开机制

条件展开不是简单的字符串替换，而是沿节点路径收集所有 `DefineConst` 定义，构建 substitution map，再递归展开 `Exp::Var(sym)`。

这一步的结果是，边上的条件不再只是一个符号名，而能变成更贴近语义的表达式。

```rust
fn collect_definitions<B: BV>(events: &[Event<B>]) -> HashMap<Sym, Exp<Sym>>
```

这里的格式化并不是 SMT-LIB 原样输出，而是一个面向阅读的自定义格式。

**源码位置**：
- `isla-lib/src/cfg_output.rs`
- `isla-lib/src/cfg_output.rs:103-270`

---

## 9. 线程安全设计

ExecutionTree 需要支持多线程执行。当前模型的并发策略是“共享树，分离写入热点”。

### 9.1 图拓扑

图拓扑由 `RwLock<DiGraph<...>>` 保护。fork 时需要写锁，但这个临界区很短，只覆盖节点和边的创建。

### 9.2 节点数据

每个节点的数据都由独立 `Mutex` 保护。这样 `push_event()` 只会锁住当前节点，不会阻塞整棵树。

### 9.3 Trace 缓存

Trace 持有 `Arc<NodeData>`，避免频繁查找 HashMap。对热路径来说，这个缓存非常关键。

### 9.4 多 worker 共享树

每个 worker 都有自己的 Solver，但可以共享同一棵 ExecutionTree。

```
worker 1 -> Solver 1 -> Trace 1 -> Arc<ExecutionTree>
worker 2 -> Solver 2 -> Trace 2 -> Arc<ExecutionTree>
worker 3 -> Solver 3 -> Trace 3 -> Arc<ExecutionTree>
```

并发 fork 时，不同 worker 可能在同一棵树上继续扩展。写锁保证拓扑一致性，节点锁保证局部事件安全写入。

**源码位置**：
- `isla-lib/src/execution_tree.rs:30-35, 71-74, 83-135`

---

## 10. 设计取舍

### 10.1 为什么用 petgraph DiGraph

这里没有重新发明一套自定义树结构，而是直接用项目里已经存在的 petgraph 依赖。

好处有两个。

1. 现成的遍历和邻接查询 API，少写很多基础代码。
2. 结构表达清晰，后续做路径、祖先、边遍历都方便。

代价也有。petgraph 的通用性比专门的树结构更强，但也意味着有些操作不是为本场景量身定制的。不过对于当前需求，这个代价可以接受。

### 10.2 为什么要分离拓扑和节点数据

因为 push_event 是热路径。

如果每次写事件都要锁图、查图、改图，执行器的并发性会很差。把图拓扑和节点数据拆开后，绝大多数时候只需要锁当前节点的事件队列，竞争面明显更小。

### 10.3 为什么 Trace 要缓存 Arc<NodeData>

因为这是一次明确的性能优化。Trace 每次追加事件都应该尽量短，不应该再多做一次 HashMap 查找。缓存 NodeData 后，写路径变成“拿锁，push，结束”，非常直接。

### 10.4 为什么 to_vec 要沿祖先链展开

因为新的 Trace 本来就是路径视图，不是扁平副本。

这个选择的代价是，收集完整路径时要做一次祖先遍历。但 `to_vec()` 和 CFG 导出都不是最热的路径，换来的是写入路径更轻、更符合树语义。

### 10.5 为什么 LCA 计算可以接受

LCA 计算是 O(h)。在这里，h 表示树高。

虽然它不是常数时间，但实际中树高通常远小于整条路径长度。和全路径 replay 相比，这个成本很小，值得换取增量恢复能力。

### 10.6 为什么 from_checkpoint 仍然需要全路径 replay

因为 Z3 solver 不能共享。不同 checkpoint 之间，即使事件看起来相似，也不能直接复用同一个求解上下文。跨树恢复时，只能重建约束状态。

不过在同树场景下，`enter_checkpoint_incremental` 已经把大部分常见情况优化掉了，所以保留全路径 replay 只是一个必要退路，不是默认路径。

---

## 11. 小结

ExecutionTree 把 Isla 的 Trace 从线性事件链，升级成了显式的执行树路径视图。这个重构带来的变化不只是数据结构替换，更重要的是语义提升。

- fork 关系被显式记录在树边上
- 事件按节点局部保存，写入更轻
- checkpoint 变成树节点引用，复制成本更低
- 同树 checkpoint 可以做增量 replay，减少恢复开销
- CFG 输出直接建立在执行树之上，更容易表达全局结构

从实现角度看，这个设计把“路径执行”和“全局结构”解耦了。Trace 继续服务执行，ExecutionTree 负责表达拓扑，二者各司其职。这样做的结果，是让 Isla 能更自然地处理分叉、恢复和后处理，也让后续的图分析能力有了坚实基础。

**源码位置汇总**：
- `isla-lib/src/execution_tree.rs`
- `isla-lib/src/smt.rs:188-215`
- `isla-lib/src/smt.rs:515-588`
- `isla-lib/src/smt.rs:2440-2508`
- `isla-lib/src/executor.rs:1249-1284`
- `isla-lib/src/cfg_output.rs`

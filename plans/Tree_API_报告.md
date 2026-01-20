# Tree/TreeNode API 说明和示例报告

## 一、API 使用验证结果

✅ **所有对 Tree 和 TreeNode 的访问和修改都通过 API 实现**

验证方法：
- 搜索所有直接字段访问模式（如 `.node_type`、`.children`、`.parent` 不带括号的调用）
- 确认所有节点创建都使用 `TreeNode::new_root()` 或 `TreeNode::new_with_parent()`
- 确认所有树操作都使用 `Tree` 的公共方法

---

## 二、TreeNode API

### 2.1 结构说明

```rust
/// 执行树节点
///
/// 表示指令符号执行过程中的一个状态点。节点通过 Arc 共享所有权，
/// 子节点持有父节点的 Weak 引用以避免循环引用。节点身份由其内存地址决定，
/// 不使用数值 ID。
///
/// 内部使用 Mutex 包装的可变状态，以支持运行时动态构建树。
pub struct TreeNode<B> {
    node_type: Mutex<NodeType<B>>,
    parent: Weak<TreeNode<B>>,
    children: Mutex<Vec<Arc<TreeNode<B>>>>,
}
```

### 2.2 构造方法

| 方法 | 签名 | 说明 | 示例 |
|------|------|------|------|
| `new_root` | `pub fn new_root(node_type: NodeType<B>) -> Arc<Self>` | 创建根节点 | `let root = TreeNode::new_root(NodeType::Root { instruction: "ADDI".into() });` |
| `new_with_parent` | `pub fn new_with_parent(node_type: NodeType<B>, parent: &Arc<TreeNode<B>>) -> Arc<Self>` | 创建子节点并自动添加到父节点 | `let child = TreeNode::new_with_parent(NodeType::Leaf { ... }, &parent);` |

**示例：**
```rust
// 创建根节点
let root = TreeNode::new_root(NodeType::Root {
    instruction: "ADDI".to_string(),
});

// 创建子节点（自动添加到父节点）
let leaf = TreeNode::new_with_parent(
    NodeType::Leaf {
        satisfiable: true,
        return_value: None,
        constructor_name: None,
        unfolded_value: None,
    },
    &root,
);
```

### 2.3 节点关系查询

| 方法 | 签名 | 说明 | 返回值 |
|------|------|------|--------|
| `parent` | `pub fn parent(&self) -> Option<Arc<TreeNode<B>>>` | 获取父节点 | 根节点返回 None |
| `child_count` | `pub fn child_count(&self) -> usize` | 获取子节点数量 | 叶子节点返回 0 |
| `is_leaf` | `pub fn is_leaf(&self) -> bool` | 是否为叶子节点 | - |
| `is_root` | `pub fn is_root(&self) -> bool` | 是否为根节点 | - |
| `children_cloned` | `pub fn children_cloned(&self) -> Vec<Arc<TreeNode<B>>>` | 获取子节点克隆列表 | - |

**示例：**
```rust
// 检查节点类型
if node.is_root() {
    println!("这是根节点");
}

if node.is_leaf() {
    println!("这是叶子节点，无子节点");
} else {
    println!("子节点数量: {}", node.child_count());
}

// 获取父节点
if let Some(parent) = node.parent() {
    println!("有父节点");
}

// 获取所有子节点
let children = node.children_cloned();
for child in children {
    println!("处理子节点...");
}
```

### 2.4 数据访问

| 方法 | 签名 | 说明 | 示例 |
|------|------|------|------|
| `with_node_type` | `pub fn with_node_type<F, R>(&self, f: F) -> R where F: FnOnce(&NodeType<B>) -> R` | 安全访问节点类型 | `node.with_node_type(|t| println!("{}", t.display_name()))` |
| `with_children` | `pub fn with_children<F, R>(&self, f: F) -> R where F: FnOnce(&[Arc<TreeNode<B>>]) -> R` | 安全访问子节点列表 | `node.with_children(|ch| println!("共 {} 个子节点", ch.len()))` |
| `node_type_cloned` | `pub fn node_type_cloned(&self) -> NodeType<B> where NodeType<B>: Clone` | 获取节点类型克隆 | `let node_type = node.node_type_cloned();` |

**示例：**
```rust
// 访问节点类型
node.with_node_type(|node_type| {
    match node_type {
        NodeType::Root { instruction } => {
            println!("指令: {}", instruction);
        }
        NodeType::Branch { fork_id, variable, .. } => {
            println!("分支 #{}: {}", fork_id, variable);
        }
        NodeType::Leaf { satisfiable, .. } => {
            println!("叶子: {}", if *satisfiable { "可满足" } else { "不可满足" });
        }
        _ => {}
    }
});

// 访问子节点
node.with_children(|children| {
    println!("子节点数量: {}", children.len());
});
```

### 2.5 节点操作

| 方法 | 签名 | 说明 | 使用场景 |
|------|------|------|----------|
| `add_child` | `pub fn add_child(self: &Arc<Self>, child: Arc<TreeNode<B>>)` | 添加子节点 | `Arc::clone(&parent).add_child(child);` |

**示例：**
```rust
// 手动添加子节点（通常使用 new_with_parent 会自动处理）
use std::sync::Arc;

let parent = Arc::new(TreeNode::new_root(...));
let child = Arc::new(TreeNode { /* ... */ });
Arc::clone(&parent).add_child(child);
```

---

## 三、Tree API

### 3.1 结构说明

```rust
/// 执行树
///
/// 封装根节点并提供了树级别的操作方法，包括遍历、查找、统计和添加节点。
pub struct Tree<B> {
    root: Arc<TreeNode<B>>,
}
```

### 3.2 构造与访问

| 方法 | 签名 | 说明 | 示例 |
|------|------|------|------|
| `new` | `pub fn new(root: Arc<TreeNode<B>>) -> Self` | 创建新树 | `let tree = Tree::new(root_node);` |
| `root` | `pub fn root(&self) -> &Arc<TreeNode<B>>` | 获取根节点引用 | `let root = tree.root();` |

**示例：**
```rust
// 创建树
let root = TreeNode::new_root(NodeType::Root {
    instruction: "ADDI".to_string(),
});
let tree = Tree::new(root);

// 访问根节点
let root_ref = tree.root();
```

### 3.3 遍历方法

| 方法 | 签名 | 说明 | 示例 |
|------|------|------|------|
| `dfs` | `pub fn dfs<F>(&self, visitor: F) where F: FnMut(&Arc<TreeNode<B>>) -> bool` | 深度优先遍历 | `tree.dfs(|node| { println!("{:?}", node); true });` |
| `bfs` | `pub fn bfs<F>(&self, visitor: F) where F: FnMut(&Arc<TreeNode<B>>) -> bool` | 广度优先遍历 | `tree.bfs(|node| { ... });` |

**访问者函数说明：**
- 参数：`&Arc<TreeNode<B>>` - 当前节点引用
- 返回值：`bool` - `true` 继续遍历，`false` 停止遍历

**示例：**
```rust
// 深度优先遍历打印所有节点
tree.dfs(|node| {
    node.with_node_type(|nt| {
        println!("{}", nt.display_name());
    });
    true // 继续遍历
});

// 广度优先遍历查找第一个叶子节点
tree.bfs(|node| {
    if node.is_leaf() {
        println!("找到第一个叶子节点");
        false // 停止遍历
    } else {
        true // 继续遍历
    }
});
```

### 3.4 查找方法

| 方法 | 签名 | 说明 | 示例 |
|------|------|------|------|
| `find` | `pub fn find<F>(&self, predicate: F) -> Option<Arc<TreeNode<B>>> where F: Fn(&TreeNode<B>) -> bool` | 根据条件查找节点 | `tree.find(|n| n.is_leaf())` |

**示例：**
```rust
// 查找第一个叶子节点
if let Some(leaf) = tree.find(|n| n.is_leaf()) {
    println!("找到叶子节点");
}

// 查找特定分支
if let Some(branch) = tree.find(|n| {
    n.with_node_type(|nt| matches!(nt, NodeType::Branch { fork_id: 1, .. }))
}) {
    println!("找到分支 #1");
}
```

### 3.5 统计方法

| 方法 | 签名 | 说明 | 返回值 |
|------|------|------|--------|
| `node_count` | `pub fn node_count(&self) -> usize` | 总节点数 | - |
| `leaf_count` | `pub fn leaf_count(&self) -> usize` | 叶子节点数 | - |
| `max_depth` | `pub fn max_depth(&self) -> usize` | 最大深度 | - |

**示例：**
```rust
println!("总节点数: {}", tree.node_count());
println!("叶子节点数: {}", tree.leaf_count());
println!("最大深度: {}", tree.max_depth());
```

### 3.6 叶子节点

| 方法 | 签名 | 说明 | 示例 |
|------|------|------|------|
| `leaves` | `pub fn leaves(&self) -> Vec<Arc<TreeNode<B>>>` | 获取所有叶子节点 | `for leaf in tree.leaves() { ... }` |

**示例：**
```rust
// 遍历所有叶子节点
for leaf in tree.leaves() {
    leaf.with_node_type(|nt| {
        if let NodeType::Leaf { satisfiable, .. } = nt {
            println!("叶子节点: {}", if *satisfiable { "可满足" } else { "不可满足" });
        }
    });
}
```

### 3.7 格式化输出

| 方法 | 签名 | 说明 | 示例 |
|------|------|------|------|
| `format_ascii` | `pub fn format_ascii(&self, num_paths: usize) -> String` | ASCII 艺术格式 | `println!("{}", tree.format_ascii(3));` |
| `format_graphviz` | `pub fn format_graphviz(&self) -> String` | Graphviz DOT 格式 | `println!("{}", tree.format_graphviz());` |

**示例：**
```rust
// 输出 ASCII 格式的树
println!("{}", tree.format_ascii(result.num_paths));

// 输出 Graphviz DOT 格式（可用于生成图形）
println!("{}", tree.format_graphviz());
// 保存到文件并使用 graphviz 渲染:
// dot -Tpng output.dot -o tree.png
```

**ASCII 输出示例：**
```
指令执行树 (3 条路径):

📋 指令: ADDI
├── 🔀 分岔 #1: x @ rv32d.ir:1234
│   ├── 🍁 ✓ 可满足 (返回: Done)
│   └── 🍁 ✗ 不可满足
└── 🍁 ✓ 可满足 (返回: Done)
```

---

## 四、NodeType API

### 4.1 枚举定义

```rust
/// 树节点类型
#[derive(Clone, Debug)]
pub enum NodeType<B> {
    /// 根节点 - 执行树的入口
    Root { instruction: String },
    /// 路径节点 - 携带约束条件并追踪数据
    Path {
        constraints: Vec<PathConstraint>,
        variables: Vec<String>,
        location: String,
    },
    /// 分支节点 - 表示执行中的分岔点
    Branch {
        fork_id: u32,
        variable: String,
        location: String,
    },
    /// 叶子节点 - 执行完成
    Leaf {
        satisfiable: bool,
        return_value: Option<Val<B>>,
        constructor_name: Option<String>,
        unfolded_value: Option<String>,
    },
}
```

### 4.2 辅助方法

| 方法 | 说明 | 返回值 |
|------|------|--------|
| `display_name()` | 获取节点显示名称 | `&str` ("根节点", "路径节点", "分支节点", "叶子节点") |
| `is_root()` | 是否为根节点 | `bool` |
| `is_path()` | 是否为路径节点 | `bool` |
| `is_branch()` | 是否为分支节点 | `bool` |
| `is_leaf()` | 是否为叶子节点 | `bool` |
| `as_root()` | 获取根节点信息 | `Option<&str>` |
| `as_path()` | 获取路径节点信息 | `Option<(&[PathConstraint], &[String], &str)>` |
| `as_branch()` | 获取分支节点信息 | `Option<(u32, &str, &str)>` |
| `as_leaf()` | 获取叶子节点信息 | `Option<LeafNodeInfo<B>>` |

**示例：**
```rust
node.with_node_type(|nt| {
    // 类型判断
    if nt.is_root() {
        println!("这是根节点");
    }

    // 获取显示名称
    println!("节点类型: {}", nt.display_name());

    // 获取具体信息
    if let Some(instruction) = nt.as_root() {
        println!("指令: {}", instruction);
    }

    if let Some((fork_id, variable, location)) = nt.as_branch() {
        println!("分支 #{}: {} @ {}", fork_id, variable, location);
    }

    if let Some(info) = nt.as_leaf() {
        println!("可满足: {}", info.satisfiable);
    }
});
```

---

## 五、PathConstraint API

### 5.1 结构定义

```rust
/// 路径约束条件
#[derive(Clone, Debug)]
pub struct PathConstraint {
    pub variable: String,
    pub constraint: String,
    pub branch_num: u32,
}
```

### 5.2 构造方法

| 方法 | 签名 | 说明 | 示例 |
|------|------|------|------|
| `new` | `pub fn new(variable: String, constraint: String, branch_num: u32) -> Self` | 创建新约束 | `PathConstraint::new("x".into(), "x > 0".into(), 1)` |
| `true_constraint` | `pub fn true_constraint(variable: String) -> Self` | 创建真值约束 | `PathConstraint::true_constraint("x".into())` |
| `false_constraint` | `pub fn false_constraint(variable: String) -> Self` | 创建假值约束 | `PathConstraint::false_constraint("x".into())` |

**示例：**
```rust
// 创建各种约束
let c1 = PathConstraint::new("x".into(), "x > 0".into(), 0);
let c2 = PathConstraint::true_constraint("y".into());
let c3 = PathConstraint::false_constraint("z".into());
```

### 5.3 查询方法

| 方法 | 说明 | 返回值 |
|------|------|--------|
| `is_true_branch()` | 是否为真分支 | `bool` |
| `is_false_branch()` | 是否为假分支 | `bool` |
| `branch_direction()` | 获取分支方向描述 | `&str` ("真" 或 "假") |
| `format()` | 格式化约束 | `String` |

**示例：**
```rust
let constraint = PathConstraint::true_constraint("x".into());

println!("是真分支: {}", constraint.is_true_branch());  // true
println!("是假分支: {}", constraint.is_false_branch());  // false
println!("方向: {}", constraint.branch_direction());     // "真"
println!("格式化: {}", constraint.format());             // "x = true"
```

---

## 六、执行结果 API

### 6.1 结构定义

```rust
/// 符号执行结果（包含执行树）
pub struct ExecutionResult<B> {
    pub tree: Tree<B>,           // 执行树
    pub num_paths: usize,        // 探索的执行路径数量
    pub leaves: Vec<LeafInfo<B>>, // 所有叶子节点信息
}

/// 叶子节点信息
pub struct LeafInfo<B> {
    pub path: Vec<Arc<TreeNode<B>>>,    // 通往此叶子节点的路径
    pub satisfiable: bool,               // 是否可满足
    pub return_value: Option<Val<B>>,   // 返回值
}
```

### 6.2 公共函数

| 函数 | 说明 | 示例 |
|------|------|------|
| `format_tree_ascii(result)` | ASCII 格式化执行结果 | `println!("{}", format_tree_ascii(&result));` |
| `format_tree_graphviz(result)` | Graphviz 格式化执行结果 | `println!("{}", format_tree_graphviz(&result));` |
| `execute_instruction_tree(shared_state, "ADDI")` | 执行指令并生成执行树 | `let result = execute_instruction_tree(...)?;` |

**示例：**
```rust
// 执行指令
let result = execute_instruction_tree::<u32>(
    "ADDI",
    &shared_state,
    &regs,
    &lets,
)?;

// 输出结果
println!("{}", format_tree_ascii(&result));

// 保存为 Graphviz
let dot = format_tree_graphviz(&result);
std::fs::write("output.dot", dot)?;

// 访问结果数据
println!("路径数: {}", result.num_paths);
println!("树深度: {}", result.tree.max_depth());

// 遍历叶子信息
for leaf_info in &result.leaves {
    println!("可满足: {}", leaf_info.satisfiable);
}
```

---

## 七、完整使用示例

### 7.1 创建和遍历树

```rust
use isla_lib::isarch::{TreeNode, Tree, NodeType};

// 创建根节点
let root = TreeNode::new_root(NodeType::Root {
    instruction: "ADDI".to_string(),
});

// 创建子节点
let branch1 = TreeNode::new_with_parent(
    NodeType::Branch {
        fork_id: 1,
        variable: "x".to_string(),
        location: "file.ir:100".to_string(),
    },
    &root,
);

let leaf1 = TreeNode::new_with_parent(
    NodeType::Leaf {
        satisfiable: true,
        return_value: None,
        constructor_name: Some("Done".to_string()),
        unfolded_value: Some("完成".to_string()),
    },
    &branch1,
);

// 创建树
let tree = Tree::new(root);

// 统计信息
println!("节点数: {}", tree.node_count());
println!("叶子数: {}", tree.leaf_count());
println!("深度: {}", tree.max_depth());

// 遍历所有节点
tree.dfs(|node| {
    node.with_node_type(|nt| {
        println!("{}", nt.display_name());
    });
    true
});
```

### 7.2 使用执行指令API

```rust
use isla_lib::isarch::{execute_instruction_tree, format_tree_ascii};

// 执行指令
let result = execute_instruction_tree::<u32>(
    "MRET",
    &shared_state,
    &regs,
    &lets,
)?;

// 输出ASCII树
println!("{}", format_tree_ascii(&result));

// 分析结果
for leaf_info in &result.leaves {
    if leaf_info.satisfiable {
        println!("可满足路径，返回值: {:?}", leaf_info.return_value);
    }
}
```

---

## 八、API 设计原则

1. **纯弱引用设计**：不使用 node_id，节点身份由内存地址决定
2. **Arc/Weak 内存管理**：Arc 共享所有权，Weak 避免循环引用
3. **Mutex 内部可变性**：支持运行时动态构建树
4. **语义化命名**：所有方法都有清晰的中文注释和语义化命名
5. **安全访问**：使用 `with_*` 方法模式，避免直接暴露内部状态

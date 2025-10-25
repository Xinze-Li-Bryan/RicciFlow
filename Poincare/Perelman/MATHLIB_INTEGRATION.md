# Mathlib 集成策略

本文档说明我们如何正确地使用 Mathlib 的类型类系统，以及如何逐步将 axioms 替换为真正的定理。

## 核心理念

**自顶向下 + 逐步对接**：
1. 先用 axiom/sorry 完成整体架构
2. 尽可能使用 Mathlib 的标准定义（type class）
3. 通过 Mathlib 的类型类推导减少手工工作
4. 逐步将 axiom 替换为基于 Mathlib 的证明

---

## 成功案例：Ball3 的单连通性

### 问题
我们需要证明 3-球（`Ball3`）是单连通的。

### 传统做法（不好）
```lean
axiom ball3_simply_connected : SimplyConnected Ball3
```

**问题**：
- 孤立的 axiom，无法利用 Mathlib 的已有结果
- 无法自动推导其他性质

### Mathlib 集成做法（好！）✅

```lean
-- 步骤 1: 使用 Mathlib 的标准类型类
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

-- 步骤 2: 声明实例（instance）而不是普通 axiom
instance : ContractibleSpace Ball3 := sorry
  -- TODO: 对接凸集理论

-- 步骤 3: 自动推导！
example : SimplyConnectedSpace Ball3 := inferInstance
  -- ✓ Mathlib 自动通过 SimplyConnectedSpace.ofContractible 推导
```

**优势**：
1. ✅ **自动推导**：`ContractibleSpace → SimplyConnectedSpace`（Mathlib 提供）
2. ✅ **类型类实例**：可以被其他定理自动使用
3. ✅ **清晰的依赖**：只需要证明可缩性，单连通性免费得到
4. ✅ **对接路径明确**：找到凸集的可缩性定理即可

---

## Type Class 系统的威力

### 定理推导链

在 Mathlib 中，有很多自动推导：

```
ContractibleSpace X
    ↓ (SimplyConnectedSpace.ofContractible)
SimplyConnectedSpace X
    ↓ (implies PathConnectedSpace)
PathConnectedSpace X
    ↓ (implies ConnectedSpace)
ConnectedSpace X
```

### 我们的策略

**只在最基础的层次添加 axiom/sorry**：
```lean
-- ✓ 好：在基础层次
instance : ContractibleSpace Ball3 := sorry

-- ✗ 差：在衍生层次
axiom ball3_simply_connected : SimplyConnectedSpace Ball3
axiom ball3_path_connected : PathConnectedSpace Ball3
axiom ball3_connected : ConnectedSpace Ball3
```

后三个都应该从第一个**自动推导**！

---

## 实际应用

### 1. 球面的单连通性

**当前代码**：
```lean
axiom sphere_simply_connected_instance (n : ℕ) (h : n ≥ 2) :
  SimplyConnectedSpace (Sphere n)
```

**TODO**: 对接到基本群计算
- 在 Mathlib 中找到或证明 `π₁(Sⁿ) = 1` for n ≥ 2
- 使用 `SimplyConnectedSpace` 的定义直接构造

### 2. van Kampen 定理

**当前代码**（极度简化）：
```lean
axiom van_kampen_theorem : ∀ {M : Type*} [TopologicalSpace M], True
```

**TODO**: 完整陈述并对接
```lean
-- 目标：完整的 van Kampen 陈述
theorem van_kampen
    {M : Type*} [TopologicalSpace M]
    (U V : Set M)
    (hU : IsOpen U) (hV : IsOpen V)
    (h_cover : U ∪ V = Set.univ)
    (h_intersection : PathConnectedSpace (U ∩ V))
    (x₀ : M) (hx : x₀ ∈ U ∩ V) :
    -- π₁(M, x₀) ≅ π₁(U, x₀) *_{π₁(U∩V, x₀)} π₁(V, x₀)
    FundamentalGroup x₀ ≃* ... := sorry
```

**对接路径**：
- Mathlib 有 categorical van Kampen (`Mathlib.CategoryTheory.Limits.VanKampen`)
- 需要将其特化到拓扑空间的情况

### 3. 手术保持单连通性

**当前代码**：
```lean
axiom surgery_preserves_simply_connected_abstract
    {M M' : Type*} [TopologicalSpace M] [TopologicalSpace M']
    (_h_M_sc : SimplyConnected M)
    (_h_surgery_relation : True)
    : SimplyConnected M'
```

**TODO**: 基于 van Kampen 证明
```lean
theorem surgery_preserves_simply_connected
    {M M' : Type*} [TopologicalSpace M] [TopologicalSpace M']
    (h_M_sc : SimplyConnectedSpace M)
    (h_surgery : M' ≃ₜ (M \ neck) ∪ D³ ∪ D³)  -- 需要精确定义
    : SimplyConnectedSpace M' := by
  -- 1. 应用 van Kampen 到 M' = (M \ neck) ∪ D³ ∪ D³
  -- 2. π₁(M \ neck) = π₁(M) = 1 （移除高余维不改变基本群）
  -- 3. π₁(D³) = 1 （可缩空间单连通）
  -- 4. 粘合沿 S² 进行，π₁(S²) = 1
  -- 5. 因此 π₁(M') = 1
  sorry
```

---

## 对接优先级

### 第一阶梯：Type Class Instances（立即可做）

这些是 Mathlib 的标准 type class，应该优先声明为 instance：

1. ✅ **ContractibleSpace Ball3** - 已完成（instance sorry）
2. ⬜ **CompactSpace Sphere3** - 应该容易（闭且有界）
3. ⬜ **CompactSpace Ball3** - 应该容易（闭且有界）
4. ⬜ **PathConnectedSpace (Sphere n)** - 标准拓扑结果

### 第二阶梯：基本拓扑定理（需要证明）

基于 Mathlib 的凸集、紧致性等理论：

1. ⬜ **ContractibleSpace Ball3 的证明**
   - 对接到凸集理论
   - 凸集 → 星形 → 可缩

2. ⬜ **球面的紧致性**
   - 有界闭集 → 紧致（Heine-Borel）

### 第三阶梯：代数拓扑定理（困难）

需要深入的 FundamentalGroupoid 理论：

1. ⬜ **π₁(Sⁿ) = 1** for n ≥ 2
2. ⬜ **van Kampen theorem**（topological version）
3. ⬜ **surgery_preserves_simply_connected**（基于 van Kampen）

### 第四阶梯：3-流形拓扑（可能保留为 axiom）

这些接近庞加莱猜想本身的难度：

1. 🔒 **gluing_balls_classification**（球粘贴分类）
2. 🔒 **PDE/几何分析结果**（Ricci flow 的深层定理）

---

## 检查清单

每次添加新的拓扑/几何性质时，问自己：

- [ ] 这个性质是 Mathlib 的标准 type class 吗？
  - 是 → 使用 instance
  - 否 → 考虑定义为普通定理

- [ ] 这个性质能从更基础的性质推导吗？
  - 能 → 不要 axiomatize，用 inferInstance
  - 不能 → 在最基础层次 axiomatize

- [ ] 是否有 Mathlib 的类似定理？
  - 有 → 添加 TODO 注释说明对接路径
  - 无 → 记录在 AXIOM_TODO.md

- [ ] 是否需要在 instance 之间建立桥接？
  - 需要 → 添加明确的转换函数/定理

---

## 示例：完整的类型类策略

### 定义层次
```lean
-- 最基础：可缩性
instance : ContractibleSpace Ball3 := sorry

-- 自动推导：单连通性
example : SimplyConnectedSpace Ball3 := inferInstance

-- 自动推导：道路连通性
example : PathConnectedSpace Ball3 := inferInstance

-- 自动推导：连通性
example : ConnectedSpace Ball3 := inferInstance
```

### 桥接到我们的定义
```lean
-- 我们的简化版单连通性
class SimplyConnected (M : Type*) [TopologicalSpace M] : Prop where
  pathConnected : PathConnectedSpace M
  pi1_trivial : True

-- 桥接引理
theorem simplyConnectedSpace_implies_simplyConnected
    (M : Type*) [TopologicalSpace M] [SimplyConnectedSpace M] :
    SimplyConnected M where
  pathConnected := inferInstance  -- 自动推导！
  pi1_trivial := trivial
```

---

## 当前进展总结

### ✅ 已完成
- 导入 Mathlib 的 `SimplyConnectedSpace`, `ContractibleSpace`
- Ball3 的可缩性作为 instance
- Ball3 的单连通性**自动推导**
- 建立了 SimplyConnectedSpace ↔ SimplyConnected 的桥接

### ⚠️ 进行中
- sphere_simply_connected_instance（已 axiomatize）
- 搜索 Mathlib 中的 van Kampen

### ❌ 待完成
- 证明 ContractibleSpace Ball3（对接凸集理论）
- 完整陈述 van Kampen 定理
- 基于 van Kampen 证明手术保持单连通性

---

## 最终目标

**理想状态**：
- ✅ 所有标准拓扑性质都用 Mathlib type class
- ✅ 最大化利用 Mathlib 的自动推导
- ✅ 只有深层 PDE/几何分析结果保留为 axiom
- ✅ 所有拓扑 axioms 都有清晰的对接路径

**当前距离理想状态**：
- ContractibleSpace Ball3: ⚠️ instance sorry（需对接凸集）
- SimplyConnectedSpace Ball3: ✅ 自动推导
- van Kampen: ❌ 需要完整陈述和证明
- 手术相关: ❌ 需要基于 van Kampen 证明

我们在正确的道路上！🎯

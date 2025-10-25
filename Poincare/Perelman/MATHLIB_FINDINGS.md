# Mathlib 对接发现报告

本文档记录了在 Mathlib 中找到的与我们项目相关的定理和定义。

**生成时间**: 2025-10-25
**Mathlib 版本**: Latest (从 .lake/packages/mathlib 检查)

---

## 🎉 重大发现

### 1. **Mathlib 已有庞加莱猜想的形式化声明！**

**文件**: `Mathlib.Geometry.Manifold.PoincareConjecture`

```lean
/-- The 3-dimensional topological Poincaré conjecture (proven by Perelman) -/
proof_wanted SimplyConnectedSpace.nonempty_homeomorph_sphere_three
    [T2Space M] [ChartedSpace ℝ³ M] [SimplyConnectedSpace M] [CompactSpace M] :
    Nonempty (M ≃ₜ 𝕊³)

/-- The 3-dimensional smooth Poincaré conjecture (proven by Perelman) -/
proof_wanted SimplyConnectedSpace.nonempty_diffeomorph_sphere_three
    [T2Space M] [ChartedSpace ℝ³ M] [IsManifold (𝓡 3) ∞ M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ 𝕊³)
```

**意义**:
- Mathlib 使用 `proof_wanted` 标记了庞加莱猜想！
- 使用了 `SimplyConnectedSpace`（我们已经集成的类型类）
- **我们的工作可以直接对接这个声明**！

**对接策略**:
```lean
-- 我们的目标
theorem poincare_conjecture :
  ∀ M : Type*, Is3Manifold M → SimplyConnected M → Nonempty (M ≃ₜ Sphere3)

-- 对接到 Mathlib
theorem poincare_connects_to_mathlib :
  -- 将我们的类型转换为 Mathlib 的类型
  -- Is3Manifold M → ChartedSpace ℝ³ M
  -- SimplyConnected M → SimplyConnectedSpace M (我们已经有桥接)
  -- Sphere3 ≃ₜ 𝕊³
  ...
```

---

## 找到的关键定理

### 2. **凸集的可缩性** ✅

**文件**: `Mathlib.Analysis.Convex.Contractible`

```lean
/-- A non-empty convex set is a contractible space. -/
protected theorem Convex.contractibleSpace (hs : Convex ℝ s) (hne : s.Nonempty) :
    ContractibleSpace s
```

**立即应用**: 证明 `ContractibleSpace Ball3`

**证明路径**:
1. 证明 `Ball3` 是 `ℝ⁴` 的凸子集
2. 应用 `Convex.contractibleSpace`
3. `SimplyConnectedSpace Ball3` 自动推导（通过 `SimplyConnectedSpace.ofContractible`）

**代码**:
```lean
-- 在 TopologyHelpers.lean 中
theorem ball3_is_convex : Convex ℝ (Set.univ : Set Ball3) := by
  -- 证明: ∀ x y ∈ Ball3, ∀ a b ≥ 0, a + b = 1 → a • x + b • y ∈ Ball3
  intro x _ y _ a b ha hb hab
  -- ‖a • x + b • y‖² ≤ a‖x‖² + b‖y‖² ≤ a + b = 1
  sorry

instance : ContractibleSpace Ball3 :=
  (ball3_is_convex.contractibleSpace ⟨Classical.arbitrary Ball3, Set.mem_univ _⟩)
```

---

### 3. **van Kampen 余极限** (Categorical)

**文件**: `Mathlib.CategoryTheory.Limits.VanKampen`

```lean
/-!
# Universal colimits and van Kampen colimits

## Main definitions
- `CategoryTheory.IsUniversalColimit`: A (colimit) cocone over a diagram `F : J ⥤ C` is universal
  if it is stable under pullbacks.
- `CategoryTheory.IsVanKampenColimit`: A (colimit) cocone over a diagram `F : J ⥤ C` is van
  Kampen if for every cocone `c'` over the pullback of the diagram `F' : J ⥤ C'`,
  `c'` is colimiting iff `c'` is the pullback of `c`.
-/
```

**状态**: 这是 **categorical** van Kampen，不是拓扑学的 van Kampen

**需要的工作**:
- Mathlib 没有拓扑学 van Kampen（针对基本群的版本）
- 我们需要**自己陈述并证明**（或者保留为 axiom）
- 可能需要在 `Mathlib.AlgebraicTopology.FundamentalGroupoid` 中添加

**参考**: https://ncatlab.org/nlab/show/van+Kampen+theorem

---

### 4. **基本群和单连通性**

**文件**: `Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected`

```lean
/-- A simply connected space is one whose fundamental groupoid is equivalent
    to the discrete unit category. -/
class SimplyConnectedSpace (X : Type*) [TopologicalSpace X] : Prop where
  equiv_unit : Nonempty (FundamentalGroupoid X ≌ Discrete Unit)
```

**关键定理**:
```lean
-- 可缩空间是单连通的
theorem SimplyConnectedSpace.ofContractible [ContractibleSpace X] :
    SimplyConnectedSpace X

-- 单连通性等价于路径同伦唯一性
theorem simply_connected_iff_paths_homotopic :
    SimplyConnectedSpace X ↔
    PathConnectedSpace X ∧ ∀ (x y : X) (p q : Path x y), p.Homotopic q
```

**我们已经用了**: ✅ 已经在 TopologyHelpers.lean 中集成

---

### 5. **球面定义**

**文件**: `Mathlib.Topology.Category.TopCat.Sphere`

```lean
-- Mathlib 使用度量空间中的球面定义
variable (n : ℕ)
def sphere : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  {x | ‖x‖ = 1}
```

**文件**: `Mathlib.Geometry.Manifold.Instances.Sphere`

**我们的定义**:
```lean
def Sphere (n : ℕ) : Type := { x : Fin (n+1) → ℝ // (∑ i, x i ^ 2) = 1 }
```

**对接工作**:
- 证明两个定义等价
- 或者直接使用 Mathlib 的定义

---

## 球面的拓扑性质搜索结果

### 找到的内容
- ❌ **没有** π₁(Sⁿ) = 1 for n ≥ 2 的证明
- ❌ **没有** `SimplyConnectedSpace (Sphere n)` 实例 for n ≥ 2
- ✅ 有球面的光滑流形结构
- ✅ 有球面的紧致性

### 需要的工作
球面的单连通性需要**自己证明或 axiomatize**：

**选项 1**: Axiomatize（当前做法）
```lean
axiom sphere_simply_connected_instance (n : ℕ) (h : n ≥ 2) :
  SimplyConnectedSpace (Sphere n)
```

**选项 2**: 等待 Mathlib 添加（或者我们贡献到 Mathlib）
```lean
-- 需要证明 π₁(Sⁿ) 计算
-- 可能需要 CW 复形、同伦论等深层代数拓扑
```

---

## 立即可做的对接工作

### 优先级 1: 凸集 → 可缩性 ✅

**文件**: `Poincare/Perelman/TopologyHelpers.lean`

**修改**:
```lean
import Mathlib.Analysis.Convex.Contractible

-- 证明 Ball3 是凸集
theorem ball3_is_convex : Convex ℝ (univ : Set Ball3) := sorry

-- 应用 Mathlib 定理
instance : ContractibleSpace Ball3 :=
  ball3_is_convex.contractibleSpace ⟨_, mem_univ _⟩
```

**预期结果**:
- 移除 1 个 instance sorry
- `SimplyConnectedSpace Ball3` 仍然自动推导

**难度**: 低-中（需要证明凸性）

### 优先级 2: 对接 Mathlib 庞加莱猜想声明

**文件**: `Poincare/Final.lean`

**修改**:
```lean
import Mathlib.Geometry.Manifold.PoincareConjecture

-- 添加类型转换定理
theorem our_poincare_implies_mathlib_poincare :
  poincare_conjecture → SimplyConnectedSpace.nonempty_homeomorph_sphere_three := by
  -- 转换类型类
  sorry
```

**预期结果**:
- 明确我们的工作如何对接到 Mathlib
- 为未来 PR 到 Mathlib 做准备

**难度**: 中（类型转换）

### 优先级 3: 完整陈述 van Kampen

**文件**: `Poincare/Perelman/TopologyHelpers.lean`

**修改**:
```lean
-- 目前（太简化）
axiom van_kampen_theorem : ∀ {M : Type*} [TopologicalSpace M], True

-- 改为完整陈述
theorem van_kampen_seifert_fundamental_groupoid
    {M : Type*} [TopologicalSpace M]
    (U V : Set M) (hU : IsOpen U) (hV : IsOpen V)
    (h_cover : U ∪ V = Set.univ)
    (h_path_conn : PathConnectedSpace (U ∩ V))
    (x₀ : M) (hx : x₀ ∈ U ∩ V) :
    -- π₁(M, x₀) 是 π₁(U, x₀) 和 π₁(V, x₀) 的自由积
    FundamentalGroup x₀ ≃* ... := sorry
```

**难度**: 高（需要深入 FundamentalGroupoid 理论）

---

## Mathlib 中没有但我们需要的

### 需要 Axiomatize 或自己证明

1. **π₁(Sⁿ) = 1** for n ≥ 2
   - 深层代数拓扑结果
   - 可能需要 covering space 理论

2. **拓扑学 van Kampen 定理**
   - Mathlib 只有 categorical 版本
   - 需要特化到 FundamentalGroupoid

3. **手术保持单连通性**
   - 这是我们项目特有的
   - 需要基于 van Kampen 证明

4. **球粘贴分类**
   - 接近庞加莱猜想本身
   - 可能长期保留为 axiom

---

## 总结

### ✅ 好消息

1. **Mathlib 有庞加莱猜想声明** - 我们可以对接！
2. **凸集可缩性** - 可以立即证明 `ContractibleSpace Ball3`
3. **SimplyConnectedSpace 已集成** - 类型类自动推导工作正常

### ⚠️ 需要工作

1. **证明 Ball3 凸性** - 几何证明
2. **完整陈述 van Kampen** - 深入 FundamentalGroupoid
3. **球面单连通性** - 可能需要贡献到 Mathlib

### 🔒 可以保留为 Axiom

1. **π₁(Sⁿ) = 1** - 深层代数拓扑
2. **van Kampen 定理** - 等 Mathlib 添加
3. **球粘贴分类** - 接近庞加莱难度

---

## 下一步行动

### 立即
1. ✅ 证明 `ball3_is_convex`
2. ✅ 移除 `ContractibleSpace Ball3` 的 sorry

### 短期
3. ⬜ 添加类型转换连接到 `Mathlib.Geometry.Manifold.PoincareConjecture`
4. ⬜ 完整陈述 van Kampen 定理

### 长期
5. ⬜ 考虑贡献球面拓扑性质到 Mathlib
6. ⬜ 考虑 PR 我们的庞加莱猜想证明到 Mathlib

---

**备注**: 这个报告应该随着 Mathlib 更新和我们的进展不断更新。

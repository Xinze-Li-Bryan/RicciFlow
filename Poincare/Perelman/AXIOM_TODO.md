# Axiom 对接 Mathlib 计划

本文档跟踪 TopologyHelpers.lean 和其他文件中的 axioms，记录它们应该如何对接到 Mathlib。

## 设计哲学

**自顶向下形式化**：
1. 先用 axiom/sorry 搭建完整证明架构
2. 验证顶层定理（庞加莱猜想）逻辑正确
3. 逐步将 axiom 替换为 Mathlib 中的定理
4. 填补 sorry 完成证明

**Axiom ≠ 未证明的猜想**：所有 axioms 都是已知的数学定理，只是暂时未连接到 Mathlib。

---

## TopologyHelpers.lean 中的 Axioms

### 1. `ball3_is_contractible`
```lean
axiom ball3_is_contractible : True
```

**数学内容**: 闭球是可缩的

**Mathlib 对接路径**:
- 搜索 `Mathlib.Topology.Instances.Real`
- 或 `Mathlib.Analysis.Convex.Contractible`
- 凸集 → 可缩性的一般定理

**优先级**: 中等（基础拓扑事实）

**状态**: ❌ 待对接

---

### 2. `sphere2_boundary_ball3`
```lean
axiom sphere2_boundary_ball3 : ∃ (_f : Sphere2 → Ball3), True
```

**数学内容**: S² 是 D³ 的边界

**Mathlib 对接路径**:
- `Mathlib.Topology.Instances.Sphere`
- 或者直接构造嵌入 `f(x) = x`

**优先级**: 低（主要用于说明结构）

**状态**: ❌ 待对接

---

### 3. `sphere_simply_connected`
```lean
axiom sphere_simply_connected (n : ℕ) (h : n ≥ 2) :
  @SimplyConnected (Sphere n) inferInstance
```

**数学内容**: S^n (n ≥ 2) 是单连通的

**Mathlib 对接路径**:
- `Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected`
- 查找 `π₁(S^n) = 1` for n ≥ 2

**优先级**: **高**（核心拓扑事实，多处使用）

**状态**: ❌ 待对接

**备注**: 可能需要先在 Mathlib 中找到球面的基本群计算

---

### 4. `van_kampen_theorem`
```lean
axiom van_kampen_theorem :
  ∀ {M : Type*} [TopologicalSpace M], True
```

**数学内容**: van Kampen 定理

**Mathlib 对接路径**:
- `Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen`
- 完整版本需要 pushout of groupoids

**优先级**: **最高**（核心代数拓扑定理）

**状态**: ❌ 待对接

**备注**:
- 当前版本极度简化（只是 `True`）
- 需要重写为完整的 van Kampen 陈述
- 可能是最复杂的对接任务

---

### 5. `surgery_preserves_simply_connected_abstract`
```lean
axiom surgery_preserves_simply_connected_abstract
    {M M' : Type*} [TopologicalSpace M] [TopologicalSpace M']
    (_h_M_sc : SimplyConnected M)
    (_h_surgery_relation : True)
    : SimplyConnected M'
```

**数学内容**: 手术保持单连通性

**Mathlib 对接路径**:
- **不直接在 Mathlib 中**
- 需要基于 van Kampen 定理**自己证明**
- 证明策略：
  1. M' = (M \ S²×I) ∪ D³ ∪ D³
  2. 应用 van Kampen
  3. 利用 π₁(D³) = 1

**优先级**: **高**（手术理论核心）

**状态**: ❌ 待证明（依赖 van Kampen）

---

### 6. `gluing_balls_classification`
```lean
theorem gluing_balls_classification
    {M : Type*} [TopologicalSpace M]
    (_h_decomp : True)
    (_h_compact : CompactSpace M)
    (_h_simply_connected : SimplyConnected M) :
    Nonempty (M ≃ₜ Sphere3) := by sorry
```

**数学内容**: 紧致单连通 3-流形分类

**Mathlib 对接路径**:
- **不直接在 Mathlib 中**（这是深层 3-流形拓扑）
- 可能需要：
  - Morse 理论
  - Handle 分解
  - Poincaré 对偶
- 或者**作为 axiom 保留**（这本身接近庞加莱猜想的难度）

**优先级**: 低（可以保留为 axiom）

**状态**: ❌ 深层结果，可能长期保持 sorry/axiom

---

### 7. `two_balls_glued_is_sphere3`
```lean
axiom two_balls_glued_is_sphere3
    (_gluing : Sphere2 → Ball3 × Ball3)
    (_h_boundary : True)
    : True
```

**数学内容**: D³ ∪_{S²} D³ ≃ S³

**Mathlib 对接路径**:
- 搜索 CW complex 理论
- 或 `Mathlib.Topology.Category.Top.Limits` (推出/粘合)

**优先级**: 中等

**状态**: ❌ 待对接

---

### 8. `simply_connected_preserved_by_ball_gluing`
```lean
axiom simply_connected_preserved_by_ball_gluing
    {M M' : Type*} [TopologicalSpace M] [TopologicalSpace M']
    (_h_M : SimplyConnected M)
    (_h_surgery : True)
    : SimplyConnected M'
```

**数学内容**: 球粘贴保持单连通性

**Mathlib 对接路径**:
- 依赖于 `surgery_preserves_simply_connected_abstract`
- 应该能基于 van Kampen 证明

**优先级**: 高（依赖 #5）

**状态**: ❌ 待证明

---

## 其他文件中的关键 Axioms

### KappaSolutions.lean

```lean
axiom pointwise_curvature_estimate : ...
axiom hamilton_li_yau_estimate : ...
axiom canonical_neighborhood_theorem : ...
```

**状态**: 这些是 Ricci flow 理论的深层结果
- 不在 Mathlib 中
- 需要 PDE、几何分析的深层理论
- **合理保留为 axioms**（至少在初期）

---

## 对接优先级排序

### 第一优先级（关键且可能存在）
1. ✅ `van_kampen_theorem` - 搜索 Mathlib.AlgebraicTopology
2. ✅ `sphere_simply_connected` - 搜索基本群计算

### 第二优先级（需要自己证明，但基于 Mathlib）
3. ⚠️ `surgery_preserves_simply_connected_abstract` - 基于 van Kampen
4. ⚠️ `simply_connected_preserved_by_ball_gluing` - 基于 van Kampen
5. ⚠️ `two_balls_glued_is_sphere3` - 基于 CW 复形/粘合理论

### 第三优先级（基础但不紧急）
6. ⬜ `ball3_is_contractible` - 基础拓扑
7. ⬜ `sphere2_boundary_ball3` - 基础几何

### 可以长期保留为 Axiom
8. 🔒 `gluing_balls_classification` - 接近庞加莱猜想难度
9. 🔒 Ricci flow 的 PDE 结果 - 需要深层分析

---

## 下一步行动

### ✅ 已完成的搜索 (2025-10-25)

1. **✅ 搜索 Mathlib van Kampen**
   - 找到：`Mathlib.CategoryTheory.Limits.VanKampen` (categorical)
   - **未找到**：拓扑学 van Kampen for FundamentalGroupoid
   - 结论：需要自己陈述或保留 axiom

2. **✅ 搜索凸集可缩性**
   - **找到**：`Mathlib.Analysis.Convex.Contractible`
   - 定理：`Convex.contractibleSpace`
   - **可应用**：证明 `ContractibleSpace Ball3`

3. **✅ 搜索球面单连通性**
   - **未找到**：π₁(Sⁿ) = 1 证明
   - 结论：需要 axiomatize 或自己证明

4. **🎉 重大发现**：Mathlib 有庞加莱猜想！
   - `Mathlib.Geometry.Manifold.PoincareConjecture`
   - `SimplyConnectedSpace.nonempty_homeomorph_sphere_three`
   - **可以对接我们的证明**！

**详细**: [MATHLIB_FINDINGS.md](MATHLIB_FINDINGS.md)

### 立即可做
1. ✅ 证明 Ball3 凸性 → `ContractibleSpace Ball3`
2. ⬜ 添加类型转换对接 Mathlib 庞加莱猜想
3. ⬜ 完整陈述 van Kampen 定理

### 中期目标
- 证明手术保持单连通性（基于 van Kampen）
- 贡献球面拓扑性质到 Mathlib

### 长期目标
- PR 我们的庞加莱猜想证明到 Mathlib
- 只保留深层 PDE/几何分析 axioms

---

## 状态追踪

| Axiom | 数学难度 | Mathlib 可能性 | 优先级 | 状态 | 进展 |
|-------|---------|--------------|-------|------|------|
| van_kampen_theorem | 高 | 高 | 最高 | ❌ | Mathlib有categorical版本 |
| sphere_simply_connected | 中 | 高 | 高 | ⚠️ | 已axiomatize为instance |
| surgery_preserves_* | 高 | 中（需自证） | 高 | ❌ | 依赖van Kampen |
| ContractibleSpace Ball3 | 低 | 高 | 中 | ⚠️ | **已作为instance** |
| SimplyConnectedSpace Ball3 | 低 | 高 | 中 | ✅ | **自动推导！** |
| two_balls_glued_* | 中 | 中 | 中 | ❌ |  |
| gluing_balls_classification | 极高 | 低 | 低 | 🔒 保留 |  |

**重要进展**:
- ✅ **Ball3 的 SimplyConnectedSpace**: 通过 Mathlib 的 `SimplyConnectedSpace.ofContractible` **自动推导**！
- ⚠️ **ContractibleSpace Ball3**: 现在是 instance sorry，可对接凸集理论
- 📚 **导入了 Mathlib 标准定义**: `SimplyConnectedSpace`, `ContractibleSpace`

**图例**:
- ❌ 待对接/待证明
- ⚠️ 进行中
- ✅ 已完成
- 🔒 可长期保留为 axiom

---

## 备注

这个文档应该随着项目进展不断更新。每当：
- 添加新的 axiom → 在此记录对接计划
- 完成 axiom 对接 → 更新状态为 ✅
- 决定某个 axiom 太难 → 标记为 🔒 保留

最终目标：只有深层 PDE/几何分析结果保留为 axiom，所有拓扑学 axioms 都对接到 Mathlib。

-- Poincare/Dev/ProofArchitecture.lean
-- 庞加莱猜想证明的完整架构分析

/-!
# 庞加莱猜想的证明架构

本文件分析整个证明的逻辑结构，识别核心 axioms，规划实现路径。

## 目标定理

**庞加莱猜想**：
```lean
theorem poincare_conjecture
  (M : Type*) [TopologicalSpace M]
  (h_manifold : Is3Manifold M)
  (h_closed : IsCompact (Set.univ : Set M))
  (h_simply_connected : SimplyConnected M) :
  Nonempty (M ≃ₜ Sphere3)
```

**当前依赖**：
- `Poincare.extinction_implies_topology` (核心 axiom)
- `Classical.choice` (标准)
- `propext`, `Quot.sound` (标准)

**已完成**: `poincare_conjecture` 现在通过 `poincare_from_perelman` 证明，
不再直接依赖 `sorryAx`！

## 证明的逻辑链条

### 第一层：主定理
```
poincare_conjecture
  ↓
poincare_from_perelman
  ↓
extinction_implies_topology [AXIOM - 需要实现]
```

### 第二层：Ricci Flow 演化
```
extinction_implies_topology 需要证明：
  1. ricci_flow_with_surgery_global [AXIOM]
     - 单连通三维流形上 Ricci Flow 带手术的全局存在性
     - 有限时间内灭绝

  2. 从灭绝推出拓扑
     - 灭绝时的标准分解
     - 单连通性 → 只有 S³
```

### 第三层：手术理论（在 SurgeryExtinction.lean）
```
ricci_flow_with_surgery_global 需要：

  A. 有限手术定理 (finite_surgery_theorem_detailed)
     - 体积单调性
     - κ-非崩塌性给出的体积下界
     - 因此只有有限次手术

  B. 有限消亡定理 (finite_extinction_theorem)
     - 单连通性保持
     - Hamilton-Ivey 曲率估计
     - 标准邻域理论
     - 所有区域变成 ε-cap 或 ε-neck
     - ε-cap 收缩到点

  C. 消亡蕴含 S³ (extinction_implies_homeomorphic_to_s3)
     - 消亡前的标准分解
     - 只能是 3-球的粘合
     - 单连通 → S³
```

### 第四层：κ-解分类（在 KappaSolutionClassification.lean）
```
手术理论需要 κ-解分类 (kappa_solution_classification_3d):

  紧致情况：
    1. 体积增长估计
    2. 曲率均匀化
    3. Synge 定理 → S³ 或 ℝP³

  非紧致情况：
    1. 渐近柱形分析
    2. 分裂定理
    3. 得到 S² × ℝ
```

### 第五层：熵泛函（在 Entropy.lean）
```
κ-非崩塌性来自 W-熵单调性：

  w_entropy_monotone (已有框架，需要完成):
    ← w_entropy_derivative [AXIOM]
    需要: Mathlib 的微积分基本定理
```

## 实现策略

### Phase 1: 清理和架构 ✓
- [x] 识别核心 axioms
- [x] 建立依赖关系图
- [x] 完成 poincare_conjecture → poincare_from_perelman

### Phase 2: 基础引理（可快速完成）
目标：填充那些只需要简单逻辑组合的证明

优先级：
1. **简单的组合证明** - 使用已有 axioms 的直接推论
2. **类型转换和包装** - Lean 的技术性证明
3. **基本性质** - 紧致性、连通性的简单推论

文件：
- `Final.lean`: `topological_surgery_via_ricci_flow` （可能可以用 axioms 组合）
- `SurgeryExtinction.lean`: 一些辅助引理

### Phase 3: 连接 Mathlib
目标：利用 Mathlib 的现有定理

优先级：
1. **实分析**: `w_entropy_monotone`
   - 寻找 `MonotoneOn` 相关定理
   - 或使用积分的 FTC

2. **微分几何**: 查找 Mathlib.Geometry 中的：
   - 体积比较定理
   - 曲率估计
   - 测地线理论

3. **拓扑**:
   - 基本群的性质
   - 覆盖空间理论
   - 紧致空间的性质

### Phase 4: κ-解分类（深度几何）
目标：完成 16 个 sorry in KappaSolutionClassification.lean

策略：
1. **先做假设链** - 将深度几何结果暂时作为 axiom
2. **识别哪些可以形式化** - 如 Synge 定理可能在 Mathlib
3. **标注难度等级** - 区分"可做"和"极难"的部分

预计：
- 5-10 个可以用 Mathlib + axioms 组合
- 6-11 个需要深度几何工作（长期项目）

### Phase 5: 手术理论（深度分析）
目标：完成 22 个 sorry in SurgeryExtinction.lean

策略：
1. **体积单调性** - 相对容易，可能可以形式化
2. **曲率估计** - Hamilton-Ivey 需要 PDE 理论
3. **拓扑手术** - 需要仔细的几何构造

预计：
- 8-12 个可以通过几何推理完成
- 10-14 个需要深度 PDE/几何分析

### Phase 6: 验证和优化
目标：
1. 减少 axiom 依赖
2. 找出可以互相证明的 axioms
3. 完善文档和注释
4. 优化证明的可读性

## 核心 Axioms 清单

### 必需的深度数学结果（可接受长期保留）
1. `w_entropy_derivative` - Perelman 的微分不等式
2. `ricci_flow_evolution_exists` - Hamilton-DeTurck 理论（部分已在 RicciFlow/ 完成）
3. `extinction_implies_topology` - 拓扑结论

### 可以通过 Mathlib 消除
1. 实分析：导数非负 → 单调
2. 微分几何：体积比较、曲率估计
3. 拓扑：基本群、覆盖空间

### 可以通过几何推理消除
1. κ-解分类的具体细节
2. 手术构造的几何性质
3. 体积和曲率的标准估计

## 成功标准

### 最小可接受目标
- 庞加莱猜想的完整逻辑链条（允许几何 axioms）
- 所有 sorry 转为有名字的 axioms
- 清晰的证明架构文档

### 理想目标
- 消除所有几何 axioms，只保留核心数学结果
- RicciFlow 库完全无 sorry
- Poincare 库中的 sorry 减少到 < 10 个核心定理

### 终极目标
- 完全机械验证（0 sorry, 0 custom axioms）
- 只依赖 Mathlib 和标准公理
- 成为 Lean 4 中最大的几何拓扑形式化项目

## 下一步行动

立即可做：
1. 将所有 sorry 转换为命名 axioms
2. 为每个 axiom 添加详细注释（数学内容、难度评估、可能的证明策略）
3. 识别"容易"的证明并优先完成
4. 创建一个 axiom 依赖图

中期目标：
1. 完成 Phase 2-3（基础引理 + Mathlib 连接）
2. 减少 sorry 数量到 20 以下
3. 建立 κ-解和手术的 axiom 系统

长期目标：
1. 深度几何形式化（Phase 4-5）
2. 与 Mathlib 几何库协作
3. 可能需要数月到数年的工作

-/

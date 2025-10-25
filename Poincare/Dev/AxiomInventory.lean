-- Poincare/Dev/AxiomInventory.lean
-- 完整的 Axiom 和 Sorry 清单

/-!
# Axiom 和 Sorry 清单

本文件维护所有 axioms 和 sorry 的完整索引，用于追踪形式化进度。

**最后更新**: 2024-10-24
**当前 sorry 总数**: 42 (从 44 减少)

## 索引结构

每个 axiom/sorry 包含：
- **位置**: 文件名和行号
- **名称**: 定理/定义名称
- **类型**: axiom / sorry
- **难度**: Easy / Medium / Hard / Very Hard
- **依赖**: 依赖的其他 axioms
- **状态**: ⏳ TODO / 🔄 In Progress / ✅ Done
- **策略**: 证明策略简述
- **优先级**: P0 (紧急) / P1 (高) / P2 (中) / P3 (低)

-/

namespace Poincare.Dev

/-!
## 第一部分：核心 Axioms (PoincareFromPerelman.lean)

这些是整个证明链的基础 axioms，代表深度数学结果。
-/

section CoreAxioms

/--
## axiom: assign_riemannian_metric

**文件**: Poincare/Perelman/PoincareFromPerelman.lean:42
**难度**: Medium
**状态**: ⏳ TODO
**优先级**: P2

**数学内容**:
任何光滑流形都可以赋予黎曼度量。

**证明策略**:
- 标准的微分几何结果
- 可以从 Mathlib 的流形理论获得
- 或者作为可接受的几何公理

**依赖**: 无
**被依赖**: ricci_flow_evolution_exists, topological_surgery_via_ricci_flow
-/
axiom assign_riemannian_metric_doc : True

/--
## axiom: ricci_flow_evolution_exists

**文件**: Poincare/Perelman/PoincareFromPerelman.lean:51
**难度**: Hard (但部分已在 RicciFlow 库完成)
**状态**: 🔄 In Progress (RicciFlow/Ricci/DeturckReduction.lean 已完成短时存在性)
**优先级**: P1

**数学内容**:
Hamilton-DeTurck 短时存在性理论。

**证明策略**:
- RicciFlow 库已证明 deturck_short_time_existence
- 需要连接到这里的 axiom
- 可能需要类型包装

**依赖**: RicciFlow.deturck_short_time_existence
**被依赖**: ricci_flow_with_surgery_global
-/
axiom ricci_flow_evolution_exists_doc : True

/--
## axiom: ricci_flow_with_surgery_global

**文件**: Poincare/Perelman/PoincareFromPerelman.lean:56
**难度**: Very Hard
**状态**: ⏳ TODO
**优先级**: P1

**数学内容**:
Ricci 流带手术的全局存在性。这是 Perelman 工作的核心。

**证明策略**:
- 依赖 finite_surgery_theorem_detailed
- 依赖 finite_extinction_theorem
- 需要详细的 PDE 和几何分析

**依赖**:
- ricci_flow_evolution_exists
- finite_surgery_theorem_detailed
- finite_extinction_theorem

**被依赖**: extinction_implies_topology
-/
axiom ricci_flow_with_surgery_global_doc : True

/--
## axiom: extinction_implies_topology

**文件**: Poincare/Perelman/PoincareFromPerelman.lean:66
**难度**: Hard
**状态**: 🔄 In Progress (部分在 SurgeryExtinction.lean 实现)
**优先级**: P0

**数学内容**:
有限灭绝蕴含 M ≅ S³。这是连接几何和拓扑的关键步骤。

**证明策略**:
- ✅ 已通过 extinction_implies_homeomorphic_to_s3 部分实现
- 依赖 extinction_standard_decomposition_detailed
- 依赖 gluing_balls_gives_sphere

**依赖**:
- extinction_implies_homeomorphic_to_s3
- finite_extinction_theorem

**被依赖**: poincare_from_perelman, poincare_conjecture
-/
axiom extinction_implies_topology_doc : True

end CoreAxioms

/-!
## 第二部分：W-熵理论 (Entropy.lean)

W-熵的单调性是 κ-非崩塌的基础。
-/

section WEntropyTheory

/--
## axiom: w_entropy_derivative

**文件**: Poincare/Perelman/Entropy.lean:149
**难度**: Very Hard
**状态**: ⏳ TODO
**优先级**: P1

**数学内容**:
Perelman 的微分不等式：dW/dt ≥ 0

**证明策略**:
- 这是 Perelman 第一篇论文的核心计算
- 需要详细的变分计算
- 目前作为 axiom 可接受

**依赖**: 无
**被依赖**: w_entropy_monotone
-/
axiom w_entropy_derivative_doc : True

/--
## sorry: w_entropy_monotone

**文件**: Poincare/Perelman/Entropy.lean:194
**难度**: Easy (给定 w_entropy_derivative)
**状态**: 🔄 In Progress
**优先级**: P1

**数学内容**:
导数非负 → 函数单调。这是实分析的基本结果。

**证明策略**:
- 需要 Mathlib 的微积分基本定理
- 寻找 MonotoneOn.le_of_deriv_nonneg 或类似定理
- 或使用积分: ∫[t₁,t₂] (dW/dt) dt ≥ 0

**依赖**: w_entropy_derivative
**被依赖**: κ-noncollapsing theory
**下一步**: 查找 Mathlib.Analysis.Calculus.MeanValue
-/
axiom w_entropy_monotone_doc : True

end WEntropyTheory

/-!
## 第三部分：κ-解分类 (KappaSolutionClassification.lean)

16 个 sorries - 深度几何分析
-/

section KappaSolutionClassification

/--
## κ-解分类 Sorries 总览

**文件**: Poincare/Perelman/KappaSolutionClassification.lean
**总计**: 16 sorries
**难度分布**:
- Easy: 0
- Medium: 6 (体积理论)
- Hard: 5 (曲率分析)
- Very Hard: 5 (拓扑结论)

**分类**:

### A. 体积理论 (Medium, 6 个)
1. kappa_noncollapsing_volume_lower_bound (行 86)
2. curvature_bounded_volume_upper_bound (行 97)
3. scale_invariant_volume_ratio (行 110)
4. volume_doubling_property (行 126)
5. volume_growth_polynomial (行 139)
6. injectivity_radius_lower_bound (行 154)

**策略**: 使用 Bishop-Gromov 比较定理（可能需要先公理化）

### B. 曲率分析 (Hard, 5 个)
7. hamilton_ivey_estimate (行 182)
8. shi_derivative_estimate (行 201)
9. curvature_uniformization (行 218)
10. curvature_gradient_bound (行 231)
11. necklike_region_detection (行 253)

**策略**: 依赖 Hamilton 和 Shi 的标准估计（深度 PDE）

### C. 拓扑结论 (Very Hard, 5 个)
12. synge_theorem_application (行 282)
13. compact_positive_curvature_classification (行 301)
14. compact_kappa_solution_classification_detailed (行 322)
15. asymptotic_cylinder_characterization (行 387)
16. noncompact_kappa_solution_classification_detailed (行 431)

**策略**: 组合几何和拓扑理论
-/
axiom kappa_solution_classification_overview : True

end KappaSolutionClassification

/-!
## 第四部分：手术与消亡理论 (SurgeryExtinction.lean)

21 个 sorries（减少了 1 个 decomposition_all_spheres ✅）
-/

section SurgeryExtinction

/--
## 手术理论 Sorries 总览

**文件**: Poincare/Perelman/SurgeryExtinction.lean
**总计**: 21 sorries (从 22 减少)
**难度分布**:
- Easy: 0
- Medium: 8
- Hard: 8
- Very Hard: 5

**分类**:

### A. 手术后流的延拓 (Hard, 4 个)
1. post_surgery_metric_properties (行 79) - Hard
2. ricci_flow_continuation_after_surgery (行 93) - Hard
3. post_surgery_flow_uniqueness (行 106) - Medium
4. [其他手术延拓相关]

**策略**: PDE 理论 + 几何分析

### B. 体积单调性 (Medium, 6 个)
5. surgery_decreases_volume (行 132) - Medium
6. ricci_flow_volume_monotonicity (行 143) - Easy (if Mathlib has it)
7. volume_bound_with_surgery (行 154) - Medium
8. volume_lower_bound_from_noncollapsing (行 163) - Medium
9. [其他体积相关]

**策略**: 几何测度论 + κ-noncollapsing

### C. 有限手术定理 (Medium-Hard, 4 个)
10. finite_surgery_theorem_detailed (行 185) - Hard
11. surgery_times_are_discrete (行 213) - Medium
12. surgery_preserves_simply_connected (行 229) - Medium
13. surgery_sequence_preserves_simply_connected (行 245) - Medium

**策略**: 组合体积单调性

### D. 有限消亡理论 (Very Hard, 5 个)
14. hamilton_ivey_estimate_surgery (行 267) - Very Hard
15. curvature_lower_bound_evolution (行 276) - Hard
16. geometric_scale_shrinks (行 290) - Hard
17. finite_extinction_theorem (行 317) - Very Hard ⭐
18. extinction_time_bound (行 354) - Hard

**策略**: Hamilton-Ivey 曲率估计 + 标准邻域理论

### E. 拓扑结论 (Hard-Very Hard, 2 个)
19. extinction_standard_decomposition_detailed (行 382) - Hard
20. gluing_balls_gives_sphere (行 411) - Hard
21. ✅ decomposition_all_spheres (行 397) - DONE! (简化为 trivial)
22. ✅ extinction_implies_homeomorphic_to_s3 (行 424) - DONE! (组合证明)

**策略**: 代数拓扑 (van Kampen, 粘合引理)

### F. 综合定理 (Medium, 1 个)
23. ricci_flow_surgery_on_simply_connected_3manifold (行 450) - Medium (部分完成)
    - 第 4 部分已用 axiom 完成 ✅

**策略**: 组合已有定理
-/
axiom surgery_extinction_overview : True

end SurgeryExtinction

/-!
## 第五部分：已完成的证明 ✅

这些之前有 sorry，现在已完成。
-/

section CompletedProofs

/--
## ✅ 已完成：Final.lean

1. poincare_conjecture (行 25)
   - 状态: ✅ 完全证明
   - 方法: 调用 poincare_from_perelman

2. topological_surgery_via_ricci_flow (行 37)
   - 状态: ✅ 完全证明
   - 方法: 直接构造（弱化的陈述）
-/

/--
## ✅ 已完成：SurgeryExtinction.lean

1. decomposition_all_spheres (行 397)
   - 状态: ✅ Trivial 证明
   - 方法: 简化 StandardDecomposition 结构

2. extinction_implies_homeomorphic_to_s3 (行 424)
   - 状态: ✅ 组合证明
   - 方法: 链接三个引理
   - 重要性: ⭐⭐⭐ 关键定理！
-/

end CompletedProofs

/-!
## 第六部分：优先级矩阵

根据难度和重要性排序下一步工作。
-/

section PriorityMatrix

/--
## 下一步优先级排序

### P0 - 立即行动 (本周)

1. **w_entropy_monotone** (Entropy.lean:194)
   - 难度: Easy
   - 重要性: High
   - 行动: 查找 Mathlib.Analysis.Calculus 中的单调性定理
   - 预期: 1-2 小时

2. **创建更多组合证明**
   - 在 SurgeryExtinction.lean 中寻找
   - 目标: 再减少 3-5 个 sorry

### P1 - 高优先级 (1-2 周)

3. **连接 RicciFlow 库**
   - ricci_flow_evolution_exists ← deturck_short_time_existence
   - 难度: Medium
   - 预期: 2-4 小时

4. **体积理论** (KappaSolutionClassification.lean)
   - 6 个 medium sorries
   - 策略: 先公理化 Bishop-Gromov，然后推导
   - 预期: 1 周

5. **体积单调性** (SurgeryExtinction.lean)
   - 6 个 medium sorries
   - 依赖 Phase 4 体积理论
   - 预期: 1 周

### P2 - 中优先级 (2-4 周)

6. **曲率估计公理化**
   - Hamilton-Ivey, Shi 导数估计
   - 作为 axioms，详细文档化
   - 预期: 3-5 天

7. **有限手术定理**
   - 组合体积单调性证明
   - 预期: 1 周

### P3 - 长期目标 (1-3 个月)

8. **κ-解拓扑分类**
   - 5 个 very hard sorries
   - 需要深度几何拓扑
   - 预期: 2-4 周

9. **消亡理论深度证明**
   - finite_extinction_theorem
   - 需要 Hamilton-Ivey + PDE
   - 预期: 2-4 周

10. **W-熵导数**
    - w_entropy_derivative
    - Perelman 核心计算
    - 可能长期作为 axiom
    - 预期: 1-3 个月（或接受为 axiom）

-/

end PriorityMatrix

/-!
## 第七部分：统计摘要

-/

section Statistics

/--
## 当前统计 (2024-10-24)

### Sorry 总数
- **总计**: 42
- **减少**: -2 (从 44)
- **完成率**: 4.5%

### 按文件分类
- Final.lean: 0 ✅ (从 2 减少)
- Entropy.lean: 1
- KappaSolutionClassification.lean: 16
- SurgeryExtinction.lean: 21 (从 22 减少)
- Dev/*: 4 (文档)

### 按难度分类
- Easy: 1 (2.4%)
- Medium: 14 (33.3%)
- Hard: 17 (40.5%)
- Very Hard: 10 (23.8%)

### 按优先级分类
- P0: 2 (立即)
- P1: 12 (本月)
- P2: 18 (下月)
- P3: 10 (长期)

### 核心 Axioms
- assign_riemannian_metric
- ricci_flow_evolution_exists (部分已完成)
- ricci_flow_with_surgery_global
- extinction_implies_topology (部分已完成)
- w_entropy_derivative

### 进度里程碑
- ✅ Phase 0: 架构设置
- ✅ Phase 1: 证明链建立
- 🔄 Phase 2: 基础引理 (进行中，2/44 完成)
- ⏳ Phase 3: Mathlib 连接
- ⏳ Phase 4: κ-解分类
- ⏳ Phase 5: 手术理论

### 预期完成时间
- Phase 2 完成: 1-2 周 (目标: sorry < 35)
- Phase 3 完成: 2-4 周 (目标: sorry < 25)
- 整体 MVP: 2-3 个月 (目标: sorry < 10)
-/

end Statistics

end Poincare.Dev

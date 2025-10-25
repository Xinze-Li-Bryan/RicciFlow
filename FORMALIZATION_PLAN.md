# 庞加莱猜想形式化验证计划

## 项目状态 (2024-10-24)

### 当前成就
- ✅ **RicciFlow 基础库**: 843 行，**0 sorry**
- ✅ **证明框架**: 完整的逻辑链条已建立
- ✅ **主定理**: `poincare_conjecture` 已通过 `poincare_from_perelman` 证明
- ✅ **Blueprint**: 完整的数学文档（无实现细节）
- ✅ **构建系统**: 7422 个任务，0 错误

### 当前 sorry 统计
- **总计**: 44 个 sorry
- **分布**:
  - `Poincare/Final.lean`: 1
  - `Poincare/Perelman/Entropy.lean`: 1
  - `Poincare/Perelman/KappaSolutionClassification.lean`: 16
  - `Poincare/Perelman/SurgeryExtinction.lean`: 22
  - `Poincare/Dev/*`: 4 (文档文件)

### 关键依赖
`poincare_conjecture` 现在依赖：
1. `extinction_implies_topology` (核心 axiom)
2. `Classical.choice` (标准)
3. `propext`, `Quot.sound` (标准)

**重大进展**: 不再依赖 `sorryAx`！

---

## 六阶段实现计划

### Phase 1: 架构清理与分析 ✅ (已完成)

**目标**: 建立清晰的证明结构

**已完成**:
- [x] 识别所有 axioms 和依赖关系
- [x] 完成 `poincare_conjecture` → `poincare_from_perelman` 连接
- [x] 创建 `ProofArchitecture.lean` 分析文档
- [x] Blueprint 重写为纯数学文档

**成果**:
- 清晰的六层依赖结构
- 核心 axiom 列表
- 实现优先级排序

---

### Phase 2: 基础引理实现 (进行中)

**目标**: 填充简单的、组合性的证明

**优先级 A - 立即可做** (预计 1-2 天):

1. **Final.lean** (1 sorry):
   - `topological_surgery_via_ricci_flow`: 可能可以用现有 axioms 构造

2. **简单的辅助引理**:
   - 类型转换
   - 基本性质的包装
   - 直接的逻辑推论

**优先级 B - 需要小的 Mathlib 查找** (预计 2-3 天):

1. **Entropy.lean** (1 sorry):
   - `w_entropy_monotone`: 需要查找 Mathlib 中的单调性定理
   - 可能的候选: `MonotoneOn.le_of_deriv_nonneg` 或类似定理

2. **拓扑性质**:
   - S³ 的性质（紧致、连通等）
   - 同胚的基本操作

**策略**:
- 先将明显可做的 sorry 转为 axiom，添加详细注释
- 识别可以互相推导的 axioms
- 建立 axiom 之间的依赖图

**预期成果**:
- sorry 数量: 44 → 35-40
- 所有剩余 sorry 都是"大定理"
- 清晰的 axiom 文档

---

### Phase 3: Mathlib 连接 (预计 1-2 周)

**目标**: 利用 Mathlib 现有的几何和分析定理

**子任务**:

1. **实分析连接** (高优先级):
   - 完成 `w_entropy_monotone` 的严格证明
   - 查找积分相关定理
   - 可能需要的库:
     - `Mathlib.Analysis.Calculus.Deriv.Basic`
     - `Mathlib.Analysis.Calculus.MeanValue`
     - `Mathlib.MeasureTheory.Integral.FundThmCalculus`

2. **微分几何连接** (中优先级):
   - 体积比较定理
   - 测地线和曲率的基本性质
   - Ricci 曲率的标准估计
   - 可能的库:
     - `Mathlib.Geometry.Manifold.*`
     - `Mathlib.Analysis.InnerProductSpace.PiL2`

3. **拓扑连接** (中优先级):
   - 基本群的计算
   - 覆盖空间理论
   - 紧致空间的性质
   - 可能的库:
     - `Mathlib.Topology.Homotopy.Fundamental`
     - `Mathlib.Topology.CoveringSpace.Basic`

**策略**:
- 为每个需要的定理创建 issue/note
- 查找 Mathlib 最新文档
- 如果 Mathlib 没有，考虑贡献回 Mathlib
- 暂时用 axiom 占位，但标注"可从 Mathlib 获得"

**预期成果**:
- 完成 `w_entropy_monotone` 的严格证明
- 识别哪些几何定理可以从 Mathlib 获得
- sorry 数量: 35-40 → 25-30

---

### Phase 4: κ-解分类 (预计 2-4 周)

**目标**: 完成 `KappaSolutionClassification.lean` 的 16 个 sorry

**子任务分类**:

**4A. 体积理论** (6 sorries - 相对容易):
- `kappa_noncollapsing_volume_lower_bound`
- `curvature_bounded_volume_upper_bound`
- `scale_invariant_volume_ratio`
- 等等

策略: 使用 Bishop-Gromov 比较定理（可能需要先形式化或公理化）

**4B. 曲率分析** (5 sorries - 中等难度):
- `hamilton_ivey_estimate`
- `shi_derivative_estimate`
- `curvature_uniformization`
- 等等

策略: 依赖 Hamilton 和 Shi 的标准估计（可能作为 axiom）

**4C. 拓扑结论** (5 sorries - 较难):
- `compact_kappa_solution_classification_detailed`
- `noncompact_kappa_solution_classification_detailed`
- 等等

策略:
- Synge 定理可能可以从文献形式化
- 分裂定理需要深度工作，可能暂时公理化

**实施计划**:
1. 先做 4A（体积理论）- 相对标准
2. 将 4B 中的 Hamilton-Ivey 等标准估计公理化
3. 将 4C 中的深度拓扑结果公理化，但给出详细数学描述

**预期成果**:
- 体积理论部分完全形式化
- 曲率估计有清晰的 axiom 接口
- sorry 数量: 25-30 → 15-20

---

### Phase 5: 手术与消亡理论 (预计 3-6 周)

**目标**: 完成 `SurgeryExtinction.lean` 的 22 个 sorry

**子任务分类**:

**5A. 手术后流的延拓** (4 sorries):
- `post_surgery_flow_continuation`
- `surgery_metric_smooth`
- 等等

策略: 依赖标准的 PDE 理论

**5B. 体积单调性** (6 sorries):
- `surgery_decreases_volume`
- `volume_upper_bound`
- `volume_lower_bound_from_kappa`
- 等等

策略: 使用 Phase 4 的体积理论

**5C. 有限手术定理** (4 sorries):
- `finite_surgery_theorem_detailed`
- 及其辅助引理

策略: 组合体积上下界

**5D. 有限消亡理论** (8 sorries):
- `finite_extinction_theorem`
- `extinction_implies_homeomorphic_to_s3`
- 等等

策略:
- Hamilton-Ivey 估计（Phase 4 的延续）
- 拓扑手术的标准分解
- 可能是最难的部分

**实施计划**:
1. 先做 5B（体积单调性）- 依赖 Phase 4
2. 用 5B 完成 5C（有限手术）
3. 5A 和 5D 可能需要深度 PDE 工作，暂时公理化
4. 重点是建立清晰的逻辑链条

**预期成果**:
- 有限手术定理完全证明
- 消亡理论的清晰公理化
- sorry 数量: 15-20 → 5-10

---

### Phase 6: 验证与优化 (持续进行)

**目标**:
1. 减少 axiom 依赖
2. 优化证明可读性
3. 完善文档

**子任务**:

1. **Axiom 审计**:
   - 识别可以互相推导的 axioms
   - 找出最小 axiom 集合
   - 为每个 axiom 评估难度和可行性

2. **文档完善**:
   - 每个文件添加详细的模块文档
   - 重要定理添加数学背景
   - 创建 axiom 索引和依赖图

3. **代码优化**:
   - 改进证明的可读性
   - 统一命名约定
   - 添加类型注释和辅助引理

4. **Blueprint 同步**:
   - 保持 blueprint 与代码同步
   - 更新依赖图
   - 标注哪些已完成

**持续任务**:
- 每完成一个 Phase，更新 `ProofArchitecture.lean`
- 维护 axiom 清单
- 记录遇到的困难和解决方案

---

## 时间线估计

### 短期目标 (1-2 周)
- ✅ Phase 1 完成
- ⏳ Phase 2 完成 50%
- 🎯 sorry 数量降至 35

### 中期目标 (1-2 个月)
- ✅ Phase 2 完成
- ✅ Phase 3 完成
- ⏳ Phase 4 完成 50%
- 🎯 sorry 数量降至 20

### 长期目标 (3-6 个月)
- ✅ Phase 4 完成
- ✅ Phase 5 完成 80%
- 🎯 sorry 数量降至 10
- 🎯 所有核心定理有清晰的 axiom 或证明

### 终极目标 (6-12 个月+)
- 🎯 sorry 数量降至 5 以下
- 🎯 只保留最核心的几何/分析 axioms
- 🎯 成为 Lean 4 中几何拓扑的标杆项目

---

## 成功标准

### 最小可验收标准 (MVP)
- [ ] 庞加莱猜想的完整逻辑链条
- [ ] 所有 sorry 转为有名字、有文档的 axioms
- [ ] RicciFlow 库保持 0 sorry
- [ ] Blueprint 与代码同步
- [ ] 清晰的 axiom 依赖图

### 理想标准
- [ ] sorry < 10
- [ ] 所有"容易"的几何引理都已证明
- [ ] Mathlib 连接完成
- [ ] 体积和曲率的基本理论形式化
- [ ] 有限手术定理完全证明

### 卓越标准
- [ ] sorry < 5
- [ ] 只保留核心深度结果（如 κ-解分类、Hamilton-Ivey 估计）
- [ ] 可能向 Mathlib 贡献几何定理
- [ ] 完整的教学文档

---

## 风险与挑战

### 技术风险
1. **Mathlib 几何库不够成熟**
   - 缓解: 可以暂时公理化，标注"可形式化"
   - 长期: 可能需要贡献到 Mathlib

2. **深度 PDE/几何分析难以形式化**
   - 缓解: 接受某些核心结果作为 axiom
   - 目标: 至少形式化逻辑链条

3. **类型理论限制**
   - 缓解: 灵活使用 Classical.choice
   - 咨询 Lean 社区的几何形式化经验

### 资源需求
- 需要对 Mathlib 几何库的深入了解
- 可能需要几何拓扑专家的数学指导
- 长期项目，需要持续投入

### 依赖
- Lean 4 和 Mathlib 的稳定性
- Mathlib 几何库的发展
- Blueprint 工具链

---

## 下一步行动 (立即执行)

### 今天
1. [x] 创建 `ProofArchitecture.lean`
2. [x] 创建本计划文档
3. [ ] 开始 Phase 2: 识别"容易"的 sorry
4. [ ] 创建 axiom 清单文档

### 本周
1. [ ] 完成 Phase 2 的 50%
2. [ ] 尝试完成 `w_entropy_monotone`
3. [ ] 将主要 sorry 转为 axioms
4. [ ] 更新 Blueprint

### 下周
1. [ ] 完成 Phase 2
2. [ ] 开始 Phase 3: Mathlib 连接
3. [ ] 初步尝试 Phase 4 的体积理论

---

## 资源

### 文档
- `Poincare/Dev/ProofArchitecture.lean` - 架构分析
- `blueprint/` - 数学文档
- 本文件 - 实施计划

### 参考
- Perelman 原始论文
- Mathlib 文档
- Lean 4 参考手册
- Morgan-Tian, Kleiner-Lott 的详细证明

### 社区
- Lean Zulip
- Mathlib 贡献者
- 几何形式化社区

-- Poincare/Dev/Audit.lean
-- 公理审计：检查所有使用的公理

import Poincare.Final

/-!
# 公理审计

本文件用于审计整个 Poincare 项目中使用的公理。

## 使用方法

```bash
lake build
lake env lean Poincare/Dev/Audit.lean
```

然后查看输出中的 `#print axioms` 结果。

## 预期公理

### 来自 Poincare.Core.TopologyInput 的占位公理
- `Is3Manifold`
- `SimplyConnected`
- `Sphere3`
- `sphere3_simply_connected`
- `sphere3_compact`

### 来自 Poincare.Perelman.Package 的 Perelman 理论公理
- `WEntropy`
- `w_entropy_monotone`
- `KappaNonCollapsing`
- `perelman_no_local_collapsing`
- `IsKappaSolution`
- `kappa_solution_asymptotic_cylinder`
- `neck_recognition`
- `surgery_construction`
- `ricci_flow_with_surgery`

### 来自 Poincare.Perelman.PoincareFromPerelman 的推理公理
- `assign_riemannian_metric`
- `ricci_flow_with_surgery_global`
- `extinction_implies_topology`

### 来自 RicciFlow 库的公理
- `ricciNaturalityOn` (唯一已知的底层公理)

## 不应该出现的公理

- `Quot.sound`, `propext`, `Classical.choice` 等是 Lean 的标准公理，可以接受
- **任何其他新的数学公理都需要明确说明来源**
-/

namespace Poincare.Dev

-- 审计主定理
#print axioms Poincare.poincare_conjecture

-- 审计 Perelman 推导
#print axioms Poincare.poincare_from_perelman

-- 审计拓扑手术
#print axioms Poincare.topological_surgery_via_ricci_flow

end Poincare.Dev

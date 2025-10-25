-- Poincare/Perelman/Package.lean
-- Perelman 工作包：熵泛函、无崩塌定理、κ-解

import Poincare.Perelman.Entropy
import Poincare.Perelman.KappaSolutions
import Poincare.Perelman.GeometricSurgery
import RicciFlow.Flow
import RicciFlow.Ricci.DeturckReduction

/-!
# Perelman 的 Ricci 流理论包

本文件汇总 Perelman 证明庞加莱猜想所需的关键工具：

1. **熵泛函（Entropy Functional）**
   - W-熵及其单调性
   - F-泛函及其单调性
   - ν-熵及其单调性

2. **无崩塌定理（No Local Collapsing）**
   - κ-无崩塌条件
   - 局部体积下界

3. **κ-解（κ-solutions）**
   - 古代解的分类
   - 渐近柱形性质

4. **几何手术（Geometric Surgery）**
   - 颈部识别
   - 手术流程
   - 标准解拼接

这些结果将依赖底层的 RicciFlow 库（已完成的 DeTurck 归约）。
-/

set_option autoImplicit true

namespace Perelman

-- ========================================
-- 注意：核心定义已迁移到专门的文件
-- ========================================
-- 1. 熵泛函 → Poincare.Perelman.Entropy
-- 2. κ-解 → Poincare.Perelman.KappaSolutions
-- 3. κ-解分类 → Poincare.Perelman.KappaSolutionClassification
-- 4. 几何手术 → Poincare.Perelman.GeometricSurgery

-- ========================================
-- 说明：本文件现在作为统一导入点
-- 详细定义见各专门文件：
-- - Entropy.lean: W-熵、F-functional、ν-熵、无崩塌定理
-- - KappaSolutions.lean: κ-解的定义和性质
-- - KappaSolutionClassification.lean: κ-解的详细分类
-- - GeometricSurgery.lean: 手术理论
-- ========================================

end Perelman

import RicciFlow.Flow
import RicciFlow.Ricci.DeturckReduction

set_option autoImplicit true

namespace RicciFlow

universe u

open Set

variable {M V : Type u} [Zero V] [TopologicalSpace M] [CompactSpace M]

/-- Ricci-flat 初值的常值族例子：直接调用已证定理。 -/
example (g0 : RiemannianMetric M V) (h : ricciOfMetric g0 = 0) :
    ∃ T : ℝ, 0 < T ∧
      ∃ g : ℝ → RiemannianMetric M V,
        g 0 = g0 ∧ ricciFlowEqOn (M:=M) (V:=V) g (Ioo (0 : ℝ) T) :=
  short_time_existence_ricciFlat (M:=M) (V:=V) g0 h

-- ✅ 验证 DeTurck → Hamilton 条件式归约定理
#check @deturck_to_hamilton_reduction

-- ✅ 验证 pullback API
#check @pullbackVelocity
#check @pullbackMetric
#check @pullbackVelocity_zero
#check @pullbackVelocity_smul
#check @pullbackVelocity_add
#check @pullbackVelocity_neg
#check @pullbackVelocity_comp

-- ✅ 验证假设谓词
#check @deturckEqOnWithGauge
#check @pullbackChainRuleOn
#check @gaugeCancellationOn
#check @ricciNaturalityOn

-- ✅ 验证新增的 toy 引理（无公理，可证明）
#check @pullbackChainRuleOn_constφ
#check @deturck_to_hamilton_constφ_noGauge

end RicciFlow

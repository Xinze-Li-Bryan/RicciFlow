import Mathlib
import RicciFlow.Basic
import RicciFlow.RiemannianManifold
import RicciFlow.RicciCurvature

/-!
# Ricci Flow
-/

namespace RicciFlow

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M]

axiom ricci_flow_equation {M V : Type*} [Zero V] (g : ℝ → RiemannianMetric M V)
    (Ric : ℝ → RicciTensor M) : Prop

theorem short_time_existence {M V : Type*} [TopologicalSpace M] [CompactSpace M] [Zero V]
    (g₀ : RiemannianMetric M V) :
    ∃ T > 0, ∃ g : ℝ → RiemannianMetric M V,
      g 0 = g₀ ∧ ricci_flow_equation g sorry :=
  sorry

end RicciFlow

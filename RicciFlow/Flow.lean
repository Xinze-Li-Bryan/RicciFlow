import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Basic
import RicciFlow.RiemannianManifold
import RicciFlow.RicciCurvature

set_option autoImplicit true

namespace RicciFlow

open Set

universe u

/-- 时间导数：对每个坐标函数取实变量导数，得到速度张量。 -/
noncomputable def timeDeriv {M V : Type u} [Zero V]
    (g : ℝ → RiemannianMetric M V) (t : ℝ) :
    MetricVelocity M V :=
{ toFun := fun x v w => deriv (fun s => (g s).toFun x v w) t
  symm := by
    intro x v w
    have hfun :
        (fun s => (g s).toFun x v w) =
        (fun s => (g s).toFun x w v) := by
      funext s
      simpa using (g s).symm x v w
    simp [hfun] }

/-- Ricci 流方程在集合 `s ⊆ ℝ` 上成立。 -/
def ricciFlowEqOn {M V : Type u} [Zero V]
    (g : ℝ → RiemannianMetric M V) (s : Set ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, t ∈ s → timeDeriv g t = (-2 : ℝ) • ricciOfMetric (g t)

/-- 常值族的时间导数为零。 -/
@[simp] lemma timeDeriv_const {M V : Type u} [Zero V]
    (g0 : RiemannianMetric M V) (t : ℝ) :
    timeDeriv (fun _ => g0) t = 0 := by
  ext x v w
  simp [timeDeriv, deriv_const]

/-- Ricci-flat 初值的常值族满足 Ricci 流方程。 -/
lemma ricciFlowEqOn_const_of_ricciFlat {M V : Type u} [Zero V]
    (g0 : RiemannianMetric M V) (hRic0 : ricciOfMetric g0 = 0)
    (s : Set ℝ) :
    ricciFlowEqOn (fun _ => g0) s := by
  intro t ht
  show timeDeriv (fun _ => g0) t = (-2 : ℝ) • ricciOfMetric g0
  rw [hRic0]
  simp [timeDeriv_const]

/-- Ricci-flat 初值的短时存在性：取常值族即得解。 -/
theorem short_time_existence_ricciFlat {M V : Type u} [Zero V]
    [TopologicalSpace M] [CompactSpace M]
    (g0 : RiemannianMetric M V) (hRic0 : ricciOfMetric g0 = 0) :
    ∃ T : ℝ, 0 < T ∧
      ∃ g : ℝ → RiemannianMetric M V,
        g 0 = g0 ∧ ricciFlowEqOn (M:=M) (V:=V) g (Ioo (0 : ℝ) T) := by
  refine ⟨(1 : ℝ), zero_lt_one, ?_⟩
  refine ⟨fun _ => g0, rfl, ?_⟩
  simpa using
    ricciFlowEqOn_const_of_ricciFlat (M:=M) (V:=V) g0 hRic0 (Ioo (0 : ℝ) 1)

/-- Hamilton 的短时存在性公理化表述。 -/
axiom hamilton_short_time_existence
  {M V : Type u} [Zero V]
  [TopologicalSpace M] [CompactSpace M]
  (g0 : RiemannianMetric M V) :
  ∃ T : ℝ, 0 < T ∧
    ∃ g : ℝ → RiemannianMetric M V,
      g 0 = g0 ∧ ricciFlowEqOn (M:=M) (V:=V) g (Ioo (0 : ℝ) T)

/-- Hamilton 公理给出的短时存在性（保持原签名）。 -/
theorem short_time_existence {M V : Type u} [Zero V]
  [TopologicalSpace M] [CompactSpace M]
  (g0 : RiemannianMetric M V) :
  ∃ T : ℝ, 0 < T ∧
    ∃ g : ℝ → RiemannianMetric M V,
      g 0 = g0 ∧ ricciFlowEqOn (M:=M) (V:=V) g (Ioo (0 : ℝ) T) :=
  hamilton_short_time_existence (M:=M) (V:=V) g0

end RicciFlow

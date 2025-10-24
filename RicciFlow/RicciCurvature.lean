import Mathlib.Data.Real.Basic
import RicciFlow.RiemannianManifold

set_option autoImplicit true

namespace RicciFlow

universe u

/-- 速度层：抽象的对称 (0,2)-张量，用来承载时间导数与 Ricci(g)。 -/
structure MetricVelocity (M V : Type u) where
  toFun : M → V → V → ℝ
  symm : ∀ x v w, toFun x v w = toFun x w v

namespace MetricVelocity

@[ext] theorem ext
    {M V : Type u} {τ₁ τ₂ : MetricVelocity M V}
    (h : ∀ x v w, τ₁.toFun x v w = τ₂.toFun x v w) : τ₁ = τ₂ := by
  cases τ₁
  cases τ₂
  congr
  funext x v w
  exact h x v w

end MetricVelocity

/-- 速度的标量乘法。对称性自动保留。 -/
instance instSMulMetricVelocity {M V : Type u} : SMul ℝ (MetricVelocity M V) where
  smul c τ :=
  { toFun := fun x v w => c * τ.toFun x v w
    symm := by
      intro x v w
      simp [τ.symm x v w] }

/-- 零速度张量。 -/
instance instZeroMetricVelocity {M V : Type u} : Zero (MetricVelocity M V) where
  zero :=
  { toFun := fun _ _ _ => 0
    symm := by
      intro x v w
      simp }

@[simp] lemma MetricVelocity.toFun_zero {M V : Type u}
    (x : M) (v w : V) :
    (0 : MetricVelocity M V).toFun x v w = 0 := rfl

@[simp] lemma MetricVelocity.smul_zero {M V : Type u}
    (c : ℝ) :
    c • (0 : MetricVelocity M V) = 0 := by
  ext x v w
  change c * (0 : MetricVelocity M V).toFun x v w = 0
  simp [MetricVelocity.toFun_zero]

/-- 加法：点态相加。 -/
instance instAddMetricVelocity {M V : Type u} : Add (MetricVelocity M V) where
  add τ σ :=
  { toFun := fun x v w => τ.toFun x v w + σ.toFun x v w
    symm  := by
      intro x v w
      simp [τ.symm x v w, σ.symm x v w] }

/-- 相反元：点态取负。 -/
instance instNegMetricVelocity {M V : Type u} : Neg (MetricVelocity M V) where
  neg τ :=
  { toFun := fun x v w => - τ.toFun x v w
    symm  := by
      intro x v w
      simp [τ.symm x v w] }

@[simp] lemma mv_toFun_add {M V : Type u} (τ σ : MetricVelocity M V) (x : M) (v w : V) :
  (τ + σ).toFun x v w = τ.toFun x v w + σ.toFun x v w := rfl

@[simp] lemma mv_toFun_neg {M V : Type u} (τ : MetricVelocity M V) (x : M) (v w : V) :
  (-τ).toFun x v w = - τ.toFun x v w := rfl

lemma smul_toFun {M V : Type u} (c : ℝ) (τ : MetricVelocity M V) (x : M) (v w : V) :
  (c • τ).toFun x v w = c * τ.toFun x v w := rfl

/-- 从度量产生 Ricci 速度的运算子：Ric(g)。 -/
axiom ricciOfMetric {M V : Type u} [Zero V] (g : RiemannianMetric M V) :
  MetricVelocity M V

/-- 极简版 RicciTensor，仅用于保持兼容；PDE 接口不依赖它。 -/
structure RicciTensor (M : Type u) where
  traceValue : ℝ

def scalarCurvature (Ric : RicciTensor M) : ℝ := Ric.traceValue

@[simp] theorem scalarCurvature_eq_traceValue (Ric : RicciTensor M) :
    scalarCurvature Ric = Ric.traceValue := rfl

end RicciFlow

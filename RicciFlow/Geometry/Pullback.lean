-- Geometry/Pullback.lean
import RicciFlow.RiemannianManifold
import RicciFlow.RicciCurvature

set_option autoImplicit true

namespace RicciFlow
universe u
variable {M V : Type u} [Zero V]

-- 对速度（对称(0,2)-张量）做 pullback：仅重标底点
def pullbackVelocity (φ : M → M) (τ : MetricVelocity M V) : MetricVelocity M V :=
{ toFun := fun x v w => τ.toFun (φ x) v w
  symm  := by intro x v w; simp [τ.symm (φ x) v w] }

-- 对度量做 pullback：同样重标底点（正定性沿 φ 传递）
def pullbackMetric (φ : M → M) (g : RiemannianMetric M V) : RiemannianMetric M V :=
{ toFun := fun x v w => g.toFun (φ x) v w
  symm  := by intro x v w; exact (g.symm (φ x) v w)
  pos_def := by
    intro x v hv
    -- 直接复用 g 在 φ x 处的正定性
    exact (g.pos_def (φ x) v hv) }

-- 线性性（后续归约定理中会使用）
omit [Zero V] in
@[simp] lemma pullbackVelocity_zero (φ : M → M) :
  pullbackVelocity φ (0 : MetricVelocity M V) = 0 := by
  ext x v w; simp [pullbackVelocity, MetricVelocity.toFun_zero]

omit [Zero V] in
@[simp] lemma pullbackVelocity_smul (φ : M → M) (c : ℝ) (τ : MetricVelocity M V) :
  pullbackVelocity φ (c • τ) = c • pullbackVelocity φ τ := by
  ext x v w; simp [pullbackVelocity, smul_toFun]

omit [Zero V] in
@[simp] lemma pullbackVelocity_add (φ : M → M) (τ σ : MetricVelocity M V) :
  pullbackVelocity φ (τ + σ) = pullbackVelocity φ τ + pullbackVelocity φ σ := by
  ext x v w; simp [pullbackVelocity, mv_toFun_add]

omit [Zero V] in
@[simp] lemma pullbackVelocity_neg (φ : M → M) (τ : MetricVelocity M V) :
  pullbackVelocity φ (-τ) = - pullbackVelocity φ τ := by
  ext x v w; simp [pullbackVelocity, mv_toFun_neg]

-- 函子性（合成与恒等）
omit [Zero V] in
@[simp] lemma pullbackVelocity_id (τ : MetricVelocity M V) :
  pullbackVelocity (fun x : M => x) τ = τ := by
  ext x v w; simp [pullbackVelocity]

omit [Zero V] in
@[simp] lemma pullbackVelocity_comp (φ ψ : M → M) (τ : MetricVelocity M V) :
  pullbackVelocity (fun x => φ (ψ x)) τ =
  pullbackVelocity ψ (pullbackVelocity φ τ) := by
  ext x v w; simp [pullbackVelocity]

@[simp] lemma pullbackMetric_id (g : RiemannianMetric M V) :
  pullbackMetric (fun x : M => x) g = g := by
  -- 等式按字段证明
  cases g with
  | mk toFun symm pos =>
    rfl

@[simp] lemma pullbackMetric_comp (φ ψ : M → M) (g : RiemannianMetric M V) :
  pullbackMetric (fun x => φ (ψ x)) g =
  pullbackMetric ψ (pullbackMetric φ g) := by
  -- 逐字段展开
  cases g with
  | mk toFun symm pos =>
    rfl

end RicciFlow

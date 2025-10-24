-- Ricci/DeturckReduction.lean
import RicciFlow.Flow
import RicciFlow.Geometry.Pullback
import RicciFlow.RicciCurvature

set_option autoImplicit true

namespace RicciFlow
open Set
universe u
variable {M V : Type u} [Zero V]

-- 记号：拉回的"φ 部分"的时间导数（g 固定）
noncomputable def dPullback_dt (φ : ℝ → M → M) (g : ℝ → RiemannianMetric M V) (t : ℝ) :
  MetricVelocity M V :=
  timeDeriv (fun τ => pullbackMetric (φ τ) (g t)) t

-- DeTurck（带规范项）的方程：把"规范驱动"抽象为一个时间依赖速度场 G
def deturckEqOnWithGauge
  (g : ℝ → RiemannianMetric M V)
  (G : ℝ → MetricVelocity M V)
  (s : Set ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, t ∈ s →
    timeDeriv g t = (-2 : ℝ) • ricciOfMetric (g t) + G t

-- 链式法则（条件）：拉回复合的时间导数可以分解为两项
def pullbackChainRuleOn
  (φ : ℝ → M → M)
  (g  : ℝ → RiemannianMetric M V)
  (s  : Set ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, t ∈ s →
    timeDeriv (fun τ => pullbackMetric (φ τ) (g τ)) t
      = pullbackVelocity (φ t) (timeDeriv g t) + dPullback_dt φ g t

-- 规范抵消（条件）：选择 φ 使得"φ 的导数项"恰好抵消规范项的拉回
def gaugeCancellationOn
  (φ : ℝ → M → M)
  (g  : ℝ → RiemannianMetric M V)
  (G  : ℝ → MetricVelocity M V)
  (s  : Set ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, t ∈ s →
    dPullback_dt φ g t = - pullbackVelocity (φ t) (G t)

-- 自然性（条件）：Ricci 与拉回交换（几何自然性）
def ricciNaturalityOn
  (φ : ℝ → M → M)
  (g  : ℝ → RiemannianMetric M V)
  (s  : Set ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, t ∈ s →
    ricciOfMetric (pullbackMetric (φ t) (g t))
      = pullbackVelocity (φ t) (ricciOfMetric (g t))

/-- **DeTurck → Hamilton 条件式归约定理**。
    若在集合 `s` 上满足：
      1) `g` 满足带规范项的 DeTurck 方程；
      2) 复合拉回的时间导数满足链式法则分解；
      3) 选取的 `φ` 使"φ 的导数项"与规范项拉回相互抵消；
      4) Ricci 的自然性（与拉回交换）；
    则 `ĝ(t) := φ(t)^* g(t)` 在 `s` 上满足 Hamilton 的 Ricci 流方程。
-/
theorem deturck_to_hamilton_reduction
  (φ : ℝ → M → M)
  (g : ℝ → RiemannianMetric M V)
  (G : ℝ → MetricVelocity M V)
  (s : Set ℝ)
  (Hg      : deturckEqOnWithGauge g G s)
  (Hchain  : pullbackChainRuleOn φ g s)
  (Hcancel : gaugeCancellationOn φ g G s)
  (Hnat    : ricciNaturalityOn φ g s)
  :
  ricciFlowEqOn (fun t => pullbackMetric (φ t) (g t)) s := by
  intro t ht
  -- 1) 链式法则分解
  have hchain := Hchain ht
  -- 2) 代入 DeTurck 方程
  have hdet := Hg ht
  -- 3) 规范抵消项
  have hcancel := Hcancel ht
  -- 4) Ricci 自然性
  have hnat := Hnat ht
  -- 逐步代换：
  -- timeDeriv (φ_t^* g(t)) = φ_t^*( timeDeriv g(t) ) + d/dt|φ 部分
  --                        = φ_t^*( -2 Ric(g(t)) + G(t) ) + dPB
  --                        = -2 φ_t^*(Ric(g(t))) + φ_t^*(G(t)) + dPB
  --                        = -2 Ric(φ_t^* g(t))                    （用自然性 + 下行两项抵消）
  --                        = -2 Ric(ĝ(t))
  have step1 : timeDeriv (fun τ => pullbackMetric (φ τ) (g τ)) t
      = pullbackVelocity (φ t) (timeDeriv g t) + dPullback_dt φ g t := hchain
  -- 用 deturck 方程改写 timeDeriv g t
  have step2 : timeDeriv (fun τ => pullbackMetric (φ τ) (g τ)) t
      = pullbackVelocity (φ t) ((-2 : ℝ) • ricciOfMetric (g t) + G t) + dPullback_dt φ g t := by
    rw [step1, hdet]
  -- 展开 φ_t^* 的线性性
  have step3 : timeDeriv (fun τ => pullbackMetric (φ τ) (g τ)) t
      = (-2 : ℝ) • pullbackVelocity (φ t) (ricciOfMetric (g t))
        + pullbackVelocity (φ t) (G t) + dPullback_dt φ g t := by
    calc timeDeriv (fun τ => pullbackMetric (φ τ) (g τ)) t
        = pullbackVelocity (φ t) ((-2 : ℝ) • ricciOfMetric (g t) + G t) + dPullback_dt φ g t := step2
      _ = pullbackVelocity (φ t) ((-2 : ℝ) • ricciOfMetric (g t)) + pullbackVelocity (φ t) (G t) + dPullback_dt φ g t := by
          rw [pullbackVelocity_add]
      _ = (-2 : ℝ) • pullbackVelocity (φ t) (ricciOfMetric (g t))
          + pullbackVelocity (φ t) (G t) + dPullback_dt φ g t := by
          rw [pullbackVelocity_smul]
  -- 把 dPullback_dt 用规范抵消替换
  have step4 : timeDeriv (fun τ => pullbackMetric (φ τ) (g τ)) t
      = (-2 : ℝ) • pullbackVelocity (φ t) (ricciOfMetric (g t)) := by
    rw [step3, hcancel]
    -- 目标: -2 • ... + pb(G) + (-pb(G)) = -2 • ...
    ext x v w
    simp [mv_toFun_add, mv_toFun_neg, smul_toFun]
  -- 用自然性把 φ_t^*(Ric(g(t))) 变为 Ric(φ_t^* g(t))
  -- 目标：= (-2) • ricciOfMetric (pullbackMetric (φ t) (g t))
  rw [step4, ← hnat]

/-- **Trivial case**: Identity map satisfies chain rule.
    When φ = id, pullback is identity, so chain rule becomes: ∂ₜg = ∂ₜg + 0. -/
lemma pullbackChainRuleOn_id (g : ℝ → RiemannianMetric M V) (s : Set ℝ) :
  pullbackChainRuleOn (fun _ => id) g s := by
  intro t ht
  unfold dPullback_dt
  ext x v w
  simp [timeDeriv, pullbackMetric, pullbackVelocity, mv_toFun_add, deriv_const]

/-- **Toy lemma**: Chain rule holds for constant diffeomorphism.
    When φ is constant in time, dPullback_dt = 0, so the chain rule simplifies. -/
lemma pullbackChainRuleOn_constφ
  (φ0 : M → M) (g : ℝ → RiemannianMetric M V) (s : Set ℝ) :
  pullbackChainRuleOn (fun _ => φ0) g s := by
  intro t ht
  -- Goal: timeDeriv (fun τ => pullbackMetric φ0 (g τ)) t
  --     = pullbackVelocity φ0 (timeDeriv g t) + dPullback_dt (fun _ => φ0) g t
  -- Since φ is constant, dPullback_dt = 0
  have h_dpb : dPullback_dt (fun _ => φ0) g t = 0 := by
    unfold dPullback_dt
    -- timeDeriv (fun τ => pullbackMetric φ0 (g t)) t = 0 because g t is constant in τ
    ext x v w
    simp [timeDeriv, pullbackMetric, deriv_const]
  -- Now show the chain rule: LHS = pullbackVelocity φ0 (timeDeriv g t) + 0
  ext x v w
  simp [timeDeriv, pullbackMetric, pullbackVelocity, h_dpb, mv_toFun_add, MetricVelocity.toFun_zero]

/-- **Trivial case**: Identity map satisfies Ricci naturality.
    When φ is the identity, pullback does nothing, so Ricci commutes trivially. -/
lemma ricciNaturalityOn_id (g : ℝ → RiemannianMetric M V) (s : Set ℝ) :
  ricciNaturalityOn (fun _ => id) g s := by
  intro t ht
  rfl

/-- **Trivial case**: Constant φ with zero gauge satisfies gauge cancellation.
    When φ is constant, dPullback_dt = 0, and with zero gauge, -φ*(0) = 0. -/
lemma gaugeCancellationOn_zero_constφ
  (φ0 : M → M) (g : ℝ → RiemannianMetric M V) (s : Set ℝ) :
  gaugeCancellationOn (fun _ => φ0) g (fun _ => 0) s := by
  intro t ht
  unfold dPullback_dt
  ext x v w
  simp [timeDeriv, pullbackMetric, pullbackVelocity, deriv_const,
        mv_toFun_neg, MetricVelocity.toFun_zero]

/-- **Trivial case**: Identity map with zero gauge satisfies gauge cancellation.
    When φ = id and G = 0, both sides are zero: 0 = -id*(0) = 0. -/
lemma gaugeCancellationOn_id_zero (g : ℝ → RiemannianMetric M V) (s : Set ℝ) :
  gaugeCancellationOn (fun _ => id) g (fun _ => 0) s := by
  intro t ht
  unfold dPullback_dt
  ext x v w
  simp [timeDeriv, pullbackMetric, pullbackVelocity, deriv_const,
        mv_toFun_neg, MetricVelocity.toFun_zero]

/-- **Sanity lemma**: Ricci-flat metric trivially satisfies DeTurck with zero gauge.
    If Ric(g) = 0, then ∂g/∂t = -2·Ric(g) + 0 reduces to ∂g/∂t = 0. -/
lemma deturckEqOnWithGauge_ricciFlat_static
  (g0 : RiemannianMetric M V) (h : ricciOfMetric g0 = 0) (s : Set ℝ) :
  deturckEqOnWithGauge (fun _ => g0) (fun _ => 0) s := by
  intro t ht
  unfold timeDeriv
  ext x v w
  simp [deriv_const, h, MetricVelocity.toFun_zero, mv_toFun_add]

/-- **Sanity corollary**: With constant φ and zero gauge, DeTurck reduces to Hamilton.
    This demonstrates the reduction mechanism in a controlled, provable setting. -/
lemma deturck_to_hamilton_constφ_noGauge
  (φ0 : M → M) (g : ℝ → RiemannianMetric M V) (s : Set ℝ)
  (Hg : deturckEqOnWithGauge g (fun _ => 0) s)
  (Hnat : ricciNaturalityOn (fun _ => φ0) g s) :
  ricciFlowEqOn (fun t => pullbackMetric φ0 (g t)) s := by
  apply deturck_to_hamilton_reduction (φ:=fun _ => φ0) (g:=g) (G:=fun _ => 0) (s:=s)
  · -- DeTurck equation with G=0
    exact Hg
  · -- Chain rule for constant φ
    exact pullbackChainRuleOn_constφ φ0 g s
  · -- Gauge cancellation: dPullback_dt = -pullbackVelocity φ0 0 = 0
    intro t ht
    unfold dPullback_dt
    ext x v w
    simp [timeDeriv, pullbackMetric, pullbackVelocity, deriv_const, mv_toFun_neg, MetricVelocity.toFun_zero]
  · -- Ricci naturality
    exact Hnat

/-- **Complete trivial example**: Identity map on static Ricci-flat metric.
    This is the most trivial case combining all simple predicates. -/
lemma deturck_to_hamilton_id_ricciFlat
  (g0 : RiemannianMetric M V) (h : ricciOfMetric g0 = 0) (s : Set ℝ) :
  ricciFlowEqOn (fun _ => g0) s := by
  have hg : ricciFlowEqOn (fun t => pullbackMetric id g0) s := by
    apply deturck_to_hamilton_reduction (φ:=fun _ => id) (g:=fun _ => g0) (G:=fun _ => 0) (s:=s)
    · exact deturckEqOnWithGauge_ricciFlat_static g0 h s
    · exact pullbackChainRuleOn_id (fun _ => g0) s
    · exact gaugeCancellationOn_id_zero (fun _ => g0) s
    · exact ricciNaturalityOn_id (fun _ => g0) s
  simpa using hg

end RicciFlow

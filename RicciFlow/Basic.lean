import Mathlib

/-!
# Ricci Flow 基础定义

本文件包含 Ricci Flow 形式化所需的基础引理和辅助定理。
-/

namespace RicciFlow

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M]

/-!
## 实数的基本性质

这些引理在处理度量张量的正定性和标量曲率计算时会用到。
-/

/-- 两个正实数的乘积仍然是正数。
这在验证度量张量的正定性时是基础性质。 -/
lemma pos_mul_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  exact mul_pos ha hb

/-- 任何非零实数的平方严格大于零。
这是度量正定性的核心性质：对于非零向量 v，⟨v, v⟩ > 0。 -/
lemma square_pos_of_ne_zero {x : ℝ} (hx : x ≠ 0) : 0 < x ^ 2 := by
  exact sq_pos_of_ne_zero hx

/-- 构造性地给出一个正实数。
在 short_time_existence 定理中，我们需要证明存在 T > 0。 -/
lemma exists_pos_real : ∃ (t : ℝ), 0 < t := by
  use 1
  norm_num

/-- 正数的倒数仍然是正数。
这在处理度量张量的逆和计算标量曲率时会用到。 -/
lemma inv_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < x⁻¹ := by
  exact inv_pos.mpr hx

/-!
## 拓扑空间的基本性质

这些引理为流形上的连续性和光滑性理论提供基础。
-/

/-- 函数在一点连续，当且仅当它在该点的某个邻域内的限制是连续的。
这个性质在局部坐标系中处理光滑函数时非常有用。 -/
lemma continuousAt_iff_continuousWithinAt {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} {x : X} :
    ContinuousAt f x ↔ ContinuousWithinAt f Set.univ x := by
  rw [continuousWithinAt_univ]

end RicciFlow

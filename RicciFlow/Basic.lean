import Mathlib

/-!
# Basic Definitions for Ricci Flow

This file contains fundamental lemmas and auxiliary theorems required for the
formalization of Ricci Flow.
-/

namespace RicciFlow

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M]

/-!
## Basic Properties of Real Numbers

These lemmas are used when dealing with positive-definiteness of metric tensors
and scalar curvature computations.
-/

/-- The product of two positive real numbers is positive.
This is a fundamental property when verifying positive-definiteness of metric tensors. -/
lemma pos_mul_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  exact mul_pos ha hb

/-- The square of any nonzero real number is strictly positive.
This is a core property of metric positive-definiteness: for nonzero vector v, ⟨v, v⟩ > 0. -/
lemma square_pos_of_ne_zero {x : ℝ} (hx : x ≠ 0) : 0 < x ^ 2 := by
  exact sq_pos_of_ne_zero hx

/-- Constructively provide a positive real number.
In the short_time_existence theorem, we need to prove there exists T > 0. -/
lemma exists_pos_real : ∃ (t : ℝ), 0 < t := by
  use 1
  norm_num

/-- The reciprocal of a positive number is positive.
This is used when dealing with inverse metric tensors and computing scalar curvature. -/
lemma inv_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < x⁻¹ := by
  exact inv_pos.mpr hx

/-!
## Basic Properties of Topological Spaces

These lemmas provide the foundation for continuity and smoothness theory on manifolds.
-/

/-- A function is continuous at a point if and only if its restriction to a
neighborhood of that point is continuous.
This property is very useful when working with smooth functions in local coordinate systems. -/
lemma continuousAt_iff_continuousWithinAt {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} {x : X} :
    ContinuousAt f x ↔ ContinuousWithinAt f Set.univ x := by
  rw [continuousWithinAt_univ]

end RicciFlow

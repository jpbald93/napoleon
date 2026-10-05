import Mathlib

/-!
# Napoleon's theorem (complex-coordinate proof)

The Euclidean plane is modelled as `ℂ`. On each side of the triangle `A B C` we erect an
equilateral triangle by rotating the side vector by `-π/3` (multiplication by `ωo`).
If `A B C` is positively oriented these triangles point outward (`apex_outward`).
The three centroids form an equilateral triangle (`napoleon_outer`); the same holds for
the inward triangles (`napoleon_inner`), and in fact for any unit `ω` with `ω²-ω+1=0`.
-/

namespace Napoleon

open Complex

/-- Rotation by `-π/3`: `ωo = 1/2 - (√3/2) i`. -/
noncomputable def ωo : ℂ := ⟨1 / 2, -(Real.sqrt 3 / 2)⟩

/-- Rotation by `+π/3`: `ωi = 1/2 + (√3/2) i`. -/
noncomputable def ωi : ℂ := ⟨1 / 2, Real.sqrt 3 / 2⟩

/-- Centroid of three points. -/
noncomputable def centroid (P Q R : ℂ) : ℂ := (P + Q + R) / 3

/-- Third vertex of the equilateral triangle on the side `P Q`, obtained by rotating
`Q - P` about `P` with the rotation `ω`. -/
def apex (ω P Q : ℂ) : ℂ := P + ω * (Q - P)

/-- Signed area of the triangle `P Q R` (positive iff counter-clockwise). -/
noncomputable def signedArea (P Q R : ℂ) : ℝ := ((starRingEnd ℂ) (Q - P) * (R - P)).im / 2

/-- Napoleon point on side `B C`, `C A`, `A B` respectively. -/
noncomputable def Ga (ω _A B C : ℂ) : ℂ := centroid B C (apex ω B C)
noncomputable def Gb (ω A _B C : ℂ) : ℂ := centroid C A (apex ω C A)
noncomputable def Gc (ω A B _C : ℂ) : ℂ := centroid A B (apex ω A B)

lemma sqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

lemma norm_eq_one_of_normSq {z : ℂ} (h : normSq z = 1) : ‖z‖ = 1 := by
  have h1 : ‖z‖ ^ 2 = 1 := by rw [Complex.sq_norm, h]
  have h2 : 0 ≤ ‖z‖ := norm_nonneg z
  nlinarith

lemma ωo_poly : ωo ^ 2 - ωo + 1 = 0 := by
  apply Complex.ext <;> simp [ωo, sq] <;> nlinarith [sqrt3_sq]

lemma ωi_poly : ωi ^ 2 - ωi + 1 = 0 := by
  apply Complex.ext <;> simp [ωi, sq] <;> nlinarith [sqrt3_sq]

lemma norm_ωo : ‖ωo‖ = 1 := by
  apply norm_eq_one_of_normSq; simp [ωo, normSq_apply]; nlinarith [sqrt3_sq]

lemma norm_ωi : ‖ωi‖ = 1 := by
  apply norm_eq_one_of_normSq; simp [ωi, normSq_apply]; nlinarith [sqrt3_sq]

lemma norm_one_sub_ωo : ‖1 - ωo‖ = 1 := by
  apply norm_eq_one_of_normSq; simp [ωo, normSq_apply]; nlinarith [sqrt3_sq]

lemma norm_one_sub_ωi : ‖1 - ωi‖ = 1 := by
  apply norm_eq_one_of_normSq; simp [ωi, normSq_apply]; nlinarith [sqrt3_sq]

/-- The erected triangle `P Q (apex ω P Q)` is equilateral whenever `‖ω‖ = 1 = ‖1-ω‖`. -/
theorem apex_equilateral {ω : ℂ} (h1 : ‖ω‖ = 1) (h2 : ‖1 - ω‖ = 1) (P Q : ℂ) :
    dist P Q = dist P (apex ω P Q) ∧ dist P Q = dist Q (apex ω P Q) := by
  simp only [dist_eq_norm, apex]
  constructor
  · rw [show P - (P + ω * (Q - P)) = -(ω * (Q - P)) by ring, norm_neg, norm_mul, h1, one_mul,
      ← norm_neg, neg_sub]
  · rw [show Q - (P + ω * (Q - P)) = (1 - ω) * (Q - P) by ring, norm_mul, h2, one_mul,
      ← norm_neg, neg_sub]

/-- Key algebraic identity: `Gb - Ga = ω (Gc - Ga)`. -/
lemma key {ω : ℂ} (h : ω ^ 2 - ω + 1 = 0) (A B C : ℂ) :
    Gb ω A B C - Ga ω A B C = ω * (Gc ω A B C - Ga ω A B C) := by
  simp only [Ga, Gb, Gc, centroid, apex]
  linear_combination (A - 2 * B + C) / 3 * h

/-- General Napoleon theorem for any rotation `ω` with `ω² - ω + 1 = 0` and
`‖ω‖ = ‖1 - ω‖ = 1` (i.e. `ω = e^{±iπ/3}`). No non-degeneracy is needed. -/
theorem napoleon_general {ω : ℂ} (h : ω ^ 2 - ω + 1 = 0) (h1 : ‖ω‖ = 1) (h2 : ‖1 - ω‖ = 1)
    (A B C : ℂ) :
    dist (Ga ω A B C) (Gb ω A B C) = dist (Gb ω A B C) (Gc ω A B C) ∧
    dist (Gb ω A B C) (Gc ω A B C) = dist (Gc ω A B C) (Ga ω A B C) := by
  have hk := key h A B C
  have e1 : dist (Ga ω A B C) (Gb ω A B C) = ‖Gc ω A B C - Ga ω A B C‖ := by
    rw [dist_comm, dist_eq_norm, hk, norm_mul, h1, one_mul]
  have e2 : dist (Gb ω A B C) (Gc ω A B C) = ‖Gc ω A B C - Ga ω A B C‖ := by
    rw [dist_comm, dist_eq_norm,
      show Gc ω A B C - Gb ω A B C = (1 - ω) * (Gc ω A B C - Ga ω A B C) by
        linear_combination (-1 : ℂ) * hk,
      norm_mul, h2, one_mul]
  have e3 : dist (Gc ω A B C) (Ga ω A B C) = ‖Gc ω A B C - Ga ω A B C‖ := dist_eq_norm _ _
  exact ⟨e1.trans e2.symm, e2.trans e3.symm⟩

/-- **Napoleon's theorem** (outer): the centres of the equilateral triangles erected
(outward, see `apex_outward`) on the sides of `A B C` form an equilateral triangle. -/
theorem napoleon_outer (A B C : ℂ) :
    dist (Ga ωo A B C) (Gb ωo A B C) = dist (Gb ωo A B C) (Gc ωo A B C) ∧
    dist (Gb ωo A B C) (Gc ωo A B C) = dist (Gc ωo A B C) (Ga ωo A B C) :=
  napoleon_general ωo_poly norm_ωo norm_one_sub_ωo A B C

/-- **Napoleon's theorem** (inner): same with the triangles erected inward. -/
theorem napoleon_inner (A B C : ℂ) :
    dist (Ga ωi A B C) (Gb ωi A B C) = dist (Gb ωi A B C) (Gc ωi A B C) ∧
    dist (Gb ωi A B C) (Gc ωi A B C) = dist (Gc ωi A B C) (Ga ωi A B C) :=
  napoleon_general ωi_poly norm_ωi norm_one_sub_ωi A B C

/-- Orientation of the erected triangle: `P Q (apex ωo P Q)` is clockwise, with signed area
`-(√3/4)‖Q-P‖²`. Hence if `A B C` is counter-clockwise (`0 < signedArea A B C`), each apex
lies on the opposite side of its base from the third vertex, i.e. the triangles are outward. -/
theorem apex_outward (P Q : ℂ) :
    signedArea P Q (apex ωo P Q) = -(Real.sqrt 3 / 4) * normSq (Q - P) := by
  simp only [signedArea, apex, ωo, add_sub_cancel_left, normSq_apply]
  simp [Complex.mul_im, Complex.mul_re]
  ring

/-- Non-vacuity: a concrete non-degenerate, counter-clockwise triangle. -/
example : 0 < signedArea 0 1 Complex.I ∧
    dist (Ga ωo 0 1 Complex.I) (Gb ωo 0 1 Complex.I) =
      dist (Gb ωo 0 1 Complex.I) (Gc ωo 0 1 Complex.I) ∧
    dist (Ga ωo 0 1 Complex.I) (Gb ωo 0 1 Complex.I) ≠ 0 := by
  refine ⟨by norm_num [signedArea], (napoleon_outer 0 1 Complex.I).1, ?_⟩
  rw [dist_ne_zero]
  intro h
  have := congrArg Complex.re h
  simp [Ga, Gb, centroid, apex, ωo] at this
  nlinarith [sqrt3_sq, Real.sqrt_nonneg 3]

end Napoleon

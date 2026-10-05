import Napoleon.Basic

/-!
# Definition bridges

The local definitions of `Napoleon.Basic`, tied to the standard Mathlib notions:

* `ωo_eq_exp`, `ωi_eq_exp` : `ωo = exp(-iπ/3)`, `ωi = exp(iπ/3)`;
* `apex_eq_rotation` : `apex ω P Q` is `Q` rotated about `P` by the unit complex `ω`
  (`rotation`, Mathlib's rotation of `ℂ` as a linear isometry);
* `centroid_eq_finset_centroid` : `centroid P Q R` is Mathlib's `Finset.centroid` of the three
  points;
* `signedArea_eq_areaForm` : `signedArea P Q R` is half the area form of `ℂ` (standard
  orientation) on `Q - P`, `R - P`;
* `Ga_eq_centroid`, `Gb_eq_centroid`, `Gc_eq_centroid` : the Napoleon points are the Mathlib
  centroids of the triangles erected on the sides `BC`, `CA`, `AB`.
-/

namespace Napoleon

open Complex
open scoped Real

/-- **Bridge for `ωo`.** `ωo = exp(-iπ/3)`, rotation by `-π/3`. -/
theorem ωo_eq_exp : ωo = Complex.exp (↑(-(π / 3)) * I) := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  apply Complex.ext <;> simp [ωo]

/-- **Bridge for `ωi`.** `ωi = exp(iπ/3)`, rotation by `+π/3`. -/
theorem ωi_eq_exp : ωi = Complex.exp (↑(π / 3) * I) := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  apply Complex.ext <;> simp [ωi]

/-- **Bridge for `apex`.** For a unit complex number `a`, `apex a P Q` is the image of `Q` under
the rotation by `a` about `P`. -/
theorem apex_eq_rotation (a : Circle) (P Q : ℂ) : apex (a : ℂ) P Q = P + rotation a (Q - P) := by
  rw [rotation_apply, apex]

/-- **Bridge for `centroid`.** The local centroid is Mathlib's centroid of the three points. -/
theorem centroid_eq_finset_centroid (P Q R : ℂ) : centroid P Q R =
    Finset.univ.centroid ℝ ![P, Q, R] := by
  rw [Finset.centroid_def, Finset.affineCombination_eq_linear_combination _ _ _
    (by simp [Finset.sum_const, Finset.card_univ])]
  simp only [Finset.centroidWeights_apply, Finset.card_univ, Fintype.card_fin, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Complex.real_smul, centroid]
  push_cast
  ring

attribute [local instance] Complex.finrank_real_complex_fact in
/-- **Bridge for `signedArea`.** The signed area is half the area form of `ℂ` (with its standard
orientation) evaluated on the edge vectors `Q - P`, `R - P`. -/
theorem signedArea_eq_areaForm (P Q R : ℂ) : signedArea P Q R =
    Complex.orientation.areaForm (Q - P) (R - P) / 2 := by
  rw [Complex.areaForm, signedArea]

/-- **Bridge for `Ga`.** The Napoleon point on `BC` is the Mathlib centroid of the triangle
`B C (apex ω B C)`; it does not depend on `A`. -/
theorem Ga_eq_centroid (ω A B C : ℂ) : Ga ω A B C =
    Finset.univ.centroid ℝ ![B, C, apex ω B C] := by
  rw [Ga, centroid_eq_finset_centroid]

/-- **Bridge for `Gb`.** The Napoleon point on `CA`; it does not depend on `B`. -/
theorem Gb_eq_centroid (ω A B C : ℂ) : Gb ω A B C =
    Finset.univ.centroid ℝ ![C, A, apex ω C A] := by
  rw [Gb, centroid_eq_finset_centroid]

/-- **Bridge for `Gc`.** The Napoleon point on `AB`; it does not depend on `C`. -/
theorem Gc_eq_centroid (ω A B C : ℂ) : Gc ω A B C =
    Finset.univ.centroid ℝ ![A, B, apex ω A B] := by
  rw [Gc, centroid_eq_finset_centroid]

end Napoleon

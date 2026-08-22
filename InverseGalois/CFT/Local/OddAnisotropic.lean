import Mathlib
import InverseGalois.CFT.Local.UnramifiedNormForm
import InverseGalois.CFT.Global.DiagForm

/-!
# An anisotropic quaternary form at an odd place

Fix an odd prime `p` and a unit `w` of `ℤ_[p]` whose residue is not a square, so that
`x ^ 2 - w y ^ 2` is the norm form of the unramified quadratic extension of `ℚ_[p]`.  The
quaternary form `⟨1, -w, -p, w p⟩` is the orthogonal sum of that norm form and its multiple by
the uniformiser, and it is anisotropic: a zero of it would equate a value of the norm form with
`p` times another such value, and the values of the norm form all have even valuation.

Together with the dyadic case this shows that the bound of five variables is sharp at every
finite place: the `u`-invariant of a field of `p`-adic numbers is exactly four.

## Main results

* `InverseGalois.CFT.Local.eq_zero_of_sub_sq_eq_zero`: the norm form of a nonsquare vanishes only
  at the origin.
* `InverseGalois.CFT.Local.not_isDiagIsotropic_unramified_quaternary`: the form
  `⟨1, -w, -p, w p⟩` is anisotropic over `ℚ_[p]`.
* `InverseGalois.CFT.Local.exists_not_isDiagIsotropic_four_odd`: **the bound `u(ℚ_[p]) ≤ 4` is
  sharp at every odd place.**
-/

namespace InverseGalois.CFT.Local

variable {p : ℕ} [Fact p.Prime]

/-- **The norm form of a nonsquare vanishes only at the origin.**  A nontrivial zero would
exhibit the nonsquare as the square of a ratio of coordinates. -/
theorem eq_zero_of_sub_sq_eq_zero {c x y : ℚ_[p]} (hc : ¬ IsSquare c)
    (h : x ^ 2 - c * y ^ 2 = 0) : x = 0 ∧ y = 0 := by
  have hy : y = 0 := by
    by_contra hy0
    refine hc ⟨x / y, ?_⟩
    field_simp
    linear_combination -h
  refine ⟨?_, hy⟩
  rw [hy] at h
  have hx2 : x ^ 2 = 0 := by
    rw [show (0 : ℚ_[p]) ^ 2 = 0 from by ring, mul_zero, sub_zero] at h
    exact h
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hx2

/-- **The unramified quaternary form is anisotropic.**  A zero of `⟨1, -w, -p, w p⟩` equates a
value of the norm form of the unramified extension with `p` times another such value; a nonzero
value of that norm form has even valuation, and the two parities disagree. -/
theorem not_isDiagIsotropic_unramified_quaternary (hp : p ≠ 2) {w : ℤ_[p]} (hw : IsUnit w)
    (hws : ¬ IsSquare (PadicInt.toZMod w)) :
    ¬ IsDiagIsotropic
      (![1, -(w : ℚ_[p]), -(p : ℚ_[p]), (w : ℚ_[p]) * (p : ℚ_[p])] : Fin 4 → ℚ_[p]) := by
  have hnsq : ¬ IsSquare ((w : ℚ_[p])) := fun hs =>
    hws (((isSquare_coe_iff hw).mp hs).map PadicInt.toZMod)
  have hp0 : ((p : ℚ_[p])) ≠ 0 := NeZero.ne _
  rintro ⟨x, hx, hsum⟩
  rw [Fin.sum_univ_four] at hsum
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three] at hsum
  set A : ℚ_[p] := x 0 ^ 2 - (w : ℚ_[p]) * x 1 ^ 2 with hA
  set B : ℚ_[p] := x 2 ^ 2 - (w : ℚ_[p]) * x 3 ^ 2 with hB
  have hkey : A = (p : ℚ_[p]) * B := by rw [hA, hB]; linear_combination hsum
  by_cases hB0 : B = 0
  · obtain ⟨h2, h3⟩ := eq_zero_of_sub_sq_eq_zero hnsq hB0
    have hA0 : A = 0 := by rw [hkey, hB0, mul_zero]
    obtain ⟨h0, h1⟩ := eq_zero_of_sub_sq_eq_zero hnsq hA0
    refine hx (funext fun i => ?_)
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · have hA0 : A ≠ 0 := by
      rw [hkey]
      exact mul_ne_zero hp0 hB0
    have hevA : Even A.valuation := even_valuation_of_eq_sub_sq hp hw hws hA0 hA
    have hevB : Even B.valuation := even_valuation_of_eq_sub_sq hp hw hws hB0 hB
    have hval : A.valuation = 1 + B.valuation := by
      rw [hkey, Padic.valuation_mul hp0 hB0, Padic.valuation_p]
    rw [hval] at hevA
    obtain ⟨k, hk⟩ := hevA
    obtain ⟨m, hm⟩ := hevB
    omega

/-- **The bound `u(ℚ_[p]) ≤ 4` is sharp at every odd place.**  Some diagonal form in four
variables with nonzero coefficients represents zero only trivially. -/
theorem exists_not_isDiagIsotropic_four_odd (hp : p ≠ 2) :
    ∃ a : Fin 4 → ℚ_[p], (∀ i, a i ≠ 0) ∧ ¬ IsDiagIsotropic a := by
  obtain ⟨w, hw, hws⟩ := exists_unramified_nonsquare (p := p) hp
  have hwne : ((w : ℚ_[p])) ≠ 0 := PadicInt.coe_ne_zero.mpr hw.ne_zero
  have hp0 : ((p : ℚ_[p])) ≠ 0 := NeZero.ne _
  refine ⟨_, ?_, not_isDiagIsotropic_unramified_quaternary hp hw hws⟩
  intro i
  fin_cases i
  · exact one_ne_zero
  · exact neg_ne_zero.mpr hwne
  · exact neg_ne_zero.mpr hp0
  · exact mul_ne_zero hwne hp0

end InverseGalois.CFT.Local

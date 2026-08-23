import Mathlib
import InverseGalois.CFT.Local.PadicSquares

/-!
# Squares in the dyadic numbers

`InverseGalois/CFT/Local/PadicSquares.lean` describes the squares of `ℚ_[p]` for an odd prime `p`
in terms of the residue modulo `p`. That description fails at `p = 2`, where the derivative of
`X ^ 2 - C u` is not a unit and one has to go one step further into the filtration: a dyadic unit
is a square exactly when it is congruent to `1` modulo `8`. Hensel's lemma still applies, started
at the approximate root `1`, because `‖1 - u‖ ≤ 1 / 8` is strictly smaller than `‖2‖ ^ 2 = 1 / 4`.

From this one reads off that `ℚ_[2]ˣ` has exactly eight square classes, represented by
`1, -1, 5, -5, 2, -2, 10, -10`, which is the input to the computation of the Hilbert symbol at the
dyadic place. Compare Serre, *A Course in Arithmetic*, II §3.3.

Throughout, congruence modulo `8` is expressed through the ring homomorphism
`PadicInt.toZModPow 3 : ℤ_[2] →+* ZMod (2 ^ 3)`.

## Main results

* `InverseGalois.CFT.Local.toZModPow_three_eq_one_of_isSquare`: a square dyadic unit is congruent
  to `1` modulo `8`.
* `InverseGalois.CFT.Local.isSquare_of_toZModPow_three_eq_one`: conversely, a dyadic integer
  congruent to `1` modulo `8` is a square in `ℤ_[2]`.
* `InverseGalois.CFT.Local.isSquare_iff_toZModPow_three_eq_one` and
  `InverseGalois.CFT.Local.isSquare_coe_iff_two`: the resulting characterisation of the squares
  among the units of `ℤ_[2]`, in `ℤ_[2]` and in `ℚ_[2]`.
* `InverseGalois.CFT.Local.not_isSquare_neg_one_two`,
  `InverseGalois.CFT.Local.not_isSquare_five_two` and
  `InverseGalois.CFT.Local.not_isSquare_two_two`: three independent nontrivial square classes
  of `ℚ_[2]`.
* `InverseGalois.CFT.Local.exists_unit_square_class`: every dyadic unit is one of
  `1, -1, 5, -5` times a square.
* `InverseGalois.CFT.Local.exists_repr_square_class`: every nonzero dyadic number is one of
  `1, -1, 5, -5, 2, -2, 10, -10` times a square.
-/

namespace InverseGalois.CFT.Local

open Polynomial

/-- The dyadic norm of `2`, the uniformiser of `ℤ_[2]`. -/
theorem norm_two_two : ‖(2 : ℤ_[2])‖ = 1 / 2 := by
  rw [show ((2 : ℤ_[2])) = ((2 : ℕ) : ℤ_[2]) by norm_num, PadicInt.norm_p]
  norm_num

/-- A dyadic integer congruent to `1` modulo `8` differs from `1` by an element of norm at
most `1 / 8`. -/
theorem norm_sub_one_le_of_toZModPow_three_eq_one {u : ℤ_[2]}
    (h : PadicInt.toZModPow 3 u = 1) : ‖u - 1‖ ≤ 1 / 8 := by
  have hmem : u - 1 ∈ RingHom.ker (PadicInt.toZModPow 3 : ℤ_[2] →+* ZMod (2 ^ 3)) := by
    rw [RingHom.mem_ker, map_sub, map_one, h, sub_self]
  rw [PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow] at hmem
  refine hmem.trans (le_of_eq ?_)
  norm_num

/-- A square dyadic unit is congruent to `1` modulo `8`, because every unit of `ZMod 8` squares
to `1`. -/
theorem toZModPow_three_eq_one_of_isSquare {u : ℤ_[2]} (hu : IsUnit u) (h : IsSquare u) :
    PadicInt.toZModPow 3 u = 1 := by
  obtain ⟨v, rfl⟩ := h
  have hv : IsUnit v := isUnit_of_mul_isUnit_left hu
  have key : ∀ x : ZMod (2 ^ 3), IsUnit x → x * x = 1 := by decide
  rw [map_mul]
  exact key _ (hv.map _)

/-- Hensel's lemma for dyadic squares: a dyadic integer congruent to `1` modulo `8` is a square
in `ℤ_[2]`, the approximate root being `1`. -/
theorem isSquare_of_toZModPow_three_eq_one {u : ℤ_[2]} (h : PadicInt.toZModPow 3 u = 1) :
    IsSquare u := by
  set F : Polynomial ℤ_[2] := X ^ 2 - C u with hF
  have hev : F.aeval (1 : ℤ_[2]) = 1 - u := by simp [hF]
  have hder : F.derivative.aeval (1 : ℤ_[2]) = 2 := by
    simp [hF]
    norm_num
  have hdnorm : ‖F.derivative.aeval (1 : ℤ_[2])‖ = 1 / 2 := by
    rw [hder, norm_two_two]
  have hnorm : ‖F.aeval (1 : ℤ_[2])‖ < ‖F.derivative.aeval (1 : ℤ_[2])‖ ^ 2 := by
    rw [hdnorm, hev]
    have hle : ‖(1 : ℤ_[2]) - u‖ ≤ 1 / 8 := by
      rw [← norm_neg]
      simpa using norm_sub_one_le_of_toZModPow_three_eq_one h
    linarith
  obtain ⟨z, hz, -⟩ := hensels_lemma hnorm
  refine ⟨z, ?_⟩
  have hz2 : z ^ 2 - u = 0 := by simpa [hF] using hz
  linear_combination -hz2

/-- A dyadic unit is a square exactly when it is congruent to `1` modulo `8`. -/
theorem isSquare_iff_toZModPow_three_eq_one {u : ℤ_[2]} (hu : IsUnit u) :
    IsSquare u ↔ PadicInt.toZModPow 3 u = 1 :=
  ⟨toZModPow_three_eq_one_of_isSquare hu, isSquare_of_toZModPow_three_eq_one⟩

/-- A dyadic unit is a square in the field `ℚ_[2]` exactly when it is congruent to `1`
modulo `8`. -/
theorem isSquare_coe_iff_two {u : ℤ_[2]} (hu : IsUnit u) :
    IsSquare ((u : ℚ_[2])) ↔ PadicInt.toZModPow 3 u = 1 :=
  (isSquare_coe_iff hu).trans (isSquare_iff_toZModPow_three_eq_one hu)

/-- The element `5` is a unit of `ℤ_[2]`, being an odd integer. -/
theorem isUnit_five_two : IsUnit (5 : ℤ_[2]) := by
  rw [PadicInt.isUnit_iff]
  by_contra hne
  have hlt : ‖(5 : ℤ_[2])‖ < 1 := lt_of_le_of_ne (PadicInt.norm_le_one _) hne
  rw [show ((5 : ℤ_[2])) = (((5 : ℤ)) : ℤ_[2]) by norm_num,
    PadicInt.norm_int_lt_one_iff_dvd] at hlt
  norm_num at hlt

/-- The residue of `5` modulo `8`. -/
theorem toZModPow_three_five : PadicInt.toZModPow 3 (5 : ℤ_[2]) = 5 := map_ofNat _ 5

/-- The image of `5 : ℤ_[2]` in `ℚ_[2]` is `5`. -/
theorem coe_five_two : ((5 : ℤ_[2]) : ℚ_[2]) = 5 := by norm_cast

/-- The number `-1` is not a dyadic square: its residue modulo `8` is `7`. -/
theorem not_isSquare_neg_one_two : ¬ IsSquare (-1 : ℚ_[2]) := by
  intro h
  have h' : IsSquare (((-1 : ℤ_[2]) : ℚ_[2])) := by push_cast; exact h
  rw [isSquare_coe_iff_two isUnit_one.neg, map_neg, map_one] at h'
  exact absurd h' (by decide)

/-- The number `5` is not a dyadic square: its residue modulo `8` is `5`. -/
theorem not_isSquare_five_two : ¬ IsSquare (5 : ℚ_[2]) := by
  intro h
  have h' : IsSquare (((5 : ℤ_[2]) : ℚ_[2])) := h
  rw [isSquare_coe_iff_two isUnit_five_two, toZModPow_three_five] at h'
  exact absurd h' (by decide)

/-- The uniformiser `2` is not a dyadic square, its valuation being odd. -/
theorem not_isSquare_two_two : ¬ IsSquare (2 : ℚ_[2]) := by
  have h := not_isSquare_p (p := 2)
  rwa [show (((2 : ℕ)) : ℚ_[2]) = (2 : ℚ_[2]) by norm_num] at h

/-- Every dyadic unit becomes a square after multiplication by one of `1, -1, 5, -5`, since
these four elements exhaust the residues modulo `8` of the units of `ℤ_[2]`. -/
theorem exists_unit_square_class {u : ℤ_[2]} (hu : IsUnit u) :
    ∃ c : ℤ_[2], IsUnit c ∧ (c = 1 ∨ c = -1 ∨ c = 5 ∨ c = -5) ∧ IsSquare (u * c) := by
  have hcases : PadicInt.toZModPow 3 u = 1 ∨ PadicInt.toZModPow 3 u = -1 ∨
      PadicInt.toZModPow 3 u = 5 ∨ PadicInt.toZModPow 3 u = -5 := by
    have h := hu.map (PadicInt.toZModPow 3)
    revert h
    generalize PadicInt.toZModPow 3 u = r
    revert r
    decide
  rcases hcases with h | h | h | h
  · refine ⟨1, isUnit_one, Or.inl rfl, isSquare_of_toZModPow_three_eq_one ?_⟩
    rw [map_mul, h, map_one, one_mul]
  · refine ⟨-1, isUnit_one.neg, Or.inr (Or.inl rfl), isSquare_of_toZModPow_three_eq_one ?_⟩
    rw [map_mul, h, map_neg, map_one]
    decide
  · refine ⟨5, isUnit_five_two, Or.inr (Or.inr (Or.inl rfl)),
      isSquare_of_toZModPow_three_eq_one ?_⟩
    rw [map_mul, h, toZModPow_three_five]
    decide
  · refine ⟨-5, isUnit_five_two.neg, Or.inr (Or.inr (Or.inr rfl)),
      isSquare_of_toZModPow_three_eq_one ?_⟩
    rw [map_mul, h, map_neg, toZModPow_three_five]
    decide

/-- Every nonzero dyadic number is one of the eight elements `1, -1, 5, -5, 2, -2, 10, -10`
times a square, so `ℚ_[2]ˣ` has at most eight square classes. -/
theorem exists_repr_square_class (x : ℚ_[2]) (hx : x ≠ 0) :
    ∃ (c : ℚ_[2]) (y : ℚ_[2]), y ≠ 0 ∧
      c ∈ ({1, -1, 5, -5, 2, -2, 10, -10} : Set ℚ_[2]) ∧ x = c * y ^ 2 := by
  obtain ⟨n, u, hu, rfl⟩ := exists_unit_mul_zpow hx
  obtain ⟨c, hc, hcval, w, hw⟩ := exists_unit_square_class hu
  have h2 : ((2 : ℚ_[2])) ≠ 0 := two_ne_zero
  have hcast : (((2 : ℕ)) : ℚ_[2]) = (2 : ℚ_[2]) := by norm_num
  have hcne : ((c : ℚ_[2])) ≠ 0 := by
    have hc1 : ‖(c : ℚ_[2])‖ = 1 := PadicInt.isUnit_iff.mp hc
    intro h0
    rw [h0, norm_zero] at hc1
    exact zero_ne_one hc1
  have hwu : IsUnit w := by
    have hww : IsUnit (w * w) := hw ▸ hu.mul hc
    exact isUnit_of_mul_isUnit_left hww
  have hwne : ((w : ℚ_[2])) ≠ 0 := by
    have hw1 : ‖(w : ℚ_[2])‖ = 1 := PadicInt.isUnit_iff.mp hwu
    intro h0
    rw [h0, norm_zero] at hw1
    exact zero_ne_one hw1
  obtain ⟨m, e, hne, hee⟩ : ∃ m e : ℤ, n = m * 2 + e ∧ (e = 0 ∨ e = 1) :=
    ⟨n / 2, n % 2, by omega, by omega⟩
  have hsplit : (2 : ℚ_[2]) ^ n = ((2 : ℚ_[2]) ^ m) ^ 2 * (2 : ℚ_[2]) ^ e := by
    rw [← zpow_natCast ((2 : ℚ_[2]) ^ m) 2, ← zpow_mul, ← zpow_add₀ h2]
    norm_cast
    rw [← hne]
  have hwq : ((w : ℚ_[2])) ^ 2 = (u : ℚ_[2]) * (c : ℚ_[2]) := by
    have hcoe : ((u * c : ℤ_[2]) : ℚ_[2]) = ((w * w : ℤ_[2]) : ℚ_[2]) := by rw [hw]
    push_cast at hcoe
    rw [sq]
    exact hcoe.symm
  refine ⟨(2 : ℚ_[2]) ^ e * (c : ℚ_[2]),
    (2 : ℚ_[2]) ^ m * (w : ℚ_[2]) / (c : ℚ_[2]), ?_, ?_, ?_⟩
  · exact div_ne_zero (mul_ne_zero (zpow_ne_zero _ h2) hwne) hcne
  · rcases hee with rfl | rfl <;> rcases hcval with rfl | rfl | rfl | rfl <;>
      norm_num [coe_five_two]
  · rw [hcast, hsplit, div_pow, mul_pow, hwq]
    field_simp

end InverseGalois.CFT.Local

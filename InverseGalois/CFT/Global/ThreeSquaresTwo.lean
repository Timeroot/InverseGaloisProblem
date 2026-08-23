import Mathlib
import InverseGalois.CFT.Local.PadicSquaresTwo

/-!
# Sums of three squares in the dyadic numbers

A quadratic form over a local field represents everything outside the obvious obstruction, and for
the sum of three squares over `ℚ_[2]` that obstruction is visible modulo `8`: the quaternary form
`x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2` is anisotropic, because scaling a nontrivial dyadic zero so that
one coordinate becomes `1` produces a relation `1 + b ^ 2 + c ^ 2 + d ^ 2 = 0` among dyadic
integers, and `7` is not a sum of three squares in `ZMod 8`. So a dyadic number `c` whose negative
is a square is never a sum of three squares.

Conversely every other square class is a sum of three squares. Multiplying by a nonzero square
changes neither side of the equivalence, so it is enough to inspect the eight representatives
`1, -1, 5, -5, 2, -2, 10, -10` produced by
`InverseGalois.CFT.Local.exists_repr_square_class`. Seven of them are sums of three squares, the
three negative ones because `-7` and `-15` are dyadic units congruent to `1` modulo `8` and hence
squares; the remaining class `-1` is exactly the one excluded by the anisotropy above.

## Main results

* `InverseGalois.CFT.eq_zero_of_sum_four_sq_two`: the quaternary form
  `x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2` is anisotropic over `ℚ_[2]`.
* `InverseGalois.CFT.not_exists_three_sq_two_of_isSquare_neg`: a nonzero dyadic number whose
  negative is a square is not a sum of three squares.
* `InverseGalois.CFT.exists_three_sq_two_of_not_isSquare_neg`: a dyadic number whose negative is
  not a square is a sum of three squares.
* `InverseGalois.CFT.exists_three_sq_two_iff`: the resulting characterisation of the sums of three
  squares among the nonzero dyadic numbers.
-/

namespace InverseGalois.CFT

open Local

/-- The residue `7` is not a sum of three squares modulo `8`, the squares of `ZMod 8` being
`0`, `1` and `4`. -/
theorem one_add_three_sq_ne_zero_zmod_eight :
    ∀ b c d : ZMod (2 ^ 3), 1 + b ^ 2 + c ^ 2 + d ^ 2 ≠ 0 := by decide

/-- No three dyadic integers satisfy `1 + b ^ 2 + c ^ 2 + d ^ 2 = 0`, as one sees after reducing
the relation modulo `8`. -/
theorem one_add_three_sq_ne_zero_padicInt {b c d : ℤ_[2]} :
    (1 : ℤ_[2]) + b ^ 2 + c ^ 2 + d ^ 2 ≠ 0 := by
  intro h
  have h' := congrArg (PadicInt.toZModPow 3) h
  simp only [map_add, map_pow, map_one, map_zero] at h'
  exact one_add_three_sq_ne_zero_zmod_eight _ _ _ h'

/-- In a dyadic zero of `x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2` the coordinate of largest absolute value
vanishes: dividing by it turns the relation into one between dyadic integers with a coordinate
equal to `1`. -/
theorem eq_zero_of_norm_max_two {x y z w : ℚ_[2]} (h : x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = 0)
    (hy : ‖y‖ ≤ ‖x‖) (hz : ‖z‖ ≤ ‖x‖) (hw : ‖w‖ ≤ ‖x‖) : x = 0 := by
  by_contra hx
  have hxn : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  have hb1 : ‖y / x‖ ≤ 1 := by rw [norm_div]; exact (div_le_one hxn).mpr hy
  have hc1 : ‖z / x‖ ≤ 1 := by rw [norm_div]; exact (div_le_one hxn).mpr hz
  have hd1 : ‖w / x‖ ≤ 1 := by rw [norm_div]; exact (div_le_one hxn).mpr hw
  obtain ⟨b, hb⟩ : ∃ b : ℤ_[2], (b : ℚ_[2]) = y / x := ⟨⟨y / x, hb1⟩, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℤ_[2], (c : ℚ_[2]) = z / x := ⟨⟨z / x, hc1⟩, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℤ_[2], (d : ℚ_[2]) = w / x := ⟨⟨w / x, hd1⟩, rfl⟩
  refine one_add_three_sq_ne_zero_padicInt (b := b) (c := c) (d := d) (Subtype.coe_injective ?_)
  push_cast
  rw [hb, hc, hd]
  field_simp
  linear_combination h

/-- **The sum of four squares is anisotropic over the dyadic numbers.** -/
theorem eq_zero_of_sum_four_sq_two {x y z w : ℚ_[2]} (h : x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = 0) :
    x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0 := by
  have key : ∀ a b c d : ℚ_[2], a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 0 →
      ‖b‖ ≤ ‖a‖ → ‖c‖ ≤ ‖a‖ → ‖d‖ ≤ ‖a‖ → a = 0 := fun _ _ _ _ => eq_zero_of_norm_max_two
  have main : ∀ a : ℚ_[2], a = 0 → ‖x‖ ≤ ‖a‖ → ‖y‖ ≤ ‖a‖ → ‖z‖ ≤ ‖a‖ → ‖w‖ ≤ ‖a‖ →
      x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0 := by
    intro a ha h1 h2 h3 h4
    rw [ha, norm_zero] at h1 h2 h3 h4
    exact ⟨norm_le_zero_iff.mp h1, norm_le_zero_iff.mp h2, norm_le_zero_iff.mp h3,
      norm_le_zero_iff.mp h4⟩
  have maxW : ‖x‖ ≤ ‖w‖ → ‖y‖ ≤ ‖w‖ → ‖z‖ ≤ ‖w‖ → x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0 := by
    intro h1 h2 h3
    exact main w (key w x y z (by linear_combination h) h1 h2 h3) h1 h2 h3 le_rfl
  have maxZ : ‖x‖ ≤ ‖z‖ → ‖y‖ ≤ ‖z‖ → ‖w‖ ≤ ‖z‖ → x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0 := by
    intro h1 h2 h3
    exact main z (key z x y w (by linear_combination h) h1 h2 h3) h1 h2 le_rfl h3
  have maxY : ‖x‖ ≤ ‖y‖ → ‖z‖ ≤ ‖y‖ → ‖w‖ ≤ ‖y‖ → x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0 := by
    intro h1 h2 h3
    exact main y (key y x z w (by linear_combination h) h1 h2 h3) h1 le_rfl h2 h3
  have maxX : ‖y‖ ≤ ‖x‖ → ‖z‖ ≤ ‖x‖ → ‖w‖ ≤ ‖x‖ → x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0 := by
    intro h1 h2 h3
    exact main x (key x y z w (by linear_combination h) h1 h2 h3) le_rfl h1 h2 h3
  rcases le_total ‖x‖ ‖y‖ with h1 | h1
  · rcases le_total ‖y‖ ‖z‖ with h2 | h2
    · rcases le_total ‖z‖ ‖w‖ with h3 | h3
      · exact maxW (by linarith) (by linarith) (by linarith)
      · exact maxZ (by linarith) (by linarith) (by linarith)
    · rcases le_total ‖y‖ ‖w‖ with h3 | h3
      · exact maxW (by linarith) (by linarith) (by linarith)
      · exact maxY (by linarith) (by linarith) (by linarith)
  · rcases le_total ‖x‖ ‖z‖ with h2 | h2
    · rcases le_total ‖z‖ ‖w‖ with h3 | h3
      · exact maxW (by linarith) (by linarith) (by linarith)
      · exact maxZ (by linarith) (by linarith) (by linarith)
    · rcases le_total ‖x‖ ‖w‖ with h3 | h3
      · exact maxW (by linarith) (by linarith) (by linarith)
      · exact maxX (by linarith) (by linarith) (by linarith)

/-- The number `-7` is a dyadic square, being congruent to `1` modulo `8`. -/
theorem isSquare_neg_seven_two : IsSquare (-7 : ℚ_[2]) := by
  have h : IsSquare (-7 : ℤ_[2]) := by
    refine isSquare_of_toZModPow_three_eq_one ?_
    rw [show (-7 : ℤ_[2]) = -(7 : ℤ_[2]) by norm_num, map_neg, map_ofNat]
    decide
  obtain ⟨s, hs⟩ := h
  refine ⟨(s : ℚ_[2]), ?_⟩
  have hcast := congrArg (fun t : ℤ_[2] => (t : ℚ_[2])) hs
  push_cast at hcast
  exact hcast

/-- The number `-15` is a dyadic square, being congruent to `1` modulo `8`. -/
theorem isSquare_neg_fifteen_two : IsSquare (-15 : ℚ_[2]) := by
  have h : IsSquare (-15 : ℤ_[2]) := by
    refine isSquare_of_toZModPow_three_eq_one ?_
    rw [show (-15 : ℤ_[2]) = -(15 : ℤ_[2]) by norm_num, map_neg, map_ofNat]
    decide
  obtain ⟨s, hs⟩ := h
  refine ⟨(s : ℚ_[2]), ?_⟩
  have hcast := congrArg (fun t : ℤ_[2] => (t : ℚ_[2])) hs
  push_cast at hcast
  exact hcast

/-- Whether the negative of a dyadic number is a square depends only on its square class. -/
theorem isSquare_neg_mul_sq_iff_two {c y : ℚ_[2]} (hy : y ≠ 0) :
    IsSquare (-(c * y ^ 2)) ↔ IsSquare (-c) := by
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s / y, by field_simp; linear_combination hs⟩
  · rintro ⟨s, hs⟩
    exact ⟨s * y, by linear_combination y ^ 2 * hs⟩

/-- Being a sum of three squares depends only on the square class, a common factor being absorbed
into the three coordinates. -/
theorem exists_three_sq_mul_sq_two {c y : ℚ_[2]}
    (h : ∃ a b d : ℚ_[2], c = a ^ 2 + b ^ 2 + d ^ 2) :
    ∃ a b d : ℚ_[2], c * y ^ 2 = a ^ 2 + b ^ 2 + d ^ 2 := by
  obtain ⟨a, b, d, rfl⟩ := h
  exact ⟨a * y, b * y, d * y, by ring⟩

/-- Seven of the eight dyadic square classes are sums of three squares, with the representations
`1 = 1 + 0 + 0`, `5 = 4 + 1 + 0`, `-5 = 1 + 1 + (-7)`, `2 = 1 + 1 + 0`, `-2 = 1 + 4 + (-7)`,
`10 = 9 + 1 + 0` and `-10 = 1 + 4 + (-15)`. -/
theorem exists_three_sq_repr_two {c : ℚ_[2]}
    (hmem : c = 1 ∨ c = 5 ∨ c = -5 ∨ c = 2 ∨ c = -2 ∨ c = 10 ∨ c = -10) :
    ∃ a b d : ℚ_[2], c = a ^ 2 + b ^ 2 + d ^ 2 := by
  obtain ⟨s, hs⟩ := isSquare_neg_seven_two
  obtain ⟨r, hr⟩ := isSquare_neg_fifteen_two
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 0, 0, by ring⟩
  · exact ⟨2, 1, 0, by ring⟩
  · exact ⟨1, 1, s, by linear_combination hs⟩
  · exact ⟨1, 1, 0, by ring⟩
  · exact ⟨1, 2, s, by linear_combination hs⟩
  · exact ⟨3, 1, 0, by ring⟩
  · exact ⟨1, 2, r, by linear_combination hr⟩

/-- A nonzero dyadic number whose negative is a square is not a sum of three squares, for
otherwise the sum of four squares would have a nontrivial zero. -/
theorem not_exists_three_sq_two_of_isSquare_neg {c : ℚ_[2]} (hc : c ≠ 0) (h : IsSquare (-c)) :
    ¬ ∃ x y z : ℚ_[2], c = x ^ 2 + y ^ 2 + z ^ 2 := by
  rintro ⟨x, y, z, rfl⟩
  obtain ⟨w, hw⟩ := h
  obtain ⟨hx, hy, hz, -⟩ := eq_zero_of_sum_four_sq_two (w := w)
    (show x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = 0 by linear_combination -hw)
  exact hc (by rw [hx, hy, hz]; ring)

/-- A dyadic number whose negative is not a square is a sum of three squares, its square class
being one of the seven admissible ones. -/
theorem exists_three_sq_two_of_not_isSquare_neg {c : ℚ_[2]} (hc : c ≠ 0) (h : ¬ IsSquare (-c)) :
    ∃ x y z : ℚ_[2], c = x ^ 2 + y ^ 2 + z ^ 2 := by
  obtain ⟨c₀, y, hy, hmem, rfl⟩ := exists_repr_square_class c hc
  have h0 : ¬ IsSquare (-c₀) := fun hs => h ((isSquare_neg_mul_sq_iff_two hy).mpr hs)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  refine exists_three_sq_mul_sq_two (exists_three_sq_repr_two ?_)
  rcases hmem with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
  · exact Or.inl h1
  · exact absurd (show IsSquare (-c₀) from ⟨1, by rw [h1]; norm_num⟩) h0
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1)))))

/-- **A nonzero dyadic number is a sum of three squares exactly when its negative is not a
square.** -/
theorem exists_three_sq_two_iff {c : ℚ_[2]} (hc : c ≠ 0) :
    (∃ x y z : ℚ_[2], c = x ^ 2 + y ^ 2 + z ^ 2) ↔ ¬ IsSquare (-c) :=
  ⟨fun hrep hsq => not_exists_three_sq_two_of_isSquare_neg hc hsq hrep,
    exists_three_sq_two_of_not_isSquare_neg hc⟩

end InverseGalois.CFT

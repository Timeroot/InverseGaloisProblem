import Mathlib

/-!
# The Hilbert symbol

Following Serre, *A Course in Arithmetic*, Chapter III, the Hilbert symbol of two elements `a`
and `b` of a field `K` records whether the conic `z ^ 2 = a * x ^ 2 + b * y ^ 2` has a nontrivial
point over `K`: the symbol is `1` when it does and `-1` when it does not.  Equivalently, it says
whether the quaternion algebra `(a, b / K)` splits.  This file develops the elementary,
purely field-theoretic half of the theory: the symmetry of the symbol, its invariance under
multiplying an argument by a square, the values it takes on the standard configurations
`⟨a, 1⟩`, `⟨a, -a⟩` and `⟨a, 1 - a⟩`, the description of `⟨a, b⟩ = 1` as the assertion that `a`
is a norm from `K(√b)`, and the complete computation of the symbol over `ℝ`, where it is `-1`
exactly for two negative arguments.

The symbol takes its values in `ℤ`, as the pair of units `1` and `-1`.

No hypothesis on the characteristic of `K` is needed anywhere below, and the isotropy of a form
is a condition on the pair `(a, b)` alone, so several statements hold without the customary
hypotheses that `a` and `b` be nonzero.

## Main results

* `InverseGalois.CFT.Local.IsHilbertIsotropic`: the conic `z ^ 2 = a * x ^ 2 + b * y ^ 2` has a
  point other than the origin.
* `InverseGalois.CFT.Local.hilbertSymbol`: the Hilbert symbol, valued in `ℤ`.
* `InverseGalois.CFT.Local.hilbertSymbol_eq_one_iff`,
  `InverseGalois.CFT.Local.hilbertSymbol_eq_neg_one_iff`: the two values and what they mean.
* `InverseGalois.CFT.Local.hilbertSymbol_eq_one_or`,
  `InverseGalois.CFT.Local.hilbertSymbol_sq`, `InverseGalois.CFT.Local.abs_hilbertSymbol`,
  `InverseGalois.CFT.Local.hilbertSymbol_ne_zero`: the symbol is a sign.
* `InverseGalois.CFT.Local.hilbertSymbol_comm`: the symbol is symmetric.
* `InverseGalois.CFT.Local.hilbertSymbol_mul_sq_right`,
  `InverseGalois.CFT.Local.hilbertSymbol_mul_sq_left`: the symbol only depends on the classes of
  its arguments modulo squares.
* `InverseGalois.CFT.Local.hilbertSymbol_one_right`,
  `InverseGalois.CFT.Local.hilbertSymbol_neg_self`,
  `InverseGalois.CFT.Local.hilbertSymbol_one_sub`,
  `InverseGalois.CFT.Local.hilbertSymbol_of_isSquare_left`: the standard values.
* `InverseGalois.CFT.Local.hilbertSymbol_eq_one_iff_exists_sub_sq`: for `b` a nonsquare, the
  symbol is `1` exactly when `a` is a norm from `K(√b)`.
* `InverseGalois.CFT.Local.not_isHilbertIsotropic_of_neg`: over an ordered field a form with two
  negative coefficients is anisotropic.
* `InverseGalois.CFT.Local.hilbertSymbol_real`: the symbol over `ℝ`, computed.
* `InverseGalois.CFT.Local.hilbertSymbol_real_mul_left`,
  `InverseGalois.CFT.Local.hilbertSymbol_real_mul_right`: over `ℝ` the symbol is
  bimultiplicative.
* `InverseGalois.CFT.Local.hilbertSymbol_rat_neg_one_neg_one`: the rational quaternion algebra
  `(-1, -1 / ℚ)` does not split.
-/

namespace InverseGalois.CFT.Local

variable {K : Type*} [Field K]

/-- The binary quadratic form `⟨a, b⟩` over `K` is **isotropic** when the conic
`z ^ 2 = a * x ^ 2 + b * y ^ 2` has a point other than the origin, that is, when the ternary
form `z ^ 2 - a * x ^ 2 - b * y ^ 2` represents zero nontrivially. -/
def IsHilbertIsotropic (a b : K) : Prop :=
  ∃ x y z : K, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2

open scoped Classical in
/-- The **Hilbert symbol** of `a` and `b`, equal to `1` when the form `⟨a, b⟩` is isotropic and
to `-1` when it is not. -/
noncomputable def hilbertSymbol (a b : K) : ℤ :=
  if IsHilbertIsotropic a b then 1 else -1

/-- The Hilbert symbol is `1` exactly for an isotropic form. -/
theorem hilbertSymbol_eq_one_iff {a b : K} :
    hilbertSymbol a b = 1 ↔ IsHilbertIsotropic a b := by
  unfold hilbertSymbol
  split_ifs with h
  · simp [h]
  · simp [h]

/-- The Hilbert symbol is `-1` exactly for an anisotropic form. -/
theorem hilbertSymbol_eq_neg_one_iff {a b : K} :
    hilbertSymbol a b = -1 ↔ ¬ IsHilbertIsotropic a b := by
  unfold hilbertSymbol
  split_ifs with h
  · simp [h]
  · simp [h]

/-- The Hilbert symbol takes only the two values `1` and `-1`. -/
theorem hilbertSymbol_eq_one_or (a b : K) :
    hilbertSymbol a b = 1 ∨ hilbertSymbol a b = -1 := by
  unfold hilbertSymbol
  split_ifs with h
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The Hilbert symbol is nonzero. -/
theorem hilbertSymbol_ne_zero (a b : K) : hilbertSymbol a b ≠ 0 := by
  rcases hilbertSymbol_eq_one_or a b with h | h <;> rw [h] <;> norm_num

/-- The Hilbert symbol squares to one. -/
theorem hilbertSymbol_sq (a b : K) : hilbertSymbol a b ^ 2 = 1 := by
  rcases hilbertSymbol_eq_one_or a b with h | h <;> rw [h] <;> norm_num

/-- The Hilbert symbol has absolute value one. -/
theorem abs_hilbertSymbol (a b : K) : |hilbertSymbol a b| = 1 := by
  rcases hilbertSymbol_eq_one_or a b with h | h <;> rw [h] <;> norm_num

/-- Two pairs whose forms are isotropic together have the same Hilbert symbol. -/
theorem hilbertSymbol_congr {a b a' b' : K}
    (h : IsHilbertIsotropic a b ↔ IsHilbertIsotropic a' b') :
    hilbertSymbol a b = hilbertSymbol a' b' := by
  by_cases hi : IsHilbertIsotropic a b
  · rw [hilbertSymbol_eq_one_iff.2 hi, hilbertSymbol_eq_one_iff.2 (h.1 hi)]
  · rw [hilbertSymbol_eq_neg_one_iff.2 hi,
      hilbertSymbol_eq_neg_one_iff.2 fun h' => hi (h.2 h')]

/-- Isotropy is symmetric in the two coefficients: exchange `x` and `y`. -/
theorem IsHilbertIsotropic.symm {a b : K} (h : IsHilbertIsotropic a b) :
    IsHilbertIsotropic b a := by
  obtain ⟨x, y, z, hne, hz⟩ := h
  exact ⟨y, x, z, fun h => hne ⟨h.2.1, h.1, h.2.2⟩, by rw [hz]; ring⟩

/-- The form `⟨a, b⟩` is isotropic if and only if `⟨b, a⟩` is. -/
theorem isHilbertIsotropic_comm {a b : K} :
    IsHilbertIsotropic a b ↔ IsHilbertIsotropic b a :=
  ⟨IsHilbertIsotropic.symm, IsHilbertIsotropic.symm⟩

/-- **Symmetry of the Hilbert symbol.** -/
theorem hilbertSymbol_comm (a b : K) : hilbertSymbol a b = hilbertSymbol b a :=
  hilbertSymbol_congr isHilbertIsotropic_comm

/-- Multiplying the second coefficient by a nonzero square preserves isotropy: replace the
solution `(x, y, z)` by `(x, y / c, z)`. -/
theorem IsHilbertIsotropic.mul_sq_right {a b c : K} (hc : c ≠ 0) (h : IsHilbertIsotropic a b) :
    IsHilbertIsotropic a (b * c ^ 2) := by
  obtain ⟨x, y, z, hne, hz⟩ := h
  refine ⟨x, y / c, z, ?_, ?_⟩
  · rintro ⟨hx, hy, hz0⟩
    rw [div_eq_zero_iff] at hy
    exact hne ⟨hx, hy.resolve_right hc, hz0⟩
  · rw [hz]
    field_simp

/-- Isotropy only depends on the second coefficient modulo nonzero squares. -/
theorem isHilbertIsotropic_mul_sq_right {a b c : K} (hc : c ≠ 0) :
    IsHilbertIsotropic a (b * c ^ 2) ↔ IsHilbertIsotropic a b := by
  refine ⟨fun h => ?_, fun h => h.mul_sq_right hc⟩
  have h' := h.mul_sq_right (inv_ne_zero hc)
  rwa [show b * c ^ 2 * c⁻¹ ^ 2 = b by field_simp] at h'

/-- **The Hilbert symbol is invariant under multiplying its second argument by a square.** -/
theorem hilbertSymbol_mul_sq_right (a b c : K) (hc : c ≠ 0) :
    hilbertSymbol a (b * c ^ 2) = hilbertSymbol a b :=
  hilbertSymbol_congr (isHilbertIsotropic_mul_sq_right hc)

/-- **The Hilbert symbol is invariant under multiplying its first argument by a square.** -/
theorem hilbertSymbol_mul_sq_left (a b c : K) (hc : c ≠ 0) :
    hilbertSymbol (a * c ^ 2) b = hilbertSymbol a b := by
  rw [hilbertSymbol_comm, hilbertSymbol_mul_sq_right _ _ _ hc, hilbertSymbol_comm]

/-- The form `⟨a, 1⟩` is isotropic, as `(x, y, z) = (0, 1, 1)` shows. -/
theorem hilbertSymbol_one_right (a : K) : hilbertSymbol a 1 = 1 :=
  hilbertSymbol_eq_one_iff.2 ⟨0, 1, 1, by simp, by ring⟩

/-- The form `⟨1, b⟩` is isotropic. -/
theorem hilbertSymbol_one_left (b : K) : hilbertSymbol 1 b = 1 := by
  rw [hilbertSymbol_comm, hilbertSymbol_one_right]

/-- The form `⟨a, -a⟩` is isotropic, as `(x, y, z) = (1, 1, 0)` shows. -/
theorem hilbertSymbol_neg_self (a : K) : hilbertSymbol a (-a) = 1 :=
  hilbertSymbol_eq_one_iff.2 ⟨1, 1, 0, by simp, by ring⟩

/-- The form `⟨a, 1 - a⟩` is isotropic, as `(x, y, z) = (1, 1, 1)` shows. -/
theorem hilbertSymbol_one_sub (a : K) : hilbertSymbol a (1 - a) = 1 :=
  hilbertSymbol_eq_one_iff.2 ⟨1, 1, 1, by simp, by ring⟩

/-- A square first coefficient makes the Hilbert symbol trivial: if `a = c * c` then
`(x, y, z) = (1, 0, c)` is a point of the conic. -/
theorem hilbertSymbol_of_isSquare_left (a b : K) (h : IsSquare a) : hilbertSymbol a b = 1 := by
  obtain ⟨c, rfl⟩ := h
  exact hilbertSymbol_eq_one_iff.2 ⟨1, 0, c, by simp, by ring⟩

/-- A square second coefficient makes the Hilbert symbol trivial. -/
theorem hilbertSymbol_of_isSquare_right (a b : K) (h : IsSquare b) : hilbertSymbol a b = 1 := by
  rw [hilbertSymbol_comm]
  exact hilbertSymbol_of_isSquare_left _ _ h

/-- **The norm characterisation of the Hilbert symbol.**  When `b` is not a square in `K`, the
symbol `⟨a, b⟩` is `1` exactly when `a` is a norm from the quadratic extension `K(√b)`, that is,
of the shape `u ^ 2 - b * v ^ 2`.  A point of the conic must have `x ≠ 0`, since otherwise `b`
would be the square of `z / y`, and dividing through by `x` exhibits `a` as a norm. -/
theorem hilbertSymbol_eq_one_iff_exists_sub_sq {a b : K} (hb : ¬ IsSquare b) :
    hilbertSymbol a b = 1 ↔ ∃ u v : K, a = u ^ 2 - b * v ^ 2 := by
  rw [hilbertSymbol_eq_one_iff]
  constructor
  · rintro ⟨x, y, z, hne, hz⟩
    have hx : x ≠ 0 := by
      rintro rfl
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        zero_add] at hz
      have hy : y ≠ 0 := by
        rintro rfl
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
          pow_eq_zero_iff] at hz
        exact hne ⟨rfl, rfl, hz⟩
      exact hb ⟨z / y, by field_simp; linear_combination -hz⟩
    refine ⟨z / x, y / x, ?_⟩
    field_simp
    linear_combination -hz
  · rintro ⟨u, v, rfl⟩
    exact ⟨1, v, u, by simp, by ring⟩

section Ordered

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Over an ordered field a form with two negative coefficients is anisotropic: both
`a * x ^ 2` and `b * y ^ 2` are nonpositive while `z ^ 2` is nonnegative, so all three of `x`,
`y` and `z` vanish. -/
theorem not_isHilbertIsotropic_of_neg {a b : F} (ha : a < 0) (hb : b < 0) :
    ¬ IsHilbertIsotropic a b := by
  rintro ⟨x, y, z, hne, hz⟩
  have hx : x = 0 := by
    by_contra hx
    have hx2 : 0 < x ^ 2 := by positivity
    nlinarith [sq_nonneg z, sq_nonneg y, mul_pos (neg_pos.2 ha) hx2,
      mul_nonneg (neg_nonneg.2 hb.le) (sq_nonneg y)]
  have hy : y = 0 := by
    by_contra hy
    have hy2 : 0 < y ^ 2 := by positivity
    nlinarith [sq_nonneg z, sq_nonneg x, mul_pos (neg_pos.2 hb) hy2,
      mul_nonneg (neg_nonneg.2 ha.le) (sq_nonneg x)]
  subst hx
  subst hy
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero,
    pow_eq_zero_iff] at hz
  exact hne ⟨rfl, rfl, hz⟩

/-- Over an ordered field the Hilbert symbol of two negative elements is `-1`. -/
theorem hilbertSymbol_eq_neg_one_of_neg {a b : F} (ha : a < 0) (hb : b < 0) :
    hilbertSymbol a b = -1 :=
  hilbertSymbol_eq_neg_one_iff.2 (not_isHilbertIsotropic_of_neg ha hb)

end Ordered

/-- **The Hilbert symbol at the real place.**  For nonzero reals it is `-1` when both arguments
are negative and `1` otherwise: a positive real is a square, and a form with two negative
coefficients is anisotropic. -/
theorem hilbertSymbol_real (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertSymbol a b = if a < 0 ∧ b < 0 then -1 else 1 := by
  split_ifs with h
  · exact hilbertSymbol_eq_neg_one_of_neg h.1 h.2
  · rw [not_and_or] at h
    rcases h with h | h
    · have hpos : 0 < a := lt_of_le_of_ne (not_lt.1 h) (Ne.symm ha)
      exact hilbertSymbol_of_isSquare_left _ _ ⟨Real.sqrt a, (Real.mul_self_sqrt hpos.le).symm⟩
    · have hpos : 0 < b := lt_of_le_of_ne (not_lt.1 h) (Ne.symm hb)
      exact hilbertSymbol_of_isSquare_right _ _ ⟨Real.sqrt b, (Real.mul_self_sqrt hpos.le).symm⟩

/-- The real Hilbert symbol is `-1` exactly for two negative arguments. -/
theorem hilbertSymbol_real_eq_neg_one_iff (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertSymbol a b = -1 ↔ a < 0 ∧ b < 0 := by
  rw [hilbertSymbol_real a b ha hb]
  split_ifs with h
  · simp [h]
  · simp [h]

/-- **The real Hilbert symbol is multiplicative in its first argument.** -/
theorem hilbertSymbol_real_mul_left (a a' b : ℝ) (ha : a ≠ 0) (ha' : a' ≠ 0) (hb : b ≠ 0) :
    hilbertSymbol (a * a') b = hilbertSymbol a b * hilbertSymbol a' b := by
  rw [hilbertSymbol_real _ _ (mul_ne_zero ha ha') hb, hilbertSymbol_real a b ha hb,
    hilbertSymbol_real a' b ha' hb]
  rcases ha.lt_or_gt with h1 | h1 <;> rcases ha'.lt_or_gt with h2 | h2
  · have h3 : ¬ a * a' < 0 := not_lt.2 (mul_pos_of_neg_of_neg h1 h2).le
    simp only [h3, false_and, if_false, h1, h2, true_and]
    split_ifs <;> norm_num
  · have h3 : a * a' < 0 := mul_neg_of_neg_of_pos h1 h2
    have h4 : ¬ a' < 0 := not_lt.2 h2.le
    simp only [h3, h1, h4, true_and, false_and, if_false]
    split_ifs <;> norm_num
  · have h3 : a * a' < 0 := mul_neg_of_pos_of_neg h1 h2
    have h4 : ¬ a < 0 := not_lt.2 h1.le
    simp only [h3, h2, h4, true_and, false_and, if_false]
    split_ifs <;> norm_num
  · have h3 : ¬ a * a' < 0 := not_lt.2 (mul_pos h1 h2).le
    have h4 : ¬ a < 0 := not_lt.2 h1.le
    have h5 : ¬ a' < 0 := not_lt.2 h2.le
    simp only [h3, h4, h5, false_and, if_false]
    norm_num

/-- **The real Hilbert symbol is multiplicative in its second argument.** -/
theorem hilbertSymbol_real_mul_right (a b b' : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hb' : b' ≠ 0) :
    hilbertSymbol a (b * b') = hilbertSymbol a b * hilbertSymbol a b' := by
  rw [hilbertSymbol_comm a (b * b'), hilbertSymbol_comm a b, hilbertSymbol_comm a b',
    hilbertSymbol_real_mul_left b b' a hb hb' ha]

/-- **The rational quaternion algebra `(-1, -1 / ℚ)` does not split**: the conic
`z ^ 2 = -x ^ 2 - y ^ 2` has no rational point other than the origin. -/
theorem hilbertSymbol_rat_neg_one_neg_one : hilbertSymbol (-1 : ℚ) (-1) = -1 :=
  hilbertSymbol_eq_neg_one_of_neg (by norm_num) (by norm_num)

end InverseGalois.CFT.Local

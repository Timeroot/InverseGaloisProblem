import Mathlib
import InverseGalois.CFT.Local.DyadicQuinary

/-!
# Quaternary forms at the dyadic place with one ramified coefficient

Over `ℚ_[2]` a diagonal form in four unit variables can be anisotropic: the norm form
`⟨1, 1, 1, 1⟩` of the Hamilton quaternions is the standard example.  Making one of the four
coefficients ramified, that is of valuation exactly one, destroys the obstruction, and the
resulting form `⟨a₀, a₁, a₂, 2w⟩` with `a₀, a₁, a₂, w` units is always isotropic.

The mechanism is the same congruence argument modulo `8` that governs five unit variables, with
the ramified variable playing the role of a fifth unit at half the scale.  Modulo `8` a unit is
one of `1, 3, 5, 7`; setting the second variable to `1`, the third to `0` or `2` and the fourth
to `0` or `1` contributes `0` or `4` from the third term and `0` or `2v` from the ramified term,
where `2v ∈ {2, 6}`.  Together these realise every even residue modulo `8`, and `u₀ + u₁` is even,
so the three last terms can always be made to cancel `u₀` modulo `8`.  Solving for the first
variable leaves a dyadic unit congruent to `1` modulo `8`, hence a square, and the form vanishes
at a point whose first coordinate is nonzero.

## Main results

* `InverseGalois.CFT.Local.exists_dyadicQuaternaryPattern`: the congruence combinatorics modulo
  `8` behind the ramified quaternary form.
* `InverseGalois.CFT.Local.exists_sum_eq_zero_four`: three dyadic units together with twice a
  dyadic unit are the coefficients of a diagonal form vanishing at a point with a nonzero first
  coordinate.
* `InverseGalois.CFT.Local.isDiagIsotropic_two_quaternary`: **a diagonal form over `ℚ_[2]` in four
  variables, three of whose coefficients have absolute value one and one of whose coefficients has
  absolute value `2⁻¹`, is isotropic.**
-/

namespace InverseGalois.CFT.Local

set_option maxRecDepth 4000 in
/-- **The congruence combinatorics for a ramified quaternary form.**  Given three odd residues
modulo `8` and a fourth odd residue scaled by `2`, values in `{0, 1, 2}` for the last two
variables make the diagonal form vanish modulo `8` when the first two variables are `1`. -/
theorem exists_dyadicQuaternaryPattern (k0 k1 k2 kw : Fin 4) :
    ∃ b d : Fin 3,
      oddResidue k0 * 1 + oddResidue k1 * 1
        + oddResidue k2 * ((smallValue b : ℕ) : ZMod 8) ^ 2
        + 2 * oddResidue kw * ((smallValue d : ℕ) : ZMod 8) ^ 2 = 0 := by
  revert k0 k1 k2 kw
  decide

/-- **A diagonal form in four variables with three unit coefficients and one coefficient of
valuation one vanishes nontrivially over `ℤ_[2]`.**  The congruence pattern modulo `8` is lifted
by Hensel's lemma: after fixing the last three variables the remaining unit is congruent to `1`
modulo `8`, hence a square. -/
theorem exists_sum_eq_zero_four {a0 a1 a2 w : ℤ_[2]} (h0 : IsUnit a0) (h1 : IsUnit a1)
    (h2 : IsUnit a2) (hw : IsUnit w) :
    ∃ x0 x1 x2 x3 : ℤ_[2], x0 ≠ 0 ∧
      a0 * x0 ^ 2 + a1 * x1 ^ 2 + a2 * x2 ^ 2 + 2 * w * x3 ^ 2 = 0 := by
  obtain ⟨k0, hk0⟩ := exists_oddResidue (h0.map dyadicReduction)
  obtain ⟨k1, hk1⟩ := exists_oddResidue (h1.map dyadicReduction)
  obtain ⟨k2, hk2⟩ := exists_oddResidue (h2.map dyadicReduction)
  obtain ⟨kw, hkw⟩ := exists_oddResidue (hw.map dyadicReduction)
  obtain ⟨b, d, hc⟩ := exists_dyadicQuaternaryPattern k0 k1 k2 kw
  set v : Fin 3 → ℤ_[2] := fun c => ((smallValue c : ℕ) : ℤ_[2]) with hv
  have hred : ∀ c : Fin 3, dyadicReduction (v c) = ((smallValue c : ℕ) : ZMod 8) := by
    intro c
    simp [hv]
  set R : ℤ_[2] := a1 * 1 ^ 2 + a2 * v b ^ 2 + 2 * w * v d ^ 2 with hR
  set s : ℤ_[2] := ((h0.unit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (-R) with hs
  have h0s : a0 * s = -R := by
    rw [hs, ← mul_assoc, h0.mul_val_inv, one_mul]
  rw [hk0, hk1, hk2, hkw] at hc
  have hreds : dyadicReduction s = 1 := by
    refine (h0.map dyadicReduction).mul_left_cancel ?_
    rw [← map_mul, h0s, mul_one, map_neg, hR]
    simp only [map_add, map_mul, map_pow, map_ofNat, map_one, hred]
    linear_combination -hc
  obtain ⟨t, ht⟩ := isSquare_of_toZModPow_three_eq_one hreds
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, map_zero] at hreds
    exact absurd hreds (by decide)
  refine ⟨t, 1, v b, v d, ?_, ?_⟩
  · intro h
    rw [h, mul_zero] at ht
    exact hs0 ht
  · have hts : t ^ 2 = s := by rw [ht]; ring
    rw [hts, h0s, hR]
    ring

/-- **A diagonal form over `ℚ_[2]` in four variables with three unit coefficients and one
coefficient of absolute value `2⁻¹` is isotropic.**  This is the dyadic input to the local
solubility of a quaternary form ramified at `2`. -/
theorem isDiagIsotropic_two_quaternary {a : Fin 4 → ℚ_[2]} (h0 : ‖a 0‖ = 1) (h1 : ‖a 1‖ = 1)
    (h2 : ‖a 2‖ = 1) (h3 : ‖a 3‖ = (2 : ℝ)⁻¹) : IsDiagIsotropic a := by
  have hle : ∀ i, ‖a i‖ ≤ 1 := by
    intro i
    fin_cases i
    · exact le_of_eq h0
    · exact le_of_eq h1
    · exact le_of_eq h2
    · exact h3.le.trans (by norm_num)
  set b : Fin 4 → ℤ_[2] := fun i => ⟨a i, hle i⟩ with hbdef
  have hba : ∀ i, ((b i : ℤ_[2]) : ℚ_[2]) = a i := fun i => rfl
  have hbnorm : ∀ i, ‖b i‖ = ‖a i‖ := fun i => rfl
  have hb0 : IsUnit (b 0) := PadicInt.isUnit_iff.mpr (by rw [hbnorm]; exact h0)
  have hb1 : IsUnit (b 1) := PadicInt.isUnit_iff.mpr (by rw [hbnorm]; exact h1)
  have hb2 : IsUnit (b 2) := PadicInt.isUnit_iff.mpr (by rw [hbnorm]; exact h2)
  have hb3lt : ‖b 3‖ < 1 := by rw [hbnorm, h3]; norm_num
  obtain ⟨w, hwdef⟩ := (PadicInt.norm_lt_one_iff_dvd (b 3)).mp hb3lt
  have hnormp : ‖((2 : ℕ) : ℤ_[2])‖ = (2 : ℝ)⁻¹ := by
    simpa using PadicInt.norm_p (p := 2)
  have hwu : IsUnit w := by
    refine PadicInt.isUnit_iff.mpr ?_
    have hn := hbnorm 3
    rw [hwdef, norm_mul, hnormp, h3] at hn
    refine mul_left_cancel₀ (a := (2 : ℝ)⁻¹) (by norm_num) ?_
    rw [mul_one]
    exact hn
  obtain ⟨x0, x1, x2, x3, hx0, hsum⟩ := exists_sum_eq_zero_four hb0 hb1 hb2 hwu
  refine ⟨fun i => ((![x0, x1, x2, x3] i : ℤ_[2]) : ℚ_[2]), ?_, ?_⟩
  · intro h
    have hz := congrFun h 0
    simp only [Matrix.cons_val_zero, Pi.zero_apply] at hz
    refine hx0 (Subtype.coe_injective ?_)
    simpa using hz
  · have hcast : (((b 0 * x0 ^ 2 + b 1 * x1 ^ 2 + b 2 * x2 ^ 2 + b 3 * x3 ^ 2 : ℤ_[2])) : ℚ_[2])
        = 0 := by
      have hz : (b 0 * x0 ^ 2 + b 1 * x1 ^ 2 + b 2 * x2 ^ 2 + b 3 * x3 ^ 2 : ℤ_[2]) = 0 := by
        rw [hwdef]
        push_cast
        linear_combination hsum
      rw [hz]
      norm_cast
    rw [Fin.sum_univ_four]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
    rw [← hba 0, ← hba 1, ← hba 2, ← hba 3]
    push_cast at hcast ⊢
    linear_combination hcast

end InverseGalois.CFT.Local

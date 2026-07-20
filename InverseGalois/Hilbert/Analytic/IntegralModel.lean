/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Integral Model Construction via Tschirnhaus Substitution

## Main results

- `exists_int_multiple_of_rat_poly`: A polynomial in ℚ[T] can be scaled to have
  integer coefficients.
- `exists_common_denominator`: A bivariate polynomial over ℚ has a common
  denominator for all its coefficients.
- `tschirnhaus_monic`: The Tschirnhaus substitution preserves monicity.
- `tschirnhaus_natDegree`: The Tschirnhaus substitution preserves degree.

## Mathematical background

For `f(T, X) = X^d + a_{d-1}(T)·X^{d-1} + ⋯ + a₀(T)` with `aᵢ ∈ ℚ[T]`, let `D > 0`
be a common denominator such that `D · aᵢ ∈ ℤ[T]` for all `i`. The **Tschirnhaus
substitution** defines:

  `F(T, X) = D^d · f(T, X/D) = X^d + D·a_{d-1}(T)·X^{d-1} + ⋯ + D^d·a₀(T)`

Then `F ∈ ℤ[T][X]` is monic, and for all `t ∈ ℤ`, `F(t, X) ∈ ℤ[X]` is monic.
If `g(X)` is a monic factor of `f(t, X)` of degree `k`, then `D^k · g(X/D)` is a
monic factor of `F(t, X)` of degree `k`. By Gauss's lemma (for monic ℤ-polynomials),
`D^k · g(X/D) ∈ ℤ[X]`.

**Note**: The general Gauss's lemma (monic g divides f → g ∈ ℤ[X]) requires f to be
monic over ℤ. Without the monic hypothesis on f, it is false: e.g., f = 2X² - 1 ∈ ℤ[X]
and g = X² - 1/2 ∈ ℚ[X] is monic with g | f in ℚ[X], but g ∉ ℤ[X]. -/

open Polynomial

noncomputable section

/-!
## Denominator Clearing
-/

/-- For a polynomial `a ∈ ℚ[T]`, there exists `D > 0` such that `D · a ∈ ℤ[T]`. -/
lemma exists_int_multiple_of_rat_poly (a : Polynomial ℚ) :
    ∃ (D : ℕ) (b : Polynomial ℤ), 0 < D ∧
      (D : ℚ) • a = b.map (Int.castRingHom ℚ) := by
  obtain ⟨D, hD⟩ : ∃ D : ℕ, 0 < D ∧ ∀ i ∈ a.support, D * a.coeff i ∈ Set.range (algebraMap ℤ ℚ) := by
    obtain ⟨D, hD⟩ : ∃ D : ℕ, 0 < D ∧ ∀ i ∈ a.support, (a.coeff i).den ∣ D := by
      refine ⟨∏ i ∈ a.support, (a.coeff i |> Rat.den), ?_, ?_⟩
      · exact Finset.prod_pos fun i hi => Nat.cast_pos.mpr (Rat.pos _)
      · exact fun i hi => Finset.dvd_prod_of_mem _ hi
    refine' ⟨D, hD.1, fun i hi => _⟩
    obtain ⟨k, hk⟩ := hD.2 i hi
    use k * (a.coeff i |> Rat.num)
    simp [*, mul_comm, mul_left_comm]
  choose! f hf using hD.2
  use D, ∑ i ∈ a.support, f i • Polynomial.X ^ i
  simp_all only [Polynomial.mem_support_iff, ne_eq, algebraMap_int_eq,
    Int.coe_castRingHom, Set.mem_range, eq_intCast, zsmul_eq_mul, true_and]
  obtain ⟨left, right⟩ := hD
  ext n : 1
  simp_all only [Polynomial.coeff_smul, smul_eq_mul, Polynomial.coeff_map,
    Polynomial.finset_sum_coeff, Polynomial.coeff_intCast_mul, Int.cast_eq,
    Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Polynomial.mem_support_iff, ne_eq, ite_not, eq_intCast, Int.cast_ite,
    Int.cast_zero, not_false_eq_true, right_eq_ite_iff, implies_true]

/-- For a polynomial `f ∈ ℚ[T][X]`, there exists a common denominator `D > 0` such that
`D · (each coefficient) ∈ ℤ[T]`. -/
lemma exists_common_denominator (f : Polynomial (Polynomial ℚ)) :
    ∃ (D : ℕ), 0 < D ∧ ∀ i, ∃ b : Polynomial ℤ,
      (D : ℚ) • f.coeff i = b.map (Int.castRingHom ℚ) := by
  have hD_exists : ∀ i, ∃ D_i : ℕ, 0 < D_i ∧ ∃ b : Polynomial ℤ,
      (D_i : ℚ) • (f.coeff i) = b.map (Int.castRingHom ℚ) := by
    intro i
    obtain ⟨D, b, hD, hb⟩ := exists_int_multiple_of_rat_poly (f.coeff i)
    exact ⟨D, hD, b, hb⟩
  choose D hD_pos b hb using hD_exists
  refine' ⟨∏ i ∈ f.support, D i, Finset.prod_pos _, fun i => _⟩
  · intro i a
    simp_all only [mem_support_iff, ne_eq]
  · by_cases hi : i ∈ f.support <;> simp_all
    · use b i * ∏ j ∈ f.support \ {i}, (D j : ℤ[X])
      simp_all [Finset.prod_eq_prod_diff_singleton_mul (Polynomial.mem_support_iff.mpr hi),
        mul_comm, mul_left_comm, Algebra.smul_def]
      simp [← mul_assoc, ← hb, Polynomial.map_prod]
    · exact ⟨0, by norm_num⟩

/-!
## Gauss's Lemma for Monic Polynomials
-/

/-
**Gauss's Lemma**: A monic factor of a monic ℤ-polynomial has integer coefficients.
If `f ∈ ℤ[X]` is monic and `g ∈ ℚ[X]` is monic with `g | f` in `ℚ[X]`,
then `g ∈ ℤ[X]`.
-/
theorem monic_int_factor_of_monic_int_dvd' {f : Polynomial ℤ} {g : Polynomial ℚ}
    (hf_monic : f.Monic)
    (hg_monic : g.Monic)
    (hg_dvd : g ∣ f.map (Int.castRingHom ℚ)) :
    ∃ g' : Polynomial ℤ, g'.Monic ∧ g'.map (Int.castRingHom ℚ) = g ∧
      g'.natDegree = g.natDegree := by
  have h_int_coeffs : ∀ i, ∃ (ci : ℤ), Polynomial.coeff g i = (ci : ℚ) := by
    intro i
    have := isIntegral_coeff_of_dvd f g hf_monic hg_monic hg_dvd i
    simp_all [IsIntegrallyClosed.isIntegral_iff]
    tauto
  choose ci hci using h_int_coeffs
  refine' ⟨∑ i ∈ g.support, Polynomial.C (ci i) * Polynomial.X ^ i, _, _, _⟩ <;> simp_all [Polynomial.ext_iff]
  · rw [Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some]
    any_goals exact g.natDegree
    · have := hg_monic.coeff_natDegree
      simp_all only [Rat.intCast_eq_one_iff, finset_sum_coeff, coeff_intCast_mul, Int.cast_eq,
        coeff_X_pow, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, mem_support_iff, Int.cast_one,
        ne_eq, one_ne_zero, not_false_eq_true, ↓reduceIte]
    · rw [Polynomial.degree_eq_of_le_of_coeff_ne_zero] <;>
        norm_num [Polynomial.coeff_sum, Polynomial.coeff_X_pow, hci]
      · exact le_trans (Polynomial.degree_sum_le _ _)
          (Finset.sup_le fun i hi => Polynomial.degree_C_mul_X_pow_le _ _ |> le_trans <|
            WithBot.coe_le_coe.mpr <| Polynomial.le_natDegree_of_mem_supp _ hi)
      · have := hg_monic.coeff_natDegree
        simp_all only [Rat.intCast_eq_one_iff, one_ne_zero, not_false_eq_true]
  · rw [Polynomial.natDegree_eq_of_degree_eq_some]
    rw [Polynomial.degree_eq_of_le_of_coeff_ne_zero] <;> norm_num [Polynomial.coeff_sum, hci]
    · exact le_trans (Polynomial.degree_sum_le _ _)
        (Finset.sup_le fun i hi => Polynomial.degree_C_mul_X_pow_le _ _ |> le_trans <|
          WithBot.coe_le_coe.mpr <| Polynomial.le_natDegree_of_mem_supp _ hi)
    · have := hg_monic.coeff_natDegree
      simp_all only [Rat.intCast_eq_one_iff, one_ne_zero, not_false_eq_true]

/-!
## Tschirnhaus Substitution Properties

The rescaling `X ↦ D·X` applied to a polynomial preserves monicity and degree.
-/

/-- Tschirnhaus preserves monicity: if g is monic, so is D^(deg g) · g(X/D). -/
lemma tschirnhaus_monic (g : Polynomial ℚ) (D : ℚ) (hD : D ≠ 0) (hg_monic : g.Monic) :
    (g.comp (Polynomial.C D⁻¹ * Polynomial.X) * Polynomial.C (D ^ g.natDegree)).Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_comp]
  · simp_all only [ne_eq, Monic.leadingCoeff, leadingCoeff_mul, leadingCoeff_C, monic_X, mul_one,
      inv_pow, one_mul, map_pow, leadingCoeff_pow, pow_eq_zero_iff', Monic.natDegree_eq_zero,
      false_and, not_false_eq_true, inv_mul_cancel₀]
  · rw [Polynomial.natDegree_C_mul_X]
    · exact one_ne_zero
    · exact inv_ne_zero hD

/-- Tschirnhaus preserves degree. -/
lemma tschirnhaus_natDegree (g : Polynomial ℚ) (D : ℚ) (hD : D ≠ 0) (hg_monic : g.Monic) :
    (g.comp (Polynomial.C D⁻¹ * Polynomial.X) * Polynomial.C (D ^ g.natDegree)).natDegree =
    g.natDegree := by
  rw [Polynomial.natDegree_mul'] <;> simp_all [Polynomial.natDegree_comp, Polynomial.natDegree_mul']
  rw [Polynomial.comp_eq_zero_iff]
  simp_all only [Polynomial.mul_coeff_zero, Polynomial.coeff_C_zero,
    Polynomial.coeff_X_zero, mul_zero, map_zero, mul_eq_zero, map_eq_zero,
    inv_eq_zero, Polynomial.X_ne_zero, or_self, and_false, or_false]
  apply Aesop.BuiltinRules.not_intro
  intro a
  subst a
  simp_all only [Polynomial.not_monic_zero]

/-
Tschirnhaus preserves divisibility: if g | f, then g_tsch | f_tsch.
-/
lemma tschirnhaus_factor_dvd (f g : Polynomial ℚ) (D : ℚ) (_hD : D ≠ 0)
    (hf_monic : f.Monic) (hg_dvd : g ∣ f) :
    (g.comp (Polynomial.C D⁻¹ * Polynomial.X) * Polynomial.C (D ^ g.natDegree)) ∣
    (f.comp (Polynomial.C D⁻¹ * Polynomial.X) * Polynomial.C (D ^ f.natDegree)) := by
  obtain ⟨q, rfl⟩ := hg_dvd
  have h_deg : Polynomial.natDegree (g * q) = Polynomial.natDegree g + Polynomial.natDegree q := by
    exact Polynomial.natDegree_mul (by aesop_cat) (by aesop_cat)
  simp_all
  exact ⟨q.comp (C D⁻¹ * X) * C D ^ q.natDegree, by ring⟩

end
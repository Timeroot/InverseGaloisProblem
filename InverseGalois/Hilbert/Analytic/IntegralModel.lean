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
  obtain ⟨D, hD_pos, hD_dvd⟩ : ∃ D : ℕ, 0 < D ∧ ∀ i ∈ a.support, (a.coeff i).den ∣ D := by
    refine ⟨∏ i ∈ a.support, (a.coeff i).den, ?_, ?_⟩
    · exact Finset.prod_pos fun i hi ↦ Nat.cast_pos.mpr (Rat.pos _)
    · exact fun i hi ↦ Finset.dvd_prod_of_mem _ hi
  have hD_range : ∀ i ∈ a.support, D * a.coeff i ∈ Set.range (algebraMap ℤ ℚ) := by
    intro i hi
    obtain ⟨k, hk⟩ := hD_dvd i hi
    use k * (a.coeff i).num
    simp [*, mul_comm, mul_left_comm]
  choose! f hf using hD_range
  use D, ∑ i ∈ a.support, f i • X ^ i
  simp_all only [mem_support_iff, ne_eq, algebraMap_int_eq,
    eq_intCast, zsmul_eq_mul, true_and]
  ext n : 1
  simp_all only [coeff_smul, smul_eq_mul, coeff_map,
    finset_sum_coeff, coeff_intCast_mul, Int.cast_eq,
    coeff_X_pow, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    mem_support_iff, ne_eq, ite_not, eq_intCast, Int.cast_ite,
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
  refine ⟨∏ i ∈ f.support, D i, Finset.prod_pos ?_, fun i ↦ ?_⟩
  · intro i a
    simp_all only [mem_support_iff, ne_eq]
  · by_cases hi : i ∈ f.support
    · simp_all
      use b i * ∏ j ∈ f.support \ {i}, (D j : ℤ[X])
      simp_all [Finset.prod_eq_prod_diff_singleton_mul (mem_support_iff.mpr hi),
        mul_comm, mul_left_comm, Algebra.smul_def]
      simp [← mul_assoc, ← hb, Polynomial.map_prod]
    · simp_all
      use 0
      norm_num

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
  have h_int_coeffs : ∀ i, ∃ (ci : ℤ), coeff g i = (ci : ℚ) := by
    intro i
    have := isIntegral_coeff_of_dvd f g hf_monic hg_monic hg_dvd i
    simp only [IsIntegrallyClosed.isIntegral_iff] at this
    tauto
  choose ci hci using h_int_coeffs
  refine ⟨∑ i ∈ g.support, C (ci i) * X ^ i, ?_, ?_, ?_⟩ <;> simp_all [ext_iff]
  · rw [Monic, leadingCoeff, natDegree_eq_of_degree_eq_some]
    any_goals exact g.natDegree
    · have := hg_monic.coeff_natDegree
      simp_all
    · rw [degree_eq_of_le_of_coeff_ne_zero] <;>
        norm_num [coeff_sum, coeff_X_pow, hci]
      · exact le_trans (degree_sum_le _ _)
          (Finset.sup_le fun i hi ↦ le_trans (degree_C_mul_X_pow_le _ _)
            (WithBot.coe_le_coe.mpr (le_natDegree_of_mem_supp _ hi)))
      · have := hg_monic.coeff_natDegree
        simp_all
  · rw [natDegree_eq_of_degree_eq_some]
    rw [degree_eq_of_le_of_coeff_ne_zero] <;> norm_num [coeff_sum, hci]
    · exact le_trans (degree_sum_le _ _)
        (Finset.sup_le fun i hi ↦ le_trans (degree_C_mul_X_pow_le _ _)
          (WithBot.coe_le_coe.mpr (le_natDegree_of_mem_supp _ hi)))
    · have := hg_monic.coeff_natDegree
      simp_all

/-!
## Tschirnhaus Substitution Properties

The rescaling `X ↦ D·X` applied to a polynomial preserves monicity and degree.
-/

/-- Tschirnhaus preserves monicity: if g is monic, so is D^(deg g) · g(X/D). -/
lemma tschirnhaus_monic (g : Polynomial ℚ) (D : ℚ) (hD : D ≠ 0) (hg_monic : g.Monic) :
    (g.comp (Polynomial.C D⁻¹ * Polynomial.X) * Polynomial.C (D ^ g.natDegree)).Monic := by
  rw [Monic, leadingCoeff_mul, leadingCoeff_comp]
  · simp_all
  · rw [natDegree_C_mul_X]
    · exact one_ne_zero
    · exact inv_ne_zero hD

/-- Tschirnhaus preserves degree. -/
lemma tschirnhaus_natDegree (g : Polynomial ℚ) (D : ℚ) (hD : D ≠ 0) (hg_monic : g.Monic) :
    (g.comp (Polynomial.C D⁻¹ * Polynomial.X) * Polynomial.C (D ^ g.natDegree)).natDegree =
    g.natDegree := by
  rw [natDegree_mul']
  · simp_all [natDegree_comp, natDegree_mul']
  · simp_all
    rw [comp_eq_zero_iff]
    simp_all only [mul_coeff_zero, coeff_C_zero,
      coeff_X_zero, mul_zero, map_zero, mul_eq_zero, map_eq_zero,
      inv_eq_zero, X_ne_zero, or_self, and_false, or_false]
    intro a
    subst a
    simp_all [not_monic_zero]

/-
Tschirnhaus preserves divisibility: if g | f, then g_tsch | f_tsch.
-/
lemma tschirnhaus_factor_dvd (f g : Polynomial ℚ) (D : ℚ) (_hD : D ≠ 0)
    (hf_monic : f.Monic) (hg_dvd : g ∣ f) :
    (g.comp (Polynomial.C D⁻¹ * Polynomial.X) * Polynomial.C (D ^ g.natDegree)) ∣
    (f.comp (Polynomial.C D⁻¹ * Polynomial.X) * Polynomial.C (D ^ f.natDegree)) := by
  obtain ⟨q, rfl⟩ := hg_dvd
  have h_deg : natDegree (g * q) = natDegree g + natDegree q :=
    natDegree_mul (by simp_all only [ne_eq]; apply Aesop.BuiltinRules.not_intro; intro a; subst a; simp_all only [zero_mul, not_monic_zero]) (by simp_all only [ne_eq]; apply Aesop.BuiltinRules.not_intro; intro a; subst a; simp_all only [mul_zero, not_monic_zero])
  simp_all
  use q.comp (C D⁻¹ * X) * C D ^ q.natDegree
  ring

end
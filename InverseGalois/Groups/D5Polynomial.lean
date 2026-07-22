import Mathlib
import InverseGalois.Polynomial.QuinticDiscriminant

/-!
# Polynomial, discriminant, and root facts for the D₅ inverse Galois proof

This file studies the witness polynomial `X⁵ - 5X + 12`: irreducibility, separability,
root enumeration, its square discriminant, and the existence of a non-real root. Pure
finite-group facts are kept in `D5GroupFacts.lean`.
-/

open Polynomial Finset Matrix

noncomputable section

set_option maxHeartbeats 800000

/-!
## Gram matrix for X⁵ - 5X + 12

Power sums: p₀=5, p₁=p₂=p₃=0, p₄=20, p₅=-60, p₆=p₇=0, p₈=100
Gram determinant = 8000²
-/

/-
The Gram matrix determinant for the power sums of X⁵ - 5X + 12 is 8000².
-/
lemma gram_det_value_d5 (r : Fin 5 → K) [Field K]
    (hp1 : ∑ i : Fin 5, r i ^ 1 = 0)
    (hp2 : ∑ i : Fin 5, r i ^ 2 = 0)
    (hp3 : ∑ i : Fin 5, r i ^ 3 = 0)
    (hp4 : ∑ i : Fin 5, r i ^ 4 = (20 : K))
    (hp5 : ∑ i : Fin 5, r i ^ 5 = (-60 : K))
    (hp6 : ∑ i : Fin 5, r i ^ 6 = 0)
    (hp7 : ∑ i : Fin 5, r i ^ 7 = 0)
    (hp8 : ∑ i : Fin 5, r i ^ 8 = (100 : K)) :
    (gramMatrixOfPowerSums (fun k => ∑ i : Fin 5, r i ^ k)).det =
    (8000 : K) ^ 2 := by
      simp [gramMatrixOfPowerSums, Matrix.det_succ_row_zero]
      simp [Fin.sum_univ_succ, Fin.succAbove]
      simp_all [Fin.sum_univ_five]
      simp_all [← eq_sub_iff_add_eq']
      grind +ring

/-!
## Discriminant of X⁵ - 5X + 12 is 8000²
-/

abbrev f_d5 : ℚ[X] := X ^ 5 - C 5 * X + C 12

lemma f_d5_ne_zero : f_d5 ≠ 0 :=
  ne_of_apply_ne (Polynomial.eval 0) (by norm_num [f_d5])

lemma f_d5_natDegree : f_d5.natDegree = 5 := by
  erw [Polynomial.natDegree_add_C, Polynomial.natDegree_add_eq_left_of_natDegree_lt] <;> norm_num

lemma f_d5_irreducible : Irreducible f_d5 := by
  -- Eisenstein at p=5 after shift X → X-2 (same proof as in D5.lean)
  -- Apply Eisenstein's criterion with p=5 to the shifted polynomial.
  have h_eisenstein : Irreducible
      (Polynomial.X ^ 5 - 10 * Polynomial.X ^ 4 + 40 * Polynomial.X ^ 3
        - 80 * Polynomial.X ^ 2 + 75 * Polynomial.X - 10 : Polynomial ℤ) := by
    apply Polynomial.irreducible_of_eisenstein_criterion
    any_goals exact Ideal.span { 5 }
    any_goals erw [Ideal.span_singleton_prime]
    all_goals norm_num [Ideal.mem_span_singleton, Ideal.span_singleton_pow]
    · erw [Polynomial.leadingCoeff, Polynomial.natDegree_sub_C]
      norm_num [Polynomial.natDegree_add_eq_left_of_natDegree_lt,
        Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
      norm_num [Polynomial.coeff_X]
    · intro n hn
      erw [Polynomial.natDegree_sub_C] at hn
      norm_num [Polynomial.natDegree_add_eq_left_of_natDegree_lt,
        Polynomial.natDegree_sub_eq_left_of_natDegree_lt] at hn
      interval_cases n <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
    · ring_nf
      repeat (first | erw [Polynomial.degree_add_eq_right_of_degree_lt] | erw [Polynomial.degree_C]) <;> norm_num
    · apply Polynomial.Monic.isPrimitive
      rw [Polynomial.Monic, Polynomial.leadingCoeff]
      norm_num [Polynomial.coeff_X, Polynomial.natDegree_add_eq_left_of_natDegree_lt,
        Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
  -- Since `f(X-2)` is irreducible over ℤ, it is also irreducible over ℚ.
  have h_irred_Q_map : Irreducible (Polynomial.map (algebraMap ℤ ℚ)
      (Polynomial.X ^ 5 - 10 * Polynomial.X ^ 4 + 40 * Polynomial.X ^ 3
        - 80 * Polynomial.X ^ 2 + 75 * Polynomial.X - 10 : Polynomial ℤ)) := by
    -- Since the polynomial is primitive, we can apply Gauss's Lemma to conclude that it is irreducible over ℚ.
    have h_primitive : Polynomial.IsPrimitive
        (Polynomial.X ^ 5 - 10 * Polynomial.X ^ 4 + 40 * Polynomial.X ^ 3
          - 80 * Polynomial.X ^ 2 + 75 * Polynomial.X - 10 : Polynomial ℤ) := by
      intro p
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      norm_num
      intro h
      specialize h 5
      norm_num [Polynomial.coeff_one, Polynomial.coeff_X] at h
      exact isUnit_of_dvd_one h
    grind only [IsPrimitive.irreducible_iff_irreducible_map_fraction_map]
  -- Since `f(X-2)` is irreducible over ℚ, it follows that `f(X)` is also irreducible over ℚ.
  have h_irred_Q : Irreducible (f_d5.comp (Polynomial.X - 2) : Polynomial ℚ) := by
    convert h_irred_Q_map using 1
    norm_num [f_d5]
    ring_nf
    apply Polynomial.funext
    intro x
    norm_num
    ring
  rw [irreducible_iff] at *
  constructor
  · intro h
    refine absurd (Polynomial.degree_eq_zero_of_isUnit h) ?_
    erw [Polynomial.degree_add_C] <;>
      repeat (first | erw [Polynomial.degree_add_eq_left_of_degree_lt] | simp)
  · intro a b hab
    have := @h_irred_Q.2 (a.comp (Polynomial.X - 2)) (b.comp (Polynomial.X - 2))
    simp_all
    contrapose! h_irred_Q
    have key : ∀ p : ℚ[X], ¬IsUnit p → ¬IsUnit (p.comp (Polynomial.X - 2)) := by
      intro p hp h
      have hp0 : p ≠ 0 := by rintro rfl; simp at h
      refine hp (Polynomial.isUnit_iff_degree_eq_zero.mpr ?_)
      rw [Polynomial.degree_eq_natDegree hp0]
      have hd := Polynomial.degree_eq_zero_of_isUnit h
      rw [Polynomial.degree_eq_natDegree h.ne_zero, Polynomial.natDegree_comp] at hd
      erw [Polynomial.natDegree_X_sub_C, mul_one] at hd
      exact hd
    intro _
    exact ⟨a.comp (Polynomial.X - 2), b.comp (Polynomial.X - 2), rfl,
      key a h_irred_Q.1, key b h_irred_Q.2⟩

lemma f_d5_separable : f_d5.Separable := f_d5_irreducible.separable

lemma rootSet_card_d5 :
    Fintype.card (f_d5.rootSet f_d5.SplittingField) = 5 := by
  rw [Polynomial.card_rootSet_eq_natDegree f_d5_separable
    (SplittingField.splits f_d5), f_d5_natDegree]

-- A bijection Fin 5 ≃ rootSet
def rootEnum_d5 : Fin 5 ≃ (f_d5.rootSet f_d5.SplittingField) :=
  Fintype.equivFinOfCardEq rootSet_card_d5 |>.symm

/-
The discriminant: ∏_{i<j}(r_j - r_i)² = 8000² in the splitting field
-/
lemma disc_value_d5 (v : Fin 5 ≃ (f_d5.rootSet f_d5.SplittingField)) :
    (∏ i : Fin 5, ∏ j ∈ Ioi i,
      ((v j : f_d5.SplittingField) - (v i : f_d5.SplittingField))) ^ 2 =
    algebraMap ℚ _ (8000 ^ 2) := by
      have h_factor : (Polynomial.map (algebraMap ℚ (f_d5.SplittingField)) f_d5) =
          Finset.prod Finset.univ fun i ↦ Polynomial.X - Polynomial.C (v i : f_d5.SplittingField) := by
        convert Polynomial.Splits.eq_prod_roots _
        any_goals try infer_instance
        · rw [show (Polynomial.map (algebraMap ℚ f_d5.SplittingField) f_d5).roots =
                Multiset.map (fun x : f_d5.rootSet f_d5.SplittingField ↦ (x : f_d5.SplittingField))
                  (Multiset.map (fun x : Fin 5 ↦ (v x : f_d5.rootSet f_d5.SplittingField))
                    Finset.univ.val) from ?_]
          · erw [Polynomial.leadingCoeff_map, Polynomial.leadingCoeff, Polynomial.natDegree_add_C,
              Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> norm_num [f_d5]
            conv_rhs => rw [← Equiv.prod_comp v]
          · have hv : (f_d5.map (algebraMap ℚ (f_d5.SplittingField))).roots =
                Multiset.map (fun x ↦ (x : f_d5.SplittingField))
                  (f_d5.rootSet f_d5.SplittingField).toFinset.val := by
              have h_distinct : Multiset.Nodup (Polynomial.map (algebraMap ℚ (f_d5.SplittingField)) f_d5).roots := by
                convert Polynomial.nodup_roots _
                exact Polynomial.Separable.map f_d5_separable
              norm_num at *
              unfold Polynomial.rootSet
              norm_num [Polynomial.aroots_def]
              grind only [Multiset.dedup_eq_self]
            simp_all only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow, map_X, Polynomial.map_mul, map_C,
              eq_ratCast, Rat.cast_ofNat, Multiset.map_id', Multiset.map_univ_val_equiv]
            rfl
        · exact Polynomial.SplittingField.splits _
      have h_power_sums : ∑ i : Fin 5, (v i : f_d5.SplittingField) ^ 0 = 5
          ∧ ∑ i : Fin 5, (v i : f_d5.SplittingField) ^ 1 = 0
          ∧ ∑ i : Fin 5, (v i : f_d5.SplittingField) ^ 2 = 0
          ∧ ∑ i : Fin 5, (v i : f_d5.SplittingField) ^ 3 = 0
          ∧ ∑ i : Fin 5, (v i : f_d5.SplittingField) ^ 4 = 20 := by
        simp_all [Fin.prod_univ_five]
        simp_all [Fin.sum_univ_five]
        have h₁ := congr_arg (Polynomial.eval 0) h_factor
        have h₂ := congr_arg (Polynomial.eval 1) h_factor
        have h₃ := congr_arg (Polynomial.eval (-1)) h_factor
        have h₄ := congr_arg (Polynomial.eval (-2)) h_factor
        have h₅ := congr_arg (Polynomial.eval 2) h_factor
        norm_num at h₁ h₂ h₃ h₄ h₅
        grind +ring
      have h_power_sums_5 : ∑ i : Fin 5, (v i : f_d5.SplittingField) ^ 5 = -60 := by
        have h_pow5_each : ∀ i : Fin 5, (v i : f_d5.SplittingField) ^ 5 = 5 * (v i : f_d5.SplittingField) - 12 := by
          intro i
          have h_root : (v i : f_d5.SplittingField) ^ 5 - 5 * (v i : f_d5.SplittingField) + 12 = 0 := by
            replace h_factor :=
              congr_arg (Polynomial.eval (v i : f_d5.SplittingField)) h_factor
            simp_all [Finset.prod_eq_prod_diff_singleton_mul (Finset.mem_univ i)]
          linear_combination' h_root
        simp_all
        rw [← Finset.mul_sum, h_power_sums.1]
        norm_num
      have h_power_sums_6 : ∑ i : Fin 5, (v i : f_d5.SplittingField) ^ 6 = 0 := by
        simp_all [Fin.sum_univ_five, pow_succ']
        grind
      have h_power_sums_7 : ∑ i : Fin 5, (v i : f_d5.SplittingField) ^ 7 = 0 := by
        have h_pow7_each : ∀ i : Fin 5, (v i : f_d5.SplittingField) ^ 7 =
            5 * (v i : f_d5.SplittingField) ^ 3 - 12 * (v i : f_d5.SplittingField) ^ 2 := by
          intro i
          have h_root : (v i : f_d5.SplittingField) ^ 5 - 5 * (v i : f_d5.SplittingField) + 12 = 0 := by
            replace h_factor :=
              congr_arg (Polynomial.eval (v i : f_d5.SplittingField)) h_factor
            simp_all [Finset.prod_eq_prod_diff_singleton_mul (Finset.mem_univ i)]
          linear_combination' h_root * (v i : f_d5.SplittingField) ^ 2
        simp_all [← Finset.mul_sum]
      have h_power_sums_8 : ∑ i : Fin 5, (v i : f_d5.SplittingField) ^ 8 = 100 := by
        simp_all [Fin.sum_univ_five, pow_succ']
        grind +ring
      convert gram_det_value_d5 (fun i ↦ (v i : f_d5.SplittingField)) _ _ _ _ _ _ _ _ using 1 <;>
        norm_num [h_power_sums, h_power_sums_5, h_power_sums_6, h_power_sums_7, h_power_sums_8]
      · rw [← vandermonde_det_sq, Matrix.det_vandermonde]
      · simpa using h_power_sums.2.1

/-- The discriminant element is nonzero. -/
lemma disc_elem_ne_zero_d5 (v : Fin 5 ≃ (f_d5.rootSet f_d5.SplittingField)) :
    (∏ i : Fin 5, ∏ j ∈ Ioi i,
      ((v j : f_d5.SplittingField) - (v i : f_d5.SplittingField))) ≠ 0 := by
  simp [Finset.prod_eq_zero_iff, sub_eq_zero]
  exact fun i j hij ↦ v.injective.ne hij.ne'


end

/-! ## Non-real roots -/

/-
`X⁵ − 5X + 12` has a non-real complex root.

The derivative `5X⁴ − 5 = 5(X⁴−1)` has exactly the two real roots `±1`, so by
`Polynomial.card_rootSet_le_derivative` the polynomial has at most three distinct real
roots.  Over `ℂ` the separable quintic has five distinct roots, so at least one is
non-real.
-/
lemma f_d5_nonreal_root :
    ∃ z : ℂ, (Polynomial.aeval z) f_d5 = 0 ∧ z.im ≠ 0 := by
  by_contra! h
  -- If all roots of `f_d5` were real, then `f_d5` would have 5 distinct real roots.
  have h_real_roots : Fintype.card (f_d5.rootSet ℂ) ≤ Fintype.card (f_d5.rootSet ℝ) := by
    -- If all roots of `f_d5` were real, then the roots in ℂ would be in bijection with the roots in ℝ.
    have h_bij : (f_d5.rootSet ℂ).toFinset ⊆ Finset.image (fun x : ℝ ↦ x : ℝ → ℂ) (f_d5.rootSet ℝ).toFinset := by
      simp_all [Finset.subset_iff, Polynomial.mem_rootSet]
      intro z _ h2
      refine ⟨z.re, ?_, ?_⟩
      · simpa [Complex.ext_iff, pow_succ, h z h2] using h2
      · simp [Complex.ext_iff, h z h2]
    have := Finset.card_le_card h_bij
    simp_all [Finset.card_image_of_injective, Function.Injective]
  -- However, `f_d5` has at most 3 distinct real roots.
  have h_real_roots_card : Fintype.card (f_d5.rootSet ℝ) ≤ 3 := by
    refine le_trans (Polynomial.card_rootSet_le_derivative f_d5) ?_
    rw [Fintype.card_ofFinset]
    · refine Nat.succ_le_of_lt (lt_of_le_of_lt (Finset.card_le_card (t := {1, -1}) ?_) ?_)
      · norm_num [Finset.subset_iff, f_d5]
        intro x _ hx
        refine eq_or_eq_neg_of_sq_eq_sq _ _ ?_
        nlinarith
      · norm_num
    · simp [Polynomial.rootSet_def]
  have h_complex_roots_card : Fintype.card (f_d5.rootSet ℂ) = 5 := by
    convert Polynomial.card_rootSet_eq_natDegree f_d5_separable (IsAlgClosed.splits _) using 1
    · erw [Polynomial.natDegree_add_C, Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> norm_num
    · infer_instance
  linarith

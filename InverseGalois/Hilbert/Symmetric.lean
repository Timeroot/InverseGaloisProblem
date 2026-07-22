/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Core.Basic
import InverseGalois.Core.Cyclic
import InverseGalois.Groups.S3
import InverseGalois.Groups.S4
import InverseGalois.Hilbert.GaloisAction
import InverseGalois.Hilbert.SymmetricViaHIT

/-!
# All Symmetric Groups are Inverse Galois Groups

We show that `Sₙ = Equiv.Perm (Fin n)` is an inverse Galois group for every `n`.
-/

open Polynomial IntermediateField

noncomputable section

namespace IsInverseGalois

/-- `S₀ = Equiv.Perm (Fin 0)` is the trivial group, hence inverse Galois. -/
theorem perm_fin_zero : IsInverseGalois (Equiv.Perm (Fin 0)) :=
  unit.of_mulEquiv MulEquiv.ofUnique.symm

/-- `S₁ = Equiv.Perm (Fin 1)` is the trivial group, hence inverse Galois. -/
theorem perm_fin_one : IsInverseGalois (Equiv.Perm (Fin 1)) :=
  unit.of_mulEquiv MulEquiv.ofUnique.symm

/-- `S₂ = Equiv.Perm (Fin 2)` is cyclic of order 2, hence inverse Galois. -/
theorem perm_fin_two : IsInverseGalois (Equiv.Perm (Fin 2)) := by
  have : IsCyclic (Equiv.Perm (Fin 2)) := by
    apply isCyclic_of_prime_card (p := 2)
    simp [Nat.card_eq_fintype_card, Fintype.card_perm]
  exact of_isCyclic _

-- `perm_fin_three` is proved in `S3.lean`

/-!
### S₅ via the prime degree criterion

We realize `S₅` as the Galois group of `q₅ = X⁵ - 4X + 2` over `ℚ`.
-/

private def q₅ : ℚ[X] := X ^ 5 - C 4 * X + C 2

private lemma q₅_irreducible : Irreducible q₅ := by
  -- Apply Eisenstein's criterion with p=2 to conclude that q₅ is irreducible over ℤ.
  have h_eisenstein_int : Irreducible (Polynomial.X ^ 5 - 4 * Polynomial.X + 2 : Polynomial ℤ) := by
    apply Polynomial.irreducible_of_eisenstein_criterion
    any_goals exact Ideal.span { 2 }
    any_goals erw [Polynomial.degree_add_C] <;> erw [Polynomial.degree_sub_eq_left_of_degree_lt] <;> norm_num
    any_goals erw [Polynomial.degree_C] <;> norm_num
    · have h2 : (2 : ℤ) ≠ 0 := by norm_num
      rw [Ideal.span_singleton_prime h2]
      norm_num
    · erw [Polynomial.leadingCoeff, Polynomial.natDegree_add_C,
        Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;>
        norm_num [Ideal.mem_span_singleton]
      norm_num [Polynomial.coeff_X]
    · intro n hn
      interval_cases n <;> norm_num [Polynomial.coeff_X, Polynomial.coeff_C, Ideal.mem_span_singleton]
    · norm_num [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    · apply Polynomial.Monic.isPrimitive
      erw [Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_add_C,
        Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> norm_num [Polynomial.coeff_X]
  convert h_eisenstein_int
  constructor
  · grind only
  · intro h_irred_int
    have h_irred_rat : Irreducible (Polynomial.map (Int.castRingHom ℚ)
        (Polynomial.X ^ 5 - 4 * Polynomial.X + 2 : Polynomial ℤ)) := by
      -- Since the polynomial is primitive, we can apply Gauss's Lemma to conclude that it is irreducible over ℚ.
      have h_primitive : Polynomial.IsPrimitive
          (Polynomial.X ^ 5 - 4 * Polynomial.X + 2 : Polynomial ℤ) := by
        apply Polynomial.Monic.isPrimitive
        erw [Polynomial.Monic, Polynomial.leadingCoeff]
        erw [Polynomial.natDegree_add_C, Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;>
          norm_num [Polynomial.coeff_X]
      exact (IsPrimitive.Int.irreducible_iff_irreducible_map_cast h_primitive).mp h_eisenstein_int
    convert h_irred_rat using 1
    norm_num [q₅]
    rfl

private lemma q₅_natDegree : q₅.natDegree = 5 := by
  erw [Polynomial.natDegree_add_C, Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> norm_num

private lemma q₅_roots_card :
    Fintype.card (q₅.rootSet ℂ) = Fintype.card (q₅.rootSet ℝ) + 2 := by
      have h_real_roots : ∃ x ∈ Set.Ioo (-2 : ℝ) (-1), x^5 - 4 * x + 2 = 0 := by
        apply intermediate_value_Ioo <;> norm_num
        fun_prop
      have h_real_roots2 : ∃ y ∈ Set.Ioo (0 : ℝ) (1), y^5 - 4 * y + 2 = 0 := by
        apply intermediate_value_Ioo' <;> norm_num
        fun_prop
      have h_real_roots3 : ∃ z ∈ Set.Ioo (1 : ℝ) (2), z^5 - 4 * z + 2 = 0 := by
        apply intermediate_value_Ioo <;> norm_num
        fun_prop
      obtain ⟨x, hx⟩ := h_real_roots
      obtain ⟨y, hy⟩ := h_real_roots2
      obtain ⟨z, hz⟩ := h_real_roots3
      have h_real_roots_le : (q₅.map (algebraMap ℚ ℝ)).roots.toFinset.card ≤ 3 := by
        -- Since `q₅'` has exactly 2 real roots, `q₅` can have at most 3 real roots.
        have h_deriv_roots : (Polynomial.derivative (q₅.map (algebraMap ℚ ℝ))).roots.toFinset.card ≤ 2 := by
          unfold q₅
          norm_num [Polynomial.derivative_pow]
          ring_nf
          refine le_trans (Finset.card_le_card
              (t := { Real.sqrt (Real.sqrt (4 / 5)), -Real.sqrt (Real.sqrt (4 / 5)) }) ?_) ?_
          · intro x hx
            simp_all [sub_eq_iff_eq_add]
            apply eq_or_eq_neg_of_sq_eq_sq
            ring_nf
            norm_num [Real.sqrt_nonneg]
            have := Real.sqrt_nonneg 5
            have := Real.sq_sqrt (show 0 ≤ 5 by norm_num)
            have := inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (show 0 < 5 by norm_num)))
            rw [← sq_eq_sq₀] <;> ring_nf <;> norm_num <;> nlinarith
          · exact Finset.card_insert_le _ _
        refine le_trans (card_roots_toFinset_le_derivative _) ?_
        linarith
      have h_real_roots_count : (q₅.map (algebraMap ℚ ℝ)).roots.toFinset.card = 3 := by
        refine le_antisymm h_real_roots_le (Finset.two_lt_card.mpr ?_)
        norm_num [q₅] at *
        refine ⟨x, ⟨?_, hx.2⟩, y, ⟨?_, hy.2⟩, z, ⟨?_, hz.2⟩, ?_, ?_, ?_⟩
        · exact ne_of_apply_ne (Polynomial.eval 0) (by norm_num)
        · exact ne_of_apply_ne (Polynomial.eval 0) (by norm_num)
        · exact ne_of_apply_ne (Polynomial.eval 0) (by norm_num)
        · linarith
        · linarith
        · linarith
      have h_complex_roots_count : (q₅.map (algebraMap ℚ ℂ)).roots.toFinset.card = 5 := by
        rw [Multiset.toFinset_card_of_nodup]
        · have h_splits : (q₅.map (algebraMap ℚ ℂ)).Splits := IsAlgClosed.splits _
          rw [← h_splits.natDegree_eq_card_roots, Polynomial.natDegree_map, q₅_natDegree]
        · exact Polynomial.nodup_roots (Polynomial.Separable.map q₅_irreducible.separable)
      simp_all [Polynomial.rootSet_def]

/-- `S₅ = Equiv.Perm (Fin 5)` is an inverse Galois group. -/
theorem perm_fin_five : IsInverseGalois (Equiv.Perm (Fin 5)) := by
  have h_galois : Nonempty (Polynomial.Gal q₅ ≃* Equiv.Perm (q₅.rootSet ℂ)) :=
    ⟨MulEquiv.ofBijective _
      (Polynomial.Gal.galActionHom_bijective_of_prime_degree q₅_irreducible
        (by norm_num [q₅_natDegree]) q₅_roots_card)⟩
  have h_card : Fintype.card (q₅.rootSet ℂ) = 5 := by
    have := @Polynomial.card_rootSet_eq_natDegree ℚ _ ℂ _ _ q₅
      q₅_irreducible.separable (IsAlgClosed.splits _)
    rwa [q₅_natDegree] at this
  have h_perm_iso : Nonempty (Equiv.Perm (q₅.rootSet ℂ) ≃* Equiv.Perm (Fin 5)) :=
    ⟨{ Equiv.permCongr (Fintype.equivOfCardEq h_card) with
       map_mul' := by
         intro σ τ
         ext
         simp [Equiv.permCongr] }⟩
  exact ⟨q₅.SplittingField, inferInstance, inferInstance, inferInstance,
    { to_isSeparable := Algebra.IsAlgebraic.isSeparable_of_perfectField,
      to_normal := SplittingField.instNormal q₅ },
    ⟨h_galois.some.trans h_perm_iso.some⟩⟩

end IsInverseGalois

end

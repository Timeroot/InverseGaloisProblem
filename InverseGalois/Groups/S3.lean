/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Core.Basic

/-!
# S₃ is an Inverse Galois Group

We show that the symmetric group `S₃ = Equiv.Perm (Fin 3)` is an inverse Galois group over `ℚ`,
by showing that the Galois group of `x³ - 2` over `ℚ` is isomorphic to `S₃`.

## Strategy

The polynomial `p = X³ - 2` is irreducible over `ℚ` (by Eisenstein at 2), has degree 3 (prime),
and has exactly one real root and two complex conjugate roots. By
`Gal.galActionHom_bijective_of_prime_degree`, the Galois action on the roots gives
an isomorphism `Gal(p) ≅ Equiv.Perm (rootSet p ℂ) ≅ S₃`.

## Main results

* `IsInverseGalois.perm_fin_three`: `Equiv.Perm (Fin 3)` is an inverse Galois group.
-/

open Polynomial IntermediateField

noncomputable section

/-- The polynomial `X³ - 2` over `ℚ`. -/
private def p : ℚ[X] := X ^ 3 - C 2

private lemma p_irreducible : Irreducible p := by
  -- We can apply Eisenstein's criterion with the prime number 2.
  have h_eisenstein : Irreducible (X ^ 3 - 2 : Polynomial ℤ) := by
    apply irreducible_of_eisenstein_criterion
    any_goals erw [degree_X_pow_sub_C] <;> norm_num
    any_goals exact Ideal.span { 2 }
    · norm_num [Ideal.span_singleton_prime]
    · erw [leadingCoeff_X_pow_sub_C] <;> norm_num [Ideal.mem_span_singleton]
    · intro n hn
      interval_cases n <;>
        norm_num [coeff_one, coeff_X, Ideal.mem_span_singleton]
    · simp [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    · exact (monic_X_pow_sub_C _ (by norm_num)).isPrimitive
  have h_gauss : Irreducible (map (Int.castRingHom ℚ) (X ^ 3 - 2 : Polynomial ℤ)) := by
    have h_primitive : IsPrimitive (X ^ 3 - 2 : Polynomial ℤ) :=
      (monic_X_pow_sub_C _ (by norm_num)).isPrimitive
    grind only [IsPrimitive.Int.irreducible_iff_irreducible_map_cast]
  simpa using h_gauss

private lemma p_natDegree : p.natDegree = 3 := by
  rw [p, natDegree_X_pow_sub_C]

private lemma p_roots_card :
    Fintype.card (p.rootSet ℂ) = Fintype.card (p.rootSet ℝ) + 2 := by
  -- The polynomial `p = X³ - 2` has exactly one real root and two complex roots.
  have h_real_root : Fintype.card (p.rootSet ℝ) = 1 := by
    simp [p, rootSet_def]
    rw [Finset.card_eq_one]
    use 2 ^ (1 / 3 : ℝ)
    ext a
    norm_num [ext_iff]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rw [sub_eq_zero] at h
      have ha : (0 : ℝ) ≤ a := by nlinarith [sq_nonneg a, h.2]
      rw [← h.2, ← Real.rpow_natCast, ← Real.rpow_mul ha]
      norm_num
    · refine ⟨⟨0, by norm_num⟩, ?_⟩
      rw [h, ← Real.rpow_natCast, ← Real.rpow_mul] <;> norm_num
  have h_complex_roots : Fintype.card (p.rootSet ℂ) = 3 := by
    convert card_rootSet_eq_natDegree _ _
    · rw [p, natDegree_X_pow_sub_C]
    · exact p_irreducible.separable
    · exact IsAlgClosed.splits _
  simp [h_real_root, h_complex_roots]

/-
`Equiv.Perm (Fin 3) ≅ S₃` is an inverse Galois group over `ℚ`, realized by the
splitting field of `X³ - 2`.
-/
theorem IsInverseGalois.perm_fin_three : IsInverseGalois (Equiv.Perm (Fin 3)) := by
  -- The Galois group of `p` is isomorphic to `S₃`.
  have h_galois : Nonempty (Gal p ≃* Equiv.Perm (rootSet p ℂ)) := by
    refine ⟨MulEquiv.ofBijective _
      (Gal.galActionHom_bijective_of_prime_degree p_irreducible ?_ p_roots_card)⟩
    norm_num [p_natDegree]
  -- Since `p` is a cubic polynomial, its root set has cardinality 3.
  have h_card : Fintype.card (rootSet p ℂ) = 3 := by
    convert card_rootSet_eq_natDegree _ _
    · rw [p, natDegree_X_pow_sub_C]
    · exact p_irreducible.separable
    · exact IsAlgClosed.splits _
  -- Since the root set has cardinality 3, `Equiv.Perm (rootSet p ℂ)` is isomorphic to
  -- `Equiv.Perm (Fin 3)`.
  have h_perm_iso : Nonempty (Equiv.Perm (rootSet p ℂ) ≃* Equiv.Perm (Fin 3)) := by
    constructor
    refine' { Equiv.permCongr (Fintype.equivOfCardEq h_card) with .. }
    aesop_cat
  refine ⟨p.SplittingField, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try infer_instance
  · exact
      { to_isSeparable := Algebra.IsAlgebraic.isSeparable_of_perfectField,
        to_normal := SplittingField.instNormal p }
  -- Combining the isomorphisms, `Gal(p)` is isomorphic to `S₃`.
  · exact ⟨h_galois.some.trans h_perm_iso.some⟩

end

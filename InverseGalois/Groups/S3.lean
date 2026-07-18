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
`Polynomial.Gal.galActionHom_bijective_of_prime_degree`, the Galois action on the roots gives
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
  have h_eisenstein : Irreducible (Polynomial.X ^ 3 - 2 : Polynomial ℤ) := by
    apply Polynomial.irreducible_of_eisenstein_criterion;
    any_goals erw [ Polynomial.degree_X_pow_sub_C ] <;> norm_num;
    any_goals exact Ideal.span { 2 };
    · norm_num [ Ideal.span_singleton_prime ];
    · erw [ Polynomial.leadingCoeff_X_pow_sub_C ] <;> norm_num [ Ideal.mem_span_singleton ];
    · intro n hn; interval_cases n <;> norm_num [ Polynomial.coeff_one, Polynomial.coeff_X, Ideal.mem_span_singleton ] ;
    · simp [ Ideal.span_singleton_pow, Ideal.mem_span_singleton ];
    · exact Polynomial.Monic.isPrimitive ( Polynomial.monic_X_pow_sub_C _ ( by norm_num ) );
  have h_gauss : Irreducible (Polynomial.map (Int.castRingHom ℚ) (Polynomial.X ^ 3 - 2 : Polynomial ℤ)) := by
    have h_primitive : Polynomial.IsPrimitive (Polynomial.X ^ 3 - 2 : Polynomial ℤ) := by
      exact Polynomial.Monic.isPrimitive ( Polynomial.monic_X_pow_sub_C _ ( by norm_num ) )
    grind only [IsPrimitive.Int.irreducible_iff_irreducible_map_cast];
  aesop

private lemma p_natDegree : p.natDegree = 3 := by
  erw [ Polynomial.natDegree_X_pow_sub_C ]

private lemma p_roots_card :
    Fintype.card (p.rootSet ℂ) = Fintype.card (p.rootSet ℝ) + 2 := by
  -- The polynomial $p = X^3 - 2$ has exactly one real root and two complex roots.
  have h_real_root : Fintype.card (p.rootSet ℝ) = 1 := by
    simp [ p, Polynomial.rootSet_def ];
    rw [ Finset.card_eq_one ];
    use 2 ^ (1 / 3 : ℝ);
    ext;
    norm_num [ Polynomial.ext_iff ];
    exact ⟨ fun h => by rw [ sub_eq_zero ] at h; rw [ ← h.2 ] ; rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by nlinarith [ sq_nonneg ( ‹_› : ℝ ) ] ) ] ; norm_num, fun h => ⟨ ⟨ 0, by norm_num ⟩, by rw [ h ] ; rw [ ← Real.rpow_natCast, ← Real.rpow_mul ] <;> norm_num ⟩ ⟩
  have h_complex_roots : Fintype.card (p.rootSet ℂ) = 3 := by
    convert Polynomial.card_rootSet_eq_natDegree _ _;
    · erw [ Polynomial.natDegree_X_pow_sub_C ];
    · exact p_irreducible.separable;
    · exact IsAlgClosed.splits_codomain _
  simp [h_real_root, h_complex_roots] at *

/-
`Equiv.Perm (Fin 3) ≅ S₃` is an inverse Galois group over `ℚ`, realized by the
splitting field of `X³ - 2`.
-/
theorem IsInverseGalois.perm_fin_three : IsInverseGalois (Equiv.Perm (Fin 3)) := by
  -- By definition of $p$, we know that its Galois group � is� isomorphic to $S_3$.
  have h_galois : Nonempty (Polynomial.Gal p ≃* Equiv.Perm (Polynomial.rootSet p ℂ)) := by
    refine' ⟨ _ ⟩;
    have := @Polynomial.Gal.galActionHom_bijective_of_prime_degree;
    exact MulEquiv.ofBijective _ ( this p_irreducible ( by norm_num [ p_natDegree ] ) p_roots_card );
  -- Since $p$ � is� a cubic polynomial, its root set has cardinality 3.
  have h_card : Fintype.card (Polynomial.rootSet p ℂ) = 3 := by
    rw [ p_roots_card, show Fintype.card ( p.rootSet ℝ ) = 1 from ?_ ];
    norm_num [ Polynomial.rootSet_def ];
    rw [ Finset.card_eq_one ] ; use Real.rpow 2 ( 1/3 : ℝ ) ; ext ; norm_num [ p ] ; ring_nf ;
    exact ⟨ fun h => by rw [ show ( 2 : ℝ ) = ( ‹_› : ℝ ) ^ 3 by linarith ] ; rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by nlinarith [ sq_nonneg ( ‹_› : ℝ ) ] ) ] ; norm_num, fun h => ⟨ by exact ne_of_apply_ne ( Polynomial.eval 0 ) ( by norm_num ), by rw [ h ] ; rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by norm_num ) ] ; norm_num ⟩ ⟩;
  -- Since $p$ � �� is a cubic polynomial, its root set has cardinality 3, so $Equiv.Perm (rootSet p ℂ)$ is isomorphic to $Equiv.Perm (Fin 3)$.
  have h_perm_iso : Nonempty (Equiv.Perm (Polynomial.rootSet p ℂ) ≃* Equiv.Perm (Fin 3)) := by
    refine' ⟨ _ ⟩;
    refine' { Equiv.permCongr ( Fintype.equivOfCardEq h_card ) with .. } ; aesop_cat;
  -- By combining the isomorphisms, we � conclude� that $Gal(p)$ is isomorphic to $S_3$.
  have h_final_iso : Nonempty (Polynomial.Gal p ≃* Equiv.Perm (Fin 3)) := by
    exact ⟨ h_galois.some.trans h_perm_iso.some ⟩;
  refine' ⟨ _, _, _, _, _, _ ⟩;
  exact p.SplittingField;
  all_goals try infer_instance;
  · exact
      { to_isSeparable := Algebra.IsAlgebraic.isSeparable_of_perfectField,
        to_normal := SplittingField.instNormal p };
  · exact h_final_iso

end

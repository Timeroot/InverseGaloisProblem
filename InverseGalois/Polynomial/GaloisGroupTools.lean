/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Tools for Computing Galois Groups of Polynomials

General-purpose lemmas for determining the Galois groups of polynomials over ℚ.
-/

open Polynomial IntermediateField Module

noncomputable section

/-- For an irreducible polynomial `p` over a char 0 field, the degree divides the
order of the Galois group. -/
theorem natDegree_dvd_card {F : Type*} [Field F] [CharZero F] {p : Polynomial F}
    (p_irr : Irreducible p) : p.natDegree ∣ Nat.card p.Gal := by
  rw [Polynomial.Gal.card_of_separable p_irr.separable]
  have hp : p.degree ≠ 0 := by
    have := Irreducible.natDegree_pos p_irr
    simp [Polynomial.degree_eq_natDegree p_irr.ne_zero]; omega
  let α : p.SplittingField :=
    rootOfSplits (SplittingField.splits p) (by rwa [degree_map])
  have hα : IsIntegral F α := .of_finite F α
  use finrank (IntermediateField.adjoin F {α}) p.SplittingField
  suffices (minpoly F α).natDegree = p.natDegree by
    rw [← finrank_mul_finrank F (IntermediateField.adjoin F {α}) p.SplittingField,
      IntermediateField.adjoin.finrank hα, this]
  suffices minpoly F α ∣ p by
    have key := (minpoly.irreducible hα).dvd_symm p_irr this
    apply le_antisymm
    · exact natDegree_le_of_dvd this p_irr.ne_zero
    · exact natDegree_le_of_dvd key (minpoly.ne_zero hα)
  apply minpoly.dvd F α
  rw [← eval_map_algebraMap, eval_rootOfSplits]

/-- For a separable polynomial of degree n, the number of complex roots equals n. -/
theorem card_rootSet_eq_natDegree (p : Polynomial ℚ) (hp : p.Separable) (hp0 : p ≠ 0) :
    Fintype.card (p.rootSet ℂ) = p.natDegree := by
  simp_rw [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe]
  rw [Multiset.toFinset_card_of_nodup, ← Polynomial.Splits.natDegree_eq_card_roots,
    natDegree_map]
  · exact IsAlgClosed.splits _
  · exact nodup_roots ((separable_map (algebraMap ℚ ℂ)).mpr hp)

/-
The Galois group order divides the factorial of the number of roots. This follows
from the injective Galois action on roots (Lagrange's theorem).
-/
theorem card_gal_dvd_card_rootSet_factorial (p : Polynomial ℚ) :
    Nat.card p.Gal ∣ (Fintype.card (p.rootSet ℂ)).factorial := by
      by_contra! h_contra;
      -- By the properties of the Galois group, we know that $|Gal(p)|$ divides $|S_n| = n!$.
      have h_div : Nat.card p.Gal ∣ Fintype.card (Equiv.Perm (p.rootSet ℂ)) := by
        convert Subgroup.card_subgroup_dvd_card (MonoidHom.range (Polynomial.Gal.galActionHom p ℂ)) using 1;
        convert Nat.card_congr ( Equiv.ofInjective _ <| Polynomial.Gal.galActionHom_injective p ℂ ) using 1;
        · rw [ Nat.card_eq_fintype_card ];
        · exact Gal.splits_ℚ_ℂ;
      simp_all [ Fintype.card_perm ]

end
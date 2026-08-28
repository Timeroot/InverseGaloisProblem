/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Cyclotomic.SquareRoots
import InverseGalois.CFT.CyclotomicCompositum

/-!
# The eighth cyclotomic layer inside an algebraic closure

The cyclotomic subfield of conductor eight sits inside the algebraic closure of the rationals as
`cycSubfield 8`, and it is of degree four, so adjoining it to a field of two-power degree keeps the
degree a power of two.  What it brings is a square root of `-1` and a square root of `2`: the
fourth power of a primitive eighth root of unity is `-1`, and `η + η⁻¹` squares to `2`.

Those two square roots are exactly the input the dyadic square-class analysis needs, so this is the
layer that the Scholz–Reichardt construction at the prime two adjoins before it corrects the
ramification there.

## Main results

* `InverseGalois.CFT.exists_isPrimitiveRoot_of_cycSubfield_le`: a field containing the cyclotomic
  subfield of conductor `n` contains a primitive `n`-th root of unity.
* `InverseGalois.CFT.exists_sq_eq_neg_one_of_cycSubfield_eight_le` and
  `InverseGalois.CFT.exists_sq_eq_two_of_cycSubfield_eight_le`: **a field containing the eighth
  cyclotomic layer contains a square root of `-1` and a square root of `2`.**
* `InverseGalois.CFT.isPGroup_gal_cycSubfield_eight`: **the eighth cyclotomic layer has Galois
  group of order four.**

## Tags

cyclotomic field, root of unity, square root, two-group
-/

open NumberField

namespace InverseGalois.CFT

/-- A field containing the cyclotomic subfield of conductor `n` contains a primitive `n`-th root of
unity. -/
theorem exists_isPrimitiveRoot_of_cycSubfield_le {n : ℕ} [NeZero n]
    (M : IntermediateField ℚ (AlgebraicClosure ℚ)) (h : cycSubfield n ≤ M) :
    ∃ ζ : ↥M, IsPrimitiveRoot ζ n := by
  have hmem : cycRoot n ∈ M := h (IntermediateField.subset_adjoin ℚ _ rfl)
  refine ⟨⟨cycRoot n, hmem⟩, ?_⟩
  refine IsPrimitiveRoot.of_map_of_injective (f := (IntermediateField.val M).toMonoidHom) ?_ ?_
  · exact cycRoot_spec n
  · exact (IntermediateField.val M).injective

/-- **A field containing the eighth cyclotomic layer contains a square root of `-1`.** -/
theorem exists_sq_eq_neg_one_of_cycSubfield_eight_le
    (M : IntermediateField ℚ (AlgebraicClosure ℚ)) (h : cycSubfield 8 ≤ M) :
    ∃ i : ↥M, i ^ 2 = -1 := by
  haveI : NeZero (8 : ℕ) := ⟨by norm_num⟩
  obtain ⟨η, hη⟩ := exists_isPrimitiveRoot_of_cycSubfield_le M h
  refine ⟨η ^ 2, sq_eq_neg_one_of_isPrimitiveRoot_four ?_⟩
  simpa using isPrimitiveRoot_pow_div (m := 8) (k := 4) (by norm_num) hη (by norm_num)

/-- **A field containing the eighth cyclotomic layer contains a square root of `2`.** -/
theorem exists_sq_eq_two_of_cycSubfield_eight_le
    (M : IntermediateField ℚ (AlgebraicClosure ℚ)) (h : cycSubfield 8 ≤ M) :
    ∃ r : ↥M, r ^ 2 = 2 := by
  haveI : NeZero (8 : ℕ) := ⟨by norm_num⟩
  obtain ⟨η, hη⟩ := exists_isPrimitiveRoot_of_cycSubfield_le M h
  obtain ⟨r, hr⟩ := isSquare_two_of_isPrimitiveRoot_eight hη
  exact ⟨r, by rw [sq]; exact hr.symm⟩

/-- **The eighth cyclotomic layer has Galois group of order four**, so adjoining it keeps a
two-power degree a two-power degree. -/
theorem isPGroup_gal_cycSubfield_eight : IsPGroup 2 Gal(↥(cycSubfield 8)/ℚ) := by
  haveI : NeZero (8 : ℕ) := ⟨by norm_num⟩
  refine IsPGroup.of_card (n := 2) ?_
  rw [IsGalois.card_aut_eq_finrank ℚ ↥(cycSubfield 8), finrank_cycSubfield]
  decide

end InverseGalois.CFT

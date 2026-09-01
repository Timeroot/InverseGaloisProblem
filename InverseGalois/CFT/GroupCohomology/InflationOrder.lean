/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.InfResTwo
import InverseGalois.CFT.TateCohomology.Annihilate

/-!
# The order of a class inflated from a quotient

A second cohomology class of a group restricts to a normal subgroup, and the order of the subgroup
annihilates everything in the cohomology of the subgroup.  So the multiple of a class by the order
of the subgroup dies on the subgroup, and the exactness of the inflation-restriction sequence in
degree two produces a class on the quotient inflating to it, as soon as the first cohomology of the
subgroup vanishes.

That class carries the arithmetic of the original one down to the quotient.  If only the multiples
of the order of the whole group annihilate the class one started with, then a multiple of the
descended class which vanishes gives, after inflation, a multiple of the original class by the same
integer times the order of the subgroup; the order of the whole group divides that product, and the
order of the whole group is the order of the subgroup times the order of the quotient, so the order
of the quotient divides the integer.

Together with the corresponding statement for a subgroup this transports a class of the largest
possible order along both steps of a subquotient.  No compatibility between restriction to a
subgroup and inflation from a quotient is needed, because each step consumes only the arithmetic
property of the class produced by the previous one.

## Main results

* `InverseGalois.CFT.exists_inflTwo_eq_card_nsmul`: **the multiple of a second cohomology class by
  the order of a normal subgroup is inflated from the quotient**, once the first cohomology of the
  subgroup vanishes.
* `InverseGalois.CFT.exists_dvd_of_zsmul_eq_zero_quotientToInvariants`: **a class annihilated by
  exactly the multiples of the order of the group descends to a class of the quotient annihilated
  by exactly the multiples of the order of the quotient.**

## Tags

group cohomology, inflation, restriction, fundamental class, class formation
-/

namespace InverseGalois.CFT

open CategoryTheory groupCohomology Tate

noncomputable section

variable {G : Type} [Group G] [Finite G] {A : Rep ℤ G} {S : Subgroup G} [S.Normal]

/-- **The multiple of a second cohomology class by the order of a normal subgroup is inflated from
the quotient**, once the first cohomology of the subgroup vanishes: the order of the subgroup
annihilates the restriction of the class, and a class dying on the subgroup is an inflation. -/
theorem exists_inflTwo_eq_card_nsmul
    (hH1 : ∀ z : ↥(groupCohomology ((Action.res _ S.subtype).obj A) 1), z = 0) (β : ↥(H2 A)) :
    ∃ γ : ↥(H2 (A.quotientToInvariants S)), inflTwo A S γ = Nat.card ↥S • β := by
  refine mem_range_inflTwo_of_resTwo_eq_zero hH1 _ ?_
  have h : (resTwo A S).hom (Nat.card ↥S • β) = Nat.card ↥S • (resTwo A S).hom β :=
    map_nsmul (resTwo A S).hom _ _
  rw [h]
  exact card_nsmul_eq_zero_tateModule (k := ℤ) ((Action.res (ModuleCat ℤ) S.subtype).obj A) 2
    ((resTwo A S).hom β)

/-- **A second cohomology class annihilated by exactly the multiples of the order of the group
descends to a class of the quotient by a normal subgroup annihilated by exactly the multiples of
the order of the quotient**, once the first cohomology of the subgroup vanishes. -/
theorem exists_dvd_of_zsmul_eq_zero_quotientToInvariants
    (hH1 : ∀ z : ↥(groupCohomology ((Action.res _ S.subtype).obj A) 1), z = 0) {β : ↥(H2 A)}
    (hβ : ∀ m : ℤ, m • β = 0 → (Nat.card G : ℤ) ∣ m) :
    ∃ γ : ↥(H2 (A.quotientToInvariants S)),
      ∀ m : ℤ, m • γ = 0 → (Nat.card (G ⧸ S) : ℤ) ∣ m := by
  obtain ⟨γ, hγ⟩ := exists_inflTwo_eq_card_nsmul hH1 β
  refine ⟨γ, fun m hm => ?_⟩
  have h0 : (inflTwo A S).hom (m • γ) = 0 := by
    rw [hm, map_zero]
  rw [map_zsmul (inflTwo A S).hom, hγ] at h0
  have h1 : (m * (Nat.card ↥S : ℤ)) • β = 0 := by
    rw [mul_smul, natCast_zsmul]
    exact h0
  have h2 := hβ _ h1
  rw [← Subgroup.card_mul_index S, Subgroup.index_eq_card] at h2
  push_cast at h2
  have hne : (Nat.card ↥S : ℤ) ≠ 0 :=
    Int.natCast_ne_zero.2 (Nat.card_pos (α := ↥S)).ne'
  refine (mul_dvd_mul_iff_left hne).1 ?_
  rw [mul_comm ((Nat.card ↥S : ℤ)) m]
  exact h2

end

end InverseGalois.CFT

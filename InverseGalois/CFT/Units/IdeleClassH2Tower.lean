/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.H1Transport
import InverseGalois.CFT.GroupCohomology.H2Devissage
import InverseGalois.CFT.GroupCohomology.H2Transport
import InverseGalois.CFT.Units.IdeleClassTower

/-!
# The second cohomology of the idele class group along a tower

Let a tower of number fields have a middle field normal over the base and a top field Galois over
the base.  Restriction to the middle field is a surjection of the Galois group of the top field
over the base onto the Galois group of the middle field over the base, whose kernel is the group of
automorphisms fixing the middle field pointwise; and the idele class group of the middle field sits
inside the idele class group of the top field as the part fixed by that kernel.

That is exactly the situation of the dévissage for the second cohomology.  Once the first
cohomology over the middle field vanishes, a two-cocycle of the top group whose restriction to the
kernel is a coboundary is inflated from the quotient, so the number of classes upstairs is at most
the number of classes of the quotient times the number of classes of the kernel; and the kernel is
the Galois group of the top field over the middle field.

## Main definitions

* `InverseGalois.CFT.galRestrictKerEquiv`: restriction of scalars, as an isomorphism of the Galois
  group of the top field over the middle field with the kernel of restriction to the middle field.
* `InverseGalois.CFT.ideleClassRepKer`: the idele class group of the top field, as a representation
  of that kernel.

## Main results

* `InverseGalois.CFT.exists_zsmul_eq_zero_imp_dvd_H2_ideleClassRep_of_tower`: **a class of the
  second cohomology of the invariants of the middle field that is annihilated only by the multiples
  of a number is matched by such a class for the middle field over the base.**
* `InverseGalois.CFT.finite_and_card_H2_ideleClassRep_of_tower`: **the second cohomology of the
  idele class group of the top field over the base is finite and has at most as many elements as
  the product of the second cohomology for the middle field over the base and the second cohomology
  for the top field over the middle field.**

## Tags

number field, idele class group, group cohomology, tower, dévissage
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

open groupCohomology

namespace InverseGalois.CFT

section Tower

variable {k F K : Type} [Field k] [NumberField k] [Field F] [NumberField F] [Field K]
  [NumberField K] [Algebra k F] [Algebra F K] [Algebra k K] [IsScalarTower k F K]
  [IsGalois k F] [IsGalois F K] [IsGalois k K]

variable (k F K) in
/-- **Restriction of scalars identifies the automorphisms of the top field over the middle field
with the automorphisms of the top field over the base that fix the middle field pointwise.** -/
noncomputable def galRestrictKerEquiv :
    Gal(K/F) ≃* ↥(AlgEquiv.restrictNormalHom F : Gal(K/k) →* Gal(F/k)).ker where
  toFun σ := ⟨σ.restrictScalars k, restrictNormalHom_restrictScalars k F σ⟩
  invFun s := (exists_restrictScalars_of_restrictNormalHom_eq_one k s.2).choose
  left_inv σ := AlgEquiv.restrictScalars_injective k
    (exists_restrictScalars_of_restrictNormalHom_eq_one k
      (restrictNormalHom_restrictScalars k F σ)).choose_spec
  right_inv s := Subtype.ext
    (exists_restrictScalars_of_restrictNormalHom_eq_one k s.2).choose_spec
  map_mul' _ _ := Subtype.ext rfl

variable (k F K) in
omit [NumberField k] [NumberField F] [NumberField K] [IsGalois F K] [IsGalois k K] in
@[simp]
theorem coe_galRestrictKerEquiv (σ : Gal(K/F)) :
    ((galRestrictKerEquiv k F K σ :
      ↥(AlgEquiv.restrictNormalHom F : Gal(K/k) →* Gal(F/k)).ker) : Gal(K/k))
      = σ.restrictScalars k := rfl

variable (k F K) in
/-- The idele class group of the top field, as a representation of the group of automorphisms of
the top field over the base that fix the middle field pointwise. -/
noncomputable abbrev ideleClassRepKer :
    Rep ℤ ↥(AlgEquiv.restrictNormalHom F : Gal(K/k) →* Gal(F/k)).ker :=
  (Action.res _ (AlgEquiv.restrictNormalHom F : Gal(K/k) →* Gal(F/k)).ker.subtype).obj
    (ideleClassRep k K)

variable (k F K) in
omit [IsGalois F K] [IsGalois k K] in
/-- An automorphism of the top field fixing the middle field pointwise acts on the idele class
group as the corresponding automorphism over the middle field. -/
theorem ideleClassRepKer_rho
    (s : ↥(AlgEquiv.restrictNormalHom F : Gal(K/k) →* Gal(F/k)).ker) (a : IdeleClass K) :
    (ideleClassRepKer k F K).ρ s a
      = (ideleClassRep F K).ρ ((galRestrictKerEquiv k F K).symm s) a := by
  have hs : (s : Gal(K/k)) = ((galRestrictKerEquiv k F K).symm s).restrictScalars k := by
    rw [← coe_galRestrictKerEquiv k F K, MulEquiv.apply_symm_apply]
  show ideleClassAutHom k K (s : Gal(K/k)) a
    = ideleClassAutHom F K ((galRestrictKerEquiv k F K).symm s) a
  rw [hs, ideleClassAutHom_restrictScalars]

omit [IsGalois F K] [IsGalois k K] in
/-- The second cohomology for the kernel of restriction to the middle field has as many elements as
the second cohomology for the top field over the middle field. -/
theorem card_H2_ideleClassRepKer :
    Nat.card ↥(H2 (ideleClassRepKer k F K)) = Nat.card ↥(H2 (ideleClassRep F K)) :=
  card_H2_eq_of_addEquiv (C := ideleClassRepKer k F K) (D := ideleClassRep F K)
    (galRestrictKerEquiv k F K).symm (AddEquiv.refl (IdeleClass K))
    (fun s a => ideleClassRepKer_rho k F K s a)

omit [IsGalois F K] [IsGalois k K] in
/-- The second cohomology for the kernel of restriction to the middle field is finite as soon as
the second cohomology for the top field over the middle field is. -/
theorem finite_H2_ideleClassRepKer [Finite ↥(H2 (ideleClassRep F K))] :
    Finite ↥(H2 (ideleClassRepKer k F K)) :=
  finite_H2_of_addEquiv (C := ideleClassRepKer k F K) (D := ideleClassRep F K)
    (galRestrictKerEquiv k F K).symm (AddEquiv.refl (IdeleClass K))
    (fun s a => ideleClassRepKer_rho k F K s a)

omit [IsGalois F K] [IsGalois k K] in
/-- The first cohomology for the kernel of restriction to the middle field vanishes as soon as the
first cohomology for the top field over the middle field does. -/
theorem eq_zero_H1_ideleClassRepKer
    (hKF : ∀ y : groupCohomology (ideleClassRep F K) 1, y = 0)
    (z : groupCohomology (ideleClassRepKer k F K) 1) : z = 0 :=
  eq_zero_H1_of_mulEquiv (A := ideleClassRepKer k F K) (B := ideleClassRep F K)
    (galRestrictKerEquiv k F K).symm (LinearEquiv.refl ℤ (IdeleClass K))
    (fun s a => ideleClassRepKer_rho k F K s a) hKF z

variable (k F K) in
omit [NumberField k] in
/-- **A class of the second cohomology of the invariants of the middle field that is annihilated
only by the multiples of a number is matched by such a class for the middle field over the
base.** -/
theorem exists_zsmul_eq_zero_imp_dvd_H2_ideleClassRep_of_tower {n : ℕ}
    (h : ∃ γ : ↥(H2 ((ideleClassRep k K).quotientToInvariants
        (AlgEquiv.restrictNormalHom F : Gal(K/k) →* Gal(F/k)).ker)),
      ∀ m : ℤ, m • γ = 0 → (n : ℤ) ∣ m) :
    ∃ γ : ↥(H2 (ideleClassRep k F)), ∀ m : ℤ, m • γ = 0 → (n : ℤ) ∣ m :=
  exists_zsmul_eq_zero_imp_dvd_H2_of_devissage
    (AlgEquiv.restrictNormalHom F : Gal(K/k) →* Gal(F/k))
    (ideleClassComapLin F K)
    (fun _ _ h => ideleClassComap_injective F K h)
    (fun g b => (ideleClassAut_ideleClassComap F g b).symm)
    (fun a ha => (mem_range_ideleClassComap_iff F K a).mpr
      fun σ => ha (σ.restrictScalars k) (restrictNormalHom_restrictScalars k F σ))
    (AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := F) (E := K)) h

/-- **Dévissage of the second cohomology of the idele class group along a tower.**  The number of
classes for the top field over the base is at most the number of classes for the middle field over
the base times the number of classes for the top field over the middle field. -/
theorem finite_and_card_H2_ideleClassRep_of_tower
    (hKF : ∀ y : groupCohomology (ideleClassRep F K) 1, y = 0)
    [Finite ↥(H2 (ideleClassRep k F))] [Finite ↥(H2 (ideleClassRep F K))] :
    Finite ↥(H2 (ideleClassRep k K)) ∧ Nat.card ↥(H2 (ideleClassRep k K))
      ≤ Nat.card ↥(H2 (ideleClassRep k F)) * Nat.card ↥(H2 (ideleClassRep F K)) := by
  haveI : Finite ↥(H2 (ideleClassRepKer k F K)) := finite_H2_ideleClassRepKer
  obtain ⟨hfin, hle⟩ := finite_and_card_H2_le_of_devissage
    (A := ideleClassRep k K) (B := ideleClassRep k F)
    (AlgEquiv.restrictNormalHom F : Gal(K/k) →* Gal(F/k))
    (ideleClassComapLin F K)
    (fun _ _ h => ideleClassComap_injective F K h)
    (fun g b => (ideleClassAut_ideleClassComap F g b).symm)
    (fun a ha => (mem_range_ideleClassComap_iff F K a).mpr
      fun σ => ha (σ.restrictScalars k) (restrictNormalHom_restrictScalars k F σ))
    (AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := F) (E := K))
    (fun z => eq_zero_H1_ideleClassRepKer hKF z)
  exact ⟨hfin, hle.trans (Nat.mul_le_mul le_rfl (le_of_eq card_H2_ideleClassRepKer))⟩

end Tower

end InverseGalois.CFT

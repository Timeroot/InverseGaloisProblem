/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.H2Transport
import InverseGalois.CFT.GroupCohomology.InfResTwo
import InverseGalois.CFT.TateCohomology.Annihilate
import InverseGalois.CFT.Units.GlobalTate
import InverseGalois.CFT.Units.IdeleClassH2Tower

/-!
# The fundamental class over an arbitrary number field

The class of the right order in the second cohomology of the idele class group is known for a
Galois extension of the rationals, and the same class over an arbitrary number field as base is a
consequence rather than a second construction.  Two moves suffice.

Enlarging the base is restriction.  An intermediate field of an extension that is Galois over the
rationals gives a subgroup of the large Galois group, namely the image of restriction of scalars,
which is injective; the vanishing of the first cohomology and the bound on the second hold on every
subgroup, so the class over the rationals restricts to a class whose annihilator is exactly the
multiples of the order of that subgroup, and that order is the degree over the intermediate field.
The two representations of the smaller group on the idele class group agree because enlarging the
base does not change how an automorphism moves an idele.

Shrinking the top field is inflation.  A Galois extension of the base sits inside its normal
closure over the rationals, and the kernel of the restriction map between the two Galois groups is
annihilated by its own order, so that multiple of the class upstairs restricts to zero on the
kernel; the first cohomology of the kernel vanishing, the multiple is inflated from the quotient,
and the annihilator of the inflated class is what the dévissage for a tower needs.  Any Galois
extension of number fields is reached by doing both.

## Main definitions

* `InverseGalois.CFT.galRestrictScalarsHom`: restriction of scalars of an automorphism, as a
  homomorphism of Galois groups.

## Main results

* `InverseGalois.CFT.exists_zsmul_eq_zero_imp_dvd_H2_ideleClassRep_of_rat`: the class over an
  intermediate field of an extension Galois over the rationals.
* `InverseGalois.CFT.exists_zsmul_eq_zero_imp_dvd_H2_ideleClassRep_of_top`: descending the class
  from a larger Galois extension of the same base.
* `InverseGalois.CFT.exists_zsmul_eq_zero_imp_dvd_H2_ideleClassRep_base`: **the second cohomology
  of the idele class group of a Galois extension of number fields contains a class annihilated by
  exactly the multiples of the degree.**

## Tags

class field theory, class formation, fundamental class, idele class group, number field
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

open CategoryTheory groupCohomology NumberField

namespace InverseGalois.CFT

noncomputable section

open Tate

/-! ### Restriction of scalars -/

section RestrictScalars

variable (F k K : Type*) [Field F] [Field k] [Field K] [Algebra F k] [Algebra k K] [Algebra F K]
  [IsScalarTower F k K]

/-- Restriction of scalars, as a homomorphism from the automorphisms of an extension over an
intermediate field to the automorphisms over the base. -/
def galRestrictScalarsHom : Gal(K/k) →* Gal(K/F) where
  toFun σ := σ.restrictScalars F
  map_one' := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

@[simp]
theorem galRestrictScalarsHom_apply (σ : Gal(K/k)) :
    galRestrictScalarsHom F k K σ = σ.restrictScalars F := rfl

theorem galRestrictScalarsHom_injective : Function.Injective (galRestrictScalarsHom F k K) :=
  fun _ _ h => AlgEquiv.restrictScalars_injective F h

end RestrictScalars

/-! ### Enlarging the base field -/

section Rat

variable (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L] [Algebra k L]
  [IsGalois ℚ L]

/-- A class of the second cohomology of the idele class group of a Galois extension of the
rationals, over an intermediate field, annihilated by exactly the multiples of the degree. -/
theorem exists_zsmul_eq_zero_imp_dvd_H2_ideleClassRep_of_rat :
    ∃ α : ↥(H2 (ideleClassRep k L)), ∀ m : ℤ, m • α = 0 → (Nat.card Gal(L/k) : ℤ) ∣ m := by
  have hinj : Function.Injective (galRestrictScalarsHom ℚ k L) :=
    galRestrictScalarsHom_injective ℚ k L
  set S := (galRestrictScalarsHom ℚ k L).range with hSdef
  set e : Gal(L/k) ≃* ↥S := MonoidHom.ofInjective hinj with hedef
  have hcard : Nat.card ↥S = Nat.card Gal(L/k) := (Nat.card_congr e.toEquiv).symm
  have htate := isTateClassTwo_ideleClassRep (k := ℚ) (K := L) S
    (zsmul_globalFundamentalClass_eq_zero_imp_dvd L)
  refine exists_zsmul_eq_zero_imp_dvd_H2_of_addEquiv (C := resObj S (ideleClassRep ℚ L))
    (D := ideleClassRep k L) e.symm (AddEquiv.refl (IdeleClass L)) ?_ ?_
  · intro g c
    have h1 : ((g : Gal(L/ℚ))) = (e.symm g).restrictScalars ℚ := by
      have h2 : ((e (e.symm g) : ↥S) : Gal(L/ℚ)) = (e.symm g).restrictScalars ℚ := rfl
      rwa [MulEquiv.apply_symm_apply] at h2
    show (ideleClassRep ℚ L).ρ (g : Gal(L/ℚ)) c = (ideleClassRep k L).ρ (e.symm g) c
    rw [h1]
    rfl
  · refine ⟨tateRes S (ideleClassRep ℚ L) 2 (globalFundamentalClass L), fun m hm => ?_⟩
    rw [← hcard]
    exact htate.dvd_of_zsmul_eq_zero m hm

end Rat

/-! ### Descending from a larger extension -/

section Top

variable (k K L : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Field L]
  [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [IsGalois k K] [IsGalois k L] [IsGalois K L]

/-- A class of the second cohomology of the idele class group annihilated by exactly the multiples
of the degree descends from a larger Galois extension of the same base. -/
theorem exists_zsmul_eq_zero_imp_dvd_H2_ideleClassRep_of_top
    (h : ∃ α : ↥(H2 (ideleClassRep k L)), ∀ m : ℤ, m • α = 0 → (Nat.card Gal(L/k) : ℤ) ∣ m) :
    ∃ α : ↥(H2 (ideleClassRep k K)), ∀ m : ℤ, m • α = 0 → (Nat.card Gal(K/k) : ℤ) ∣ m := by
  obtain ⟨α, hα⟩ := h
  have hsurj : Function.Surjective (AlgEquiv.restrictNormalHom K : Gal(L/k) →* Gal(K/k)) :=
    AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := K) (E := L)
  set N := (AlgEquiv.restrictNormalHom K : Gal(L/k) →* Gal(K/k)).ker with hNdef
  have hidx : N.index = Nat.card Gal(K/k) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv
  have hcard : Nat.card ↥N * Nat.card Gal(K/k) = Nat.card Gal(L/k) := by
    rw [← hidx]
    exact N.card_mul_index
  have hr0 : (Nat.card ↥N : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := ↥N)).ne'
  have hH1 :
      ∀ z : ↥(groupCohomology ((Action.res _ N.subtype).obj (ideleClassRep k L)) 1), z = 0 :=
    fun z => eq_zero_H1_res_subgroup N (fun y => eq_zero_H1_ideleClassRep_general y) z
  have hres : resTwo (ideleClassRep k L) N ((Nat.card ↥N : ℤ) • α) = 0 := by
    rw [map_zsmul, natCast_zsmul]
    exact card_nsmul_eq_zero_tateModule (resObj N (ideleClassRep k L)) 2 _
  obtain ⟨z, hz⟩ := mem_range_inflTwo_of_resTwo_eq_zero hH1 _ hres
  refine exists_zsmul_eq_zero_imp_dvd_H2_ideleClassRep_of_tower k K L ⟨z, fun m hm => ?_⟩
  have h1 : (m * (Nat.card ↥N : ℤ)) • α = 0 := by
    rw [mul_smul, ← hz, ← map_zsmul, hm, map_zero]
  have h2 := hα _ h1
  rw [← hcard] at h2
  push_cast at h2
  rw [mul_comm (m : ℤ)] at h2
  exact (mul_dvd_mul_iff_left hr0).mp h2

end Top

/-! ### An arbitrary base -/

section Base

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

/-- **The second cohomology of the idele class group of a Galois extension of number fields
contains a class annihilated by exactly the multiples of the degree.** -/
theorem exists_zsmul_eq_zero_imp_dvd_H2_ideleClassRep_base :
    ∃ α : ↥(H2 (ideleClassRep k K)), ∀ m : ℤ, m • α = 0 → (Nat.card Gal(K/k) : ℤ) ∣ m := by
  set L := ↥(IntermediateField.normalClosure ℚ K (AlgebraicClosure K)) with hLdef
  haveI : NumberField L := ⟨⟩
  haveI : IsGalois ℚ L := ⟨⟩
  letI : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
  haveI : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsGalois k L := IsGalois.tower_top_of_isGalois ℚ k L
  haveI : IsGalois K L := IsGalois.tower_top_of_isGalois ℚ K L
  exact exists_zsmul_eq_zero_imp_dvd_H2_ideleClassRep_of_top k K L
    (exists_zsmul_eq_zero_imp_dvd_H2_ideleClassRep_of_rat k L)

end Base

end

end InverseGalois.CFT

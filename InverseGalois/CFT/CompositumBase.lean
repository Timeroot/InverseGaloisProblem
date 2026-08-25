/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Compositum

/-!
# The compositum of two subextensions as an extension of one of them

Let `A` and `B` be two finite Galois subextensions of `L / F` which meet in the base field.  The
compositum `A ⊔ B` is then an extension of `B`, and restriction to `A` identifies its Galois group
over `B` with the Galois group of `A` over `F`.  This is the base-change step of the
Scholz-Reichardt construction, where `B` is a cyclotomic field adjoined to make the roots of unity
available and `A` is the field realising the group at hand: adjoining `B` does not disturb the
Galois group, because the two degrees are coprime.

The compositum viewed as an extension of `B` is `IntermediateField.extendScalars`, which changes
the base field without changing the underlying set.  The instances that let `Mathlib` see the
resulting tower are supplied here.

## Main definitions

* `InverseGalois.CFT.supOver`: the compositum `A ⊔ B`, viewed as an extension of `B`.
* `InverseGalois.CFT.galRestrictBase`: restriction to `A` of an automorphism of the compositum
  over `B`.
* `InverseGalois.CFT.galEquivBase`: the resulting isomorphism of Galois groups.

## Main results

* `InverseGalois.CFT.galRestrictBase_injective`: **an automorphism of the compositum fixing `B`
  and `A` pointwise is the identity.**
* `InverseGalois.CFT.finrank_supOver`: **the compositum has the same degree over `B` as `A` has
  over `F`**, when the two subextensions meet in the base field.
* `InverseGalois.CFT.galRestrictBase_bijective`, `InverseGalois.CFT.galEquivBase`: **restriction
  identifies the Galois group of the compositum over `B` with the Galois group of `A` over `F`.**

## Tags

compositum, base change, Galois group, linearly disjoint
-/

namespace InverseGalois.CFT

open Module IntermediateField

section ExtendScalars

variable {F L : Type*} [Field F] [Field L] [Algebra F L] {E E' : IntermediateField F L}

/-- Enlarging the base field of an intermediate field to a smaller intermediate field leaves a
tower over the original base. -/
instance isScalarTower_extendScalars (h : E ≤ E') :
    IsScalarTower F ↥E ↥(extendScalars h) :=
  IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl

end ExtendScalars

variable {F L : Type*} [Field F] [Field L] [Algebra F L] (A B : IntermediateField F L)

/-- **The compositum of `A` and `B`, viewed as an extension of `B`.**  Its underlying set is that
of `A ⊔ B`; only the base field has changed. -/
abbrev supOver : IntermediateField ↥B L := extendScalars (le_sup_right : B ≤ A ⊔ B)

section Normal

variable [Normal F A] [Normal F B]

/-- **Restriction to `A` of an automorphism of the compositum over `B`.**  Such an automorphism is
in particular an automorphism over `F`, and `A` is normal over `F`. -/
noncomputable def galRestrictBase : Gal(↥(supOver A B)/↥B) →* Gal(A/F) where
  toFun σ := (galRestrictProd A B (σ.restrictScalars F)).1
  map_one' := by
    rw [show AlgEquiv.restrictScalars F (1 : Gal(↥(supOver A B)/↥B)) = 1 from rfl, map_one,
      Prod.fst_one]
  map_mul' σ τ := by
    show (galRestrictProd A B ((σ * τ).restrictScalars F)).1 = _
    have h : (σ * τ).restrictScalars F = σ.restrictScalars F * τ.restrictScalars F := rfl
    rw [h, map_mul]
    rfl

/-- Reading off, inside `L`, the restriction to `A` of an automorphism of the compositum. -/
theorem coe_galRestrictBase (σ : Gal(↥(supOver A B)/↥B)) (x : A) :
    ((galRestrictBase A B σ x : A) : L) =
      ((σ ⟨(x : L), (le_sup_left : A ≤ A ⊔ B) x.2⟩ : ↥(supOver A B)) : L) :=
  coe_galRestrictProd_fst A B (σ.restrictScalars F) x

/-- **An automorphism of the compositum over `B` that is the identity on `A` is the identity.**
Being an automorphism over `B` it is already the identity on `B`, and the two subextensions
generate the compositum. -/
theorem galRestrictBase_injective : Function.Injective (galRestrictBase A B) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have hsnd : (galRestrictProd A B (σ.restrictScalars F)).2 = 1 := by
    refine AlgEquiv.ext fun x => Subtype.ext ?_
    rw [coe_galRestrictProd_snd A B (σ.restrictScalars F) x]
    show ((σ (algebraMap ↥B ↥(supOver A B) x) : ↥(supOver A B)) : L) = (x : L)
    rw [σ.commutes]
    rfl
  have hone : galRestrictProd A B (σ.restrictScalars F) = 1 := by
    refine Prod.ext ?_ ?_
    · exact hσ
    · exact hsnd
  exact AlgEquiv.restrictScalars_injective F
    ((injective_iff_map_eq_one (galRestrictProd A B)).mp (galRestrictProd_injective A B) _ hone)

end Normal

section Galois

variable [IsGalois F A] [FiniteDimensional F A] [IsGalois F B] [FiniteDimensional F B]

instance finiteDimensional_supOver : FiniteDimensional F ↥(supOver A B) :=
  inferInstanceAs (FiniteDimensional F ↥(A ⊔ B))

instance isGalois_supOver : IsGalois F ↥(supOver A B) := inferInstanceAs (IsGalois F ↥(A ⊔ B))

instance finiteDimensional_supOver_base : FiniteDimensional ↥B ↥(supOver A B) :=
  Module.Finite.of_restrictScalars_finite F ↥B ↥(supOver A B)

instance isGalois_supOver_base : IsGalois ↥B ↥(supOver A B) :=
  IsGalois.tower_top_of_isGalois F ↥B ↥(supOver A B)

omit [IsGalois F ↥B] in
/-- **The compositum has the same degree over `B` as `A` has over `F`**, provided the two
subextensions meet in the base field: the degree of the compositum over `F` is then the product of
the two degrees. -/
theorem finrank_supOver (h : A ⊓ B = ⊥) : finrank ↥B ↥(supOver A B) = finrank F A := by
  have hmul : finrank F ↥B * finrank ↥B ↥(supOver A B) = finrank F ↥(supOver A B) :=
    finrank_mul_finrank F ↥B ↥(supOver A B)
  have htot : finrank F ↥(supOver A B) = finrank F A * finrank F B :=
    finrank_sup_of_inf_eq_bot A B h
  have hB : 0 < finrank F ↥B := finrank_pos
  refine Nat.eq_of_mul_eq_mul_left hB ?_
  rw [hmul, htot]
  ring

/-- **Restriction identifies the Galois group of the compositum over `B` with the Galois group of
`A` over `F`**, provided the two subextensions meet in the base field.  Restriction is injective,
and the two groups have the same order. -/
theorem galRestrictBase_bijective (h : A ⊓ B = ⊥) : Function.Bijective (galRestrictBase A B) := by
  refine (Nat.bijective_iff_injective_and_card _).mpr ⟨galRestrictBase_injective A B, ?_⟩
  rw [IsGalois.card_aut_eq_finrank ↥B ↥(supOver A B), IsGalois.card_aut_eq_finrank F A,
    finrank_supOver A B h]

/-- **The Galois group of the compositum over `B` is the Galois group of `A` over `F`**, when the
two subextensions meet in the base field. -/
noncomputable def galEquivBase (h : A ⊓ B = ⊥) : Gal(↥(supOver A B)/↥B) ≃* Gal(A/F) :=
  MulEquiv.ofBijective _ (galRestrictBase_bijective A B h)

@[simp]
theorem galEquivBase_apply (h : A ⊓ B = ⊥) (σ : Gal(↥(supOver A B)/↥B)) :
    galEquivBase A B h σ = galRestrictBase A B σ :=
  rfl

end Galois

end InverseGalois.CFT

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.IdeleClass
import InverseGalois.CFT.Units.IdeleNorm

/-!
# The ideles as a representation of the Galois group

The Galois group of an extension of number fields acts on the units of the top field, on its ideles
and on its idele classes.  Each of those actions is recorded elsewhere as an action of a single
automorphism, which is the shape the Tate formalism wants; here the actions are assembled into
`ℤ`-linear representations of the whole Galois group, which is the shape the machinery of group
cohomology wants.

An action by additive automorphisms is the same thing as a `ℤ`-linear representation, because an
additive map is automatically `ℤ`-linear; `repOfAddAut` performs that translation.  Since the
coefficient ring of a representation and the acting group live in the same universe, and the
coefficient ring here is `ℤ`, all the fields in this file are pinned to `Type`.

Enlarging the base field of the extension leaves the action untouched: the automorphism acts through
its underlying map of fields, so restricting scalars along an intermediate field changes neither the
group element's effect on the ideles nor its effect on the idele classes.  That is the content of
`ideleClassAutHom_restrictScalars`, and it makes the restriction of the representation to a
subgroup of the Galois group definitionally the representation attached to the intermediate field.

## Main definitions

* `InverseGalois.CFT.repOfAddAut`: the `ℤ`-linear representation attached to an action by additive
  automorphisms.
* `InverseGalois.CFT.IdeleClass`: **the idele class group of a number field.**
* `InverseGalois.CFT.ideleClassAutHom`: the Galois action on the idele class group, as a
  homomorphism.
* `InverseGalois.CFT.ideleRep`, `InverseGalois.CFT.globalUnitsRep`,
  `InverseGalois.CFT.ideleClassRep`: the representations of the Galois group on the ideles, on the
  units of the top field, and on the idele classes.

## Main results

* `InverseGalois.CFT.ideleClassAutHom_restrictScalars`: **the action on the idele class group does
  not change when the base field is enlarged.**

## Tags

number field, idele, idele class group, Galois representation, group cohomology
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

open IsDedekindDomain NumberField

namespace InverseGalois.CFT

/-! ### Representations from actions by additive automorphisms -/

section OfAddAut

variable {G A : Type} [Group G] [AddCommGroup A]

/-- The `ℤ`-linear representation attached to an action by additive automorphisms. -/
noncomputable def repOfAddAut (φ : G →* AddAut A) : Rep ℤ G :=
  Rep.of
    { toFun := fun g => ((φ g).toAddMonoidHom.toIntLinearMap : Module.End ℤ A)
      map_one' := by ext a; simp
      map_mul' := fun g h => by ext a; simp }

@[simp]
theorem repOfAddAut_ρ_apply (φ : G →* AddAut A) (g : G) (a : A) :
    (repOfAddAut φ).ρ g a = φ g a := rfl

end OfAddAut

/-! ### The Galois action on the idele class group -/

section Hom

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- **The idele class group of a number field.** -/
abbrev IdeleClass : Type := ↥(idele K) ⧸ (ideleDiag K).range

omit [NumberField k] in
/-- **The Galois action on the idele class group, as a homomorphism.** -/
noncomputable def ideleClassAutHom : Gal(K/k) →* AddAut (IdeleClass K) where
  toFun := ideleClassAut (k := k)
  map_one' := AddEquiv.ext fun x => by
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
    show QuotientAddGroup.mk (ideleAut (k := k) 1 a) = QuotientAddGroup.mk a
    rw [ideleAut_one]
  map_mul' σ τ := AddEquiv.ext fun x => by
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
    show QuotientAddGroup.mk (ideleAut (k := k) (σ * τ) a)
      = QuotientAddGroup.mk (ideleAut (k := k) σ (ideleAut (k := k) τ a))
    rw [ideleAut_mul]

omit [NumberField k] in
@[simp]
theorem ideleClassAutHom_apply (σ : Gal(K/k)) (x : IdeleClass K) :
    ideleClassAutHom k K σ x = ideleClassAut (k := k) σ x := rfl

/-- The representation of the Galois group on the ideles. -/
noncomputable abbrev ideleRep : Rep ℤ Gal(K/k) := repOfAddAut (ideleAutHom k K)

/-- The representation of the Galois group on the units of the top field. -/
noncomputable abbrev globalUnitsRep : Rep ℤ Gal(K/k) :=
  repOfAddAut (globalUnitsAut (k := k) (K := K))

/-- The representation of the Galois group on the idele class group. -/
noncomputable abbrev ideleClassRep : Rep ℤ Gal(K/k) := repOfAddAut (ideleClassAutHom k K)

end Hom

/-! ### Enlarging the base field -/

section BaseChange

variable (k : Type) {F K : Type} [Field k] [Field F] [Field K] [NumberField K]
  [Algebra k F] [Algebra F K] [Algebra k K] [IsScalarTower k F K]

/-- **The action on the idele class group does not change when the base field is enlarged**: an
automorphism acts through its underlying map of fields, which restriction of scalars leaves
untouched. -/
theorem ideleClassAutHom_restrictScalars [NumberField k] [NumberField F] (σ : Gal(K/F)) :
    ideleClassAutHom k K (σ.restrictScalars k) = ideleClassAutHom F K σ := rfl

end BaseChange

end InverseGalois.CFT

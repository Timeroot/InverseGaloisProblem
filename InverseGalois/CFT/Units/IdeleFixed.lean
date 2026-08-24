/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.AdicFixed
import InverseGalois.CFT.Units.Idele
import InverseGalois.CFT.Units.InfiniteFixed

/-!
# The ideles fixed by the Galois group are the ideles of the base field

An idele of the base field determines an idele of the extension: at each place of the extension take
the image of the local unit at the place below.  The finiteness condition survives, because the
places at which the resulting idele fails to be a unit of the valuation ring are exactly the places
above the finitely many bad places of the base.  This file shows that the ideles so obtained are
exactly the ideles fixed by the Galois group, which is the identification of the fixed points of the
Galois action on the ideles with the ideles of the base field.

The two halves of the argument have already been carried out place by place: at the infinite places
and at the primes, the local units fixed by the decomposition group are exactly those coming from
the completion of the base, and a fixed family is determined on an orbit by its value at any one
place of it.  All that remains is to put the archimedean and the finite halves together and to check
the finiteness condition.

For a cyclic group it is enough to be fixed by a generator, because the automorphisms fixing a given
idele form a subgroup.

## Main definitions

* `InverseGalois.CFT.galIdeleAut`: the action of the Galois group on the ideles, as a homomorphism
  into the automorphism group.
* `InverseGalois.CFT.ideleComap`: **the ideles of the base field, viewed among the ideles of the
  extension.**

## Main results

* `InverseGalois.CFT.ideleComap_injective`: distinct ideles of the base field give distinct ideles
  of the extension.
* `InverseGalois.CFT.ideleAut_ideleComap`: an idele coming from the base field is fixed.
* `InverseGalois.CFT.mem_range_ideleComap_iff`: **the ideles fixed by the Galois group are exactly
  the ideles of the base field.**
* `InverseGalois.CFT.mem_range_ideleComap_iff_of_zpowers`: the same for a cyclic Galois group, where
  being fixed by a generator suffices.

## Tags

number field, idele, Galois action, fixed points, decomposition group
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

section IdeleFixed

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-! ### The action of the Galois group as a homomorphism -/

variable (k K) in
/-- **The action of the Galois group on the ideles**, as a homomorphism into the group of
automorphisms of the ideles. -/
noncomputable def galIdeleAut : Gal(K/k) →* AddAut ↥(idele K) where
  toFun σ := ideleAut (k := k) σ
  map_one' := AddEquiv.ext fun x => Subtype.ext (by
    show fullIdeleAut (k := k) (1 : Gal(K/k)) (x : FullIdele K) = (x : FullIdele K)
    rw [fullIdeleAut, map_one, map_one]
    rfl)
  map_mul' σ τ := AddEquiv.ext fun x => Subtype.ext (by
    show fullIdeleAut (k := k) (σ * τ) (x : FullIdele K)
      = fullIdeleAut (k := k) σ (fullIdeleAut (k := k) τ (x : FullIdele K))
    rw [fullIdeleAut, fullIdeleAut, fullIdeleAut, map_mul, map_mul]
    rfl)

omit [NumberField k] in
@[simp]
theorem galIdeleAut_apply (σ : Gal(K/k)) (x : ↥(idele K)) :
    galIdeleAut k K σ x = ideleAut (k := k) σ x := rfl

variable (k K) in
/-- **The Galois automorphisms fixing a given idele form a subgroup.** -/
noncomputable def stabilizerIdele (x : ↥(idele K)) : Subgroup Gal(K/k) where
  carrier := {σ : Gal(K/k) | ideleAut (k := k) σ x = x}
  one_mem' := by
    show ideleAut (k := k) (1 : Gal(K/k)) x = x
    rw [← galIdeleAut_apply (k := k) (K := K) 1 x, map_one]
    rfl
  mul_mem' {a b} ha hb := by
    show ideleAut (k := k) (a * b) x = x
    rw [← galIdeleAut_apply, map_mul]
    show galIdeleAut k K a (galIdeleAut k K b x) = x
    rw [galIdeleAut_apply, galIdeleAut_apply, hb, ha]
  inv_mem' {a} ha := by
    show ideleAut (k := k) a⁻¹ x = x
    have h : ideleAut (k := k) a⁻¹ (ideleAut (k := k) a x) = x := by
      show galIdeleAut k K a⁻¹ (galIdeleAut k K a x) = x
      rw [← AddAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    rwa [show ideleAut (k := k) a x = x from ha] at h

omit [NumberField k] in
theorem mem_stabilizerIdele {x : ↥(idele K)} {σ : Gal(K/k)} :
    σ ∈ stabilizerIdele k K x ↔ ideleAut (k := k) σ x = x := Iff.rfl

omit [NumberField k] in
/-- **An idele fixed by a generator of a cyclic Galois group is fixed by the whole group.** -/
theorem forall_ideleAut_eq_of_zpowers {σ : Gal(K/k)}
    (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ) {x : ↥(idele K)}
    (hx : ideleAut (k := k) σ x = x) (g : Gal(K/k)) : ideleAut (k := k) g x = x :=
  mem_stabilizerIdele.mp (Subgroup.zpowers_le.mpr (mem_stabilizerIdele.mpr hx) (hgen g))

/-! ### The ideles of the base field -/

variable [IsGalois k K]

variable (k K) in
/-- **A local unit of the base field at every place, viewed at the places of the extension**: at a
place of the extension, the image of the local unit at the place below. -/
noncomputable def fullIdeleComap : FullIdele k →+ FullIdele K :=
  (infiniteUnitsComapSections k (K := K)).prodMap (adicUnitsComapSections k (K := K))

variable (k K) in
omit [IsGalois k K] in
@[simp]
theorem fullIdeleComap_apply (x : FullIdele k) :
    fullIdeleComap k K x
      = (infiniteUnitsComapSections k x.1, adicUnitsComapSections k x.2) := rfl

variable (k K) in
/-- **The construction carries the ideles of the base field to the ideles of the extension**: the
places where the result fails to be a unit of the valuation ring lie above the finitely many places
where the given idele does. -/
theorem fullIdeleComap_mem_idele {x : FullIdele k} (hx : x ∈ idele k) :
    fullIdeleComap k K x ∈ idele K := by
  rw [mem_idele] at hx ⊢
  exact (eventually_unitVal_adicUnitsComapSections_eq_zero_iff k x.2).mpr hx

variable (k K) in
/-- **The ideles of the base field, viewed among the ideles of the extension.** -/
noncomputable def ideleComap : ↥(idele k) →+ ↥(idele K) :=
  AddMonoidHom.codRestrict ((fullIdeleComap k K).comp (idele k).subtype) (idele K)
    fun x => fullIdeleComap_mem_idele k K x.2

variable (k K) in
@[simp]
theorem coe_ideleComap (x : ↥(idele k)) :
    (ideleComap k K x : FullIdele K) = fullIdeleComap k K (x : FullIdele k) := rfl

variable (k K) in
/-- **Distinct ideles of the base field give distinct ideles of the extension.** -/
theorem ideleComap_injective : Function.Injective (ideleComap k K) := by
  intro x y h
  refine Subtype.ext (Prod.ext ?_ ?_)
  · exact infiniteUnitsComapSections_injective k (congrArg Prod.fst (congrArg Subtype.val h))
  · exact adicUnitsComapSections_injective k (congrArg Prod.snd (congrArg Subtype.val h))

/-! ### The fixed ideles -/

variable (k K) in
/-- **An idele coming from the base field is fixed by the Galois group.** -/
theorem ideleAut_ideleComap (σ : Gal(K/k)) (x : ↥(idele k)) :
    ideleAut (k := k) σ (ideleComap k K x) = ideleComap k K x := by
  refine Subtype.ext ?_
  rw [coe_ideleAut, coe_ideleComap, fullIdeleComap_apply, fullIdeleAut, prodAut_apply,
    familyAut_infiniteUnitsComapSections k σ, familyAut_adicUnitsComapSections k σ]

variable (k K) in
/-- **The ideles fixed by the Galois group are exactly the ideles of the base field.** -/
theorem mem_range_ideleComap_iff (x : ↥(idele K)) :
    x ∈ (ideleComap k K).range ↔ ∀ σ : Gal(K/k), ideleAut (k := k) σ x = x := by
  refine ⟨?_, fun hx => ?_⟩
  · rintro ⟨y, rfl⟩ σ
    exact ideleAut_ideleComap k K σ y
  · have hinf : ∀ σ : Gal(K/k),
        (infiniteRingFamily (k := k) (K := K)).unitsFamily.familyAut σ (x : FullIdele K).1
          = (x : FullIdele K).1 := fun σ =>
      congrArg Prod.fst (congrArg Subtype.val (hx σ))
    have hfin : ∀ σ : Gal(K/k),
        (adicRingFamily (k := k) (K := K)).unitsFamily.familyAut σ (x : FullIdele K).2
          = (x : FullIdele K).2 := fun σ =>
      congrArg Prod.snd (congrArg Subtype.val (hx σ))
    obtain ⟨y₁, hy₁⟩ :=
      (mem_range_infiniteUnitsComapSections_iff (K := K) k (x : FullIdele K).1).mpr hinf
    obtain ⟨y₂, hy₂⟩ :=
      (mem_range_adicUnitsComapSections_iff (K := K) k (x : FullIdele K).2).mpr hfin
    have hy : (y₁, y₂) ∈ idele k := by
      rw [mem_idele]
      refine (eventually_unitVal_adicUnitsComapSections_eq_zero_iff (K := K) k y₂).mp ?_
      rw [hy₂]
      exact x.2
    exact ⟨⟨(y₁, y₂), hy⟩, Subtype.ext (Prod.ext hy₁ hy₂)⟩

variable (k K) in
/-- **For a cyclic Galois group the ideles fixed by a generator are exactly the ideles of the base
field.** -/
theorem mem_range_ideleComap_iff_of_zpowers {σ : Gal(K/k)}
    (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ) (x : ↥(idele K)) :
    x ∈ (ideleComap k K).range ↔ ideleAut (k := k) σ x = x := by
  rw [mem_range_ideleComap_iff]
  exact ⟨fun h => h σ, fun h => forall_ideleAut_eq_of_zpowers hgen h⟩

end IdeleFixed

end InverseGalois.CFT

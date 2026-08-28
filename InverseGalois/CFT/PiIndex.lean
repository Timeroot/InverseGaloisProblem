/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The index of a product of subgroups

A subgroup of a product of abelian groups given place by place has a quotient that is the product
of the local quotients.  When all but finitely many of the local subgroups are everything, that
product is finite and its order is the product of the local indices over the exceptional set.

The same computation applies to a pair of such subgroups, one inside the other: transporting the
larger one to the product of its own local factors turns the relative index into the index of a
product of subgroups, so the relative index is the product of the local relative indices.  A
two-factor version is recorded alongside, for products presented as a pair rather than as a
family.

## Main definitions

* `InverseGalois.CFT.piSubtypeAddEquiv`: the sections of a family of subgroups, as the product of
  the subgroups.
* `InverseGalois.CFT.prodSubtypeAddEquiv`: the same for a product of two subgroups.

## Main results

* `InverseGalois.CFT.card_pi_of_subsingleton_outside`: a product of pointed types that are
  singletons outside a finite set has cardinality the product over that set.
* `InverseGalois.CFT.index_pi_of_eq_top_outside`: **the index of a product of subgroups** that are
  everything outside a finite set.
* `InverseGalois.CFT.relIndex_pi`: **the relative index of two products of subgroups** which agree
  outside a finite set.
* `InverseGalois.CFT.relIndex_prod`: the relative index of two products of two subgroups.

## Tags

subgroup, product, index, relative index
-/

namespace InverseGalois.CFT

/-! ### Products that are singletons almost everywhere -/

section Card

variable {ι : Type*} {Q : ι → Type*} [∀ i, Nonempty (Q i)]

/-- A product of pointed types that are singletons outside a finite set has cardinality the
product over that set. -/
theorem card_pi_of_subsingleton_outside (F : Finset ι)
    (hF : ∀ i, i ∉ F → Subsingleton (Q i)) :
    Nat.card (∀ i, Q i) = ∏ i ∈ F, Nat.card (Q i) := by
  classical
  haveI : ∀ i : {x // x ∉ F}, Unique (Q (i : ι)) := fun i => by
    haveI := hF (i : ι) i.2
    haveI : Inhabited (Q (i : ι)) := Classical.inhabited_of_nonempty inferInstance
    exact Unique.mk' _
  have hone : Nat.card (∀ i : {x // x ∉ F}, Q (i : ι)) = 1 := Nat.card_unique
  rw [Nat.card_congr (Equiv.piEquivPiSubtypeProd (fun i => i ∈ F) Q), Nat.card_prod, hone,
    mul_one, Nat.card_pi]
  exact Finset.prod_coe_sort F fun i => Nat.card (Q i)

end Card

/-! ### The index of a product of subgroups -/

section Index

variable {ι : Type*} {M : ι → Type*} [∀ i, AddGroup (M i)]

/-- **The index of a product of subgroups** that are everything outside a finite set. -/
theorem index_pi_of_eq_top_outside (N : ∀ i, AddSubgroup (M i)) (F : Finset ι)
    (hF : ∀ i, i ∉ F → N i = ⊤) :
    (AddSubgroup.pi Set.univ N).index = ∏ i ∈ F, (N i).index := by
  classical
  have hcard : Nat.card ((∀ i, M i) ⧸ AddSubgroup.pi Set.univ N)
      = Nat.card (∀ i, M i ⧸ N i) :=
    Nat.card_congr ((Quotient.congrRight fun x y => by
      rw [QuotientAddGroup.leftRel_pi]).trans (Setoid.piQuotientEquiv _).symm)
  rw [AddSubgroup.index, hcard]
  refine card_pi_of_subsingleton_outside F fun i hi => ?_
  rw [hF i hi]
  exact QuotientAddGroup.subsingleton_quotient_top

end Index

/-! ### The sections of a family of subgroups -/

section Sections

variable {ι : Type*} {M : ι → Type*} [∀ i, AddGroup (M i)]

/-- **The sections of a family of subgroups, as the product of the subgroups.** -/
def piSubtypeAddEquiv (P : ∀ i, AddSubgroup (M i)) :
    ↥(AddSubgroup.pi Set.univ P) ≃+ ∀ i, ↥(P i) where
  toFun x i := ⟨(x : ∀ i, M i) i, x.2 i (Set.mem_univ i)⟩
  invFun y := ⟨fun i => ((y i : M i)), fun i _ => (y i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem coe_piSubtypeAddEquiv (P : ∀ i, AddSubgroup (M i))
    (x : ↥(AddSubgroup.pi Set.univ P)) (i : ι) :
    ((piSubtypeAddEquiv P x i : ↥(P i)) : M i) = (x : ∀ i, M i) i :=
  rfl

end Sections

/-! ### The relative index of two products of subgroups -/

section RelIndex

variable {G G' : Type*} [AddGroup G] [AddGroup G']

/-- The relative index of a subgroup, read off through an isomorphism of the larger one. -/
theorem relIndex_eq_index_map (A B : AddSubgroup G) (C : AddSubgroup G') (e : ↥B ≃+ G')
    (h : AddSubgroup.map (e : ↥B →+ G') (A.addSubgroupOf B) = C) : A.relIndex B = C.index := by
  rw [← h, AddSubgroup.index_map_equiv _ e, AddSubgroup.relIndex]

end RelIndex

section RelIndexPi

variable {ι : Type*} {M : ι → Type*} [∀ i, AddGroup (M i)]

theorem map_piSubtypeAddEquiv_addSubgroupOf (N P : ∀ i, AddSubgroup (M i)) :
    AddSubgroup.map ((piSubtypeAddEquiv P : ↥(AddSubgroup.pi Set.univ P) ≃+ ∀ i, ↥(P i)) :
        ↥(AddSubgroup.pi Set.univ P) →+ ∀ i, ↥(P i))
        ((AddSubgroup.pi Set.univ N).addSubgroupOf (AddSubgroup.pi Set.univ P))
      = AddSubgroup.pi Set.univ fun i => (N i).addSubgroupOf (P i) := by
  ext y
  simp only [AddSubgroup.mem_map, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi,
    Set.mem_univ, true_implies]
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    exact hx i
  · intro hy
    refine ⟨(piSubtypeAddEquiv P).symm y, fun i => hy i, (piSubtypeAddEquiv P).apply_symm_apply y⟩

/-- **The relative index of two products of subgroups** which agree outside a finite set. -/
theorem relIndex_pi (N P : ∀ i, AddSubgroup (M i)) (F : Finset ι)
    (hF : ∀ i, i ∉ F → N i = P i) :
    (AddSubgroup.pi Set.univ N).relIndex (AddSubgroup.pi Set.univ P)
      = ∏ i ∈ F, (N i).relIndex (P i) := by
  rw [relIndex_eq_index_map _ _ _ (piSubtypeAddEquiv P)
    (map_piSubtypeAddEquiv_addSubgroupOf N P),
    index_pi_of_eq_top_outside _ F fun i hi => ?_]
  · rfl
  · rw [hF i hi]
    exact AddSubgroup.addSubgroupOf_self _

end RelIndexPi

/-! ### The relative index in a product of two groups -/

section RelIndexProd

variable {G H : Type*} [AddGroup G] [AddGroup H]

/-- **The sections of a product of two subgroups, as the product of the subgroups.** -/
def prodSubtypeAddEquiv (B : AddSubgroup G) (D : AddSubgroup H) :
    ↥(B.prod D) ≃+ ↥B × ↥D where
  toFun x := (⟨(x : G × H).1, x.2.1⟩, ⟨(x : G × H).2, x.2.2⟩)
  invFun y := ⟨((y.1 : G), (y.2 : H)), ⟨y.1.2, y.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem map_prodSubtypeAddEquiv_addSubgroupOf (A B : AddSubgroup G) (C D : AddSubgroup H) :
    AddSubgroup.map ((prodSubtypeAddEquiv B D : ↥(B.prod D) ≃+ ↥B × ↥D) :
        ↥(B.prod D) →+ ↥B × ↥D) ((A.prod C).addSubgroupOf (B.prod D))
      = (A.addSubgroupOf B).prod (C.addSubgroupOf D) := by
  ext y
  simp only [AddSubgroup.mem_map, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_prod]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx.1, hx.2⟩
  · intro hy
    exact ⟨(prodSubtypeAddEquiv B D).symm y, ⟨hy.1, hy.2⟩,
      (prodSubtypeAddEquiv B D).apply_symm_apply y⟩

/-- The relative index of two products of two subgroups. -/
theorem relIndex_prod (A B : AddSubgroup G) (C D : AddSubgroup H) :
    (A.prod C).relIndex (B.prod D) = A.relIndex B * C.relIndex D := by
  rw [relIndex_eq_index_map _ _ _ (prodSubtypeAddEquiv B D)
    (map_prodSubtypeAddEquiv_addSubgroupOf A B C D), AddSubgroup.index_prod]
  rfl

end RelIndexProd

end InverseGalois.CFT

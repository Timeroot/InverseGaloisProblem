/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.FamilyTorsion
import InverseGalois.CFT.TateCohomology.Pair

/-!
# The elements killed by an integer of a subgroup and of a product

Two elementary manipulations are needed before the elements of a module killed by an integer can be
read off place by place.  A subgroup that contains every element of the ambient module killed by an
integer has exactly those elements as its own, so passing to the subgroup changes nothing; and the
elements of a product killed by an integer are the pairs of elements killed by it, so a product of
two modules contributes the product of the two answers.

Both statements are needed for the group of ideles of a number field.  The ideles sit inside the
product of the local unit groups at all places, cut out by a finiteness condition that every element
of finite order satisfies automatically, and that product is a product of two halves, the infinite
places and the finite ones, indexed by different sets.

## Main definitions

* `InverseGalois.CFT.subTorsionEquiv`: the elements of a subgroup killed by an integer, when the
  subgroup contains them all.
* `InverseGalois.CFT.prodAutHom`: the action on a product of two modules.
* `InverseGalois.CFT.prodTorsionEquiv`: the elements of a product killed by an integer.

## Main results

* `InverseGalois.CFT.torsionSubIso`: **a subgroup containing every element killed by an integer has
  the same such elements as the ambient module**, as representations.
* `InverseGalois.CFT.torsionProdIso`: **the elements of a product killed by an integer are the
  product of the elements killed by it**, as representations.

## Tags

torsion, subgroup, product, representation, idele
-/

namespace InverseGalois.CFT

open CategoryTheory Tate

noncomputable section

/-! ### A subgroup containing all the torsion -/

section Sub

variable {V : Type} [AddCommGroup V] {L : AddSubgroup V} (m : ℤ)

/-- **The elements of a subgroup killed by an integer, when the subgroup contains every element of
the ambient module killed by it, are all of them.** -/
def subTorsionEquiv (hL : ∀ x : V, m • x = 0 → x ∈ L) :
    ↥(AddSubgroup.torsionBy ↥L m) ≃+ ↥(AddSubgroup.torsionBy V m) where
  toFun a := ⟨((a : ↥L) : V),
    mem_torsionBy.2 (congrArg Subtype.val (mem_torsionBy.1 a.2))⟩
  invFun b := ⟨⟨(b : V), hL _ (mem_torsionBy.1 b.2)⟩,
    mem_torsionBy.2 (Subtype.ext (mem_torsionBy.1 b.2))⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

@[simp]
theorem coe_subTorsionEquiv (hL : ∀ x : V, m • x = 0 → x ∈ L)
    (a : ↥(AddSubgroup.torsionBy ↥L m)) :
    ((subTorsionEquiv m hL a : ↥(AddSubgroup.torsionBy V m)) : V) = ((a : ↥L) : V) := rfl

variable {G : Type} [Group G] (φ : G →* AddAut V) (ψ : G →* AddAut ↥L)

/-- **A subgroup containing every element killed by an integer has the same such elements as the
ambient module**, as representations of the group. -/
def torsionSubIso (hψ : ∀ (g : G) (x : ↥L), ((ψ g x : ↥L) : V) = φ g (x : V))
    (hL : ∀ x : V, m • x = 0 → x ∈ L) :
    torsionRep ψ m ≅ torsionRep φ m :=
  Action.mkIso (subTorsionEquiv m hL).toIntLinearEquiv.toModuleIso fun g => by
    ext u
    exact Subtype.ext (hψ g u.1)

end Sub

/-! ### A product of two modules -/

section Prod

variable {G A B : Type} [Group G] [AddCommGroup A] [AddCommGroup B]
  (φ : G →* AddAut A) (ψ : G →* AddAut B)

/-- **The action on a product of two modules**, acting on each factor separately. -/
def prodAutHom : G →* AddAut (A × B) where
  toFun g := prodAut (φ g) (ψ g)
  map_one' := AddEquiv.ext fun z => by
    refine Prod.ext ?_ ?_
    · show φ 1 z.1 = z.1
      rw [map_one]
      rfl
    · show ψ 1 z.2 = z.2
      rw [map_one]
      rfl
  map_mul' g h := AddEquiv.ext fun z => by
    refine Prod.ext ?_ ?_
    · show φ (g * h) z.1 = φ g (φ h z.1)
      rw [map_mul]
      rfl
    · show ψ (g * h) z.2 = ψ g (ψ h z.2)
      rw [map_mul]
      rfl

@[simp]
theorem prodAutHom_apply (g : G) (z : A × B) : prodAutHom φ ψ g z = (φ g z.1, ψ g z.2) := rfl

variable (m : ℤ)

/-- **The elements of a product killed by an integer are the pairs of elements killed by it.** -/
def prodTorsionEquiv :
    ↥(AddSubgroup.torsionBy (A × B) m) ≃+
      ↥(AddSubgroup.torsionBy A m) × ↥(AddSubgroup.torsionBy B m) where
  toFun z :=
    (⟨(z : A × B).1, mem_torsionBy.2 (congrArg Prod.fst (mem_torsionBy.1 z.2))⟩,
      ⟨(z : A × B).2, mem_torsionBy.2 (congrArg Prod.snd (mem_torsionBy.1 z.2))⟩)
  invFun p := ⟨((p.1 : A), (p.2 : B)), mem_torsionBy.2
    (Prod.ext (mem_torsionBy.1 p.1.2) (mem_torsionBy.1 p.2.2))⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- **The elements of a product killed by an integer are the product of the elements killed by
it**, as representations of the group. -/
def torsionProdIso :
    torsionRep (prodAutHom φ ψ) m ≅ pairRep (torsionRep φ m) (torsionRep ψ m) :=
  Action.mkIso ((prodTorsionEquiv m).trans (piBoolEquiv (V := fun b =>
      ↥(pairFamily (torsionRep φ m) (torsionRep ψ m) b).V)).symm).toIntLinearEquiv.toModuleIso
    fun g => by
      ext u
      exact funext fun b => by cases b <;> rfl

end Prod

/-! ### Transporting along an equality of actions -/

section Cast

variable {G A : Type} [Group G] [Finite G] [AddCommGroup A] {φ ψ : G →* AddAut A}

/-- The complete cohomology of the elements killed by an integer is carried along an equality of
actions on the module. -/
def tateTorsionCast (h : φ = ψ) (m n : ℤ) :
    tateModule (torsionRep φ m) n ≃+ tateModule (torsionRep ψ m) n := by
  subst h
  exact AddEquiv.refl _

end Cast

end

end InverseGalois.CFT

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Shifting

/-!
# Presenting a representation by a free one

Every representation is the quotient of one whose underlying module is free: take the free module
on the elements of the representation and let the group permute the generators along its own
action.  The map that reads a formal combination of elements as the combination itself is
equivariant and onto, so it presents the representation.

The point of the construction is that the theorems which ask the coefficients to be flat — the
theorem of Tate and Nakayama above all — can then be applied to the free presentation, and what
they produce is carried down to the original coefficients by the map presenting them.  A
representation over the integers with torsion is out of reach of those theorems, but the free
module on its elements is not.

## Main definitions

* `InverseGalois.CFT.Tate.freeRep`: the free module on the elements of a representation, with the
  group permuting the generators.
* `InverseGalois.CFT.Tate.freeCounit`: the map reading a formal combination of elements as the
  combination itself.

## Main results

* `InverseGalois.CFT.Tate.freeCounit_surjective`: **every representation is a quotient of the free
  module on its elements.**
* `InverseGalois.CFT.Tate.flat_freeRep`: **the free module on the elements of a representation is
  flat.**

## Tags

representation, free module, presentation, flat, Tate cohomology
-/

namespace InverseGalois.CFT.Tate

open Representation

universe u

noncomputable section

variable {k G : Type u} [CommRing k] [Group G] (W : Rep k G)

/-! ### The free module on the elements of a representation -/

/-- **The group permuting the generators of the free module on the elements of a
representation.** -/
def freeRho : Representation k G (↥W.V →₀ k) where
  toFun g := Finsupp.lmapDomain k k (W.ρ g)
  map_one' := by
    refine LinearMap.ext fun f => ?_
    show Finsupp.mapDomain (⇑(W.ρ 1)) f = f
    rw [map_one]
    exact Finsupp.mapDomain_id
  map_mul' g h := by
    refine LinearMap.ext fun f => ?_
    show Finsupp.mapDomain (⇑(W.ρ (g * h))) f
      = Finsupp.mapDomain (⇑(W.ρ g)) (Finsupp.mapDomain (⇑(W.ρ h)) f)
    rw [map_mul, Module.End.coe_mul, Finsupp.mapDomain_comp]

@[simp]
theorem freeRho_apply (g : G) (f : ↥W.V →₀ k) :
    freeRho W g f = Finsupp.mapDomain (W.ρ g) f := rfl

/-- **The free module on the elements of a representation**, with the group permuting the
generators. -/
def freeRep : Rep k G := Rep.of (freeRho W)

@[simp]
theorem freeRep_ρ (g : G) (f : ↥W.V →₀ k) :
    (freeRep W).ρ g f = Finsupp.mapDomain (W.ρ g) f := rfl

/-- **The free module on the elements of a representation is flat.** -/
theorem flat_freeRep : Module.Flat k ↥(freeRep W).V :=
  inferInstanceAs (Module.Flat k (↥W.V →₀ k))

/-! ### The presentation -/

/-- **Reading a formal combination of elements of a representation as the combination itself.** -/
def freeCounitMap : (↥W.V →₀ k) →ₗ[k] ↥W.V := Finsupp.linearCombination k id

@[simp]
theorem freeCounitMap_single (w : ↥W.V) (c : k) :
    freeCounitMap W (Finsupp.single w c) = c • w :=
  Finsupp.linearCombination_single k c w

/-- **Reading a formal combination of elements as the combination itself is equivariant.** -/
theorem freeCounitMap_equivariant (g : G) :
    freeCounitMap W ∘ₗ (freeRep W).ρ g = W.ρ g ∘ₗ freeCounitMap W := by
  refine Finsupp.lhom_ext' fun w => LinearMap.ext_ring ?_
  show freeCounitMap W (Finsupp.mapDomain (W.ρ g) (Finsupp.single w 1))
    = W.ρ g (freeCounitMap W (Finsupp.single w 1))
  rw [Finsupp.mapDomain_single, freeCounitMap_single, freeCounitMap_single, one_smul, one_smul]

/-- **A representation is presented by the free module on its elements.** -/
def freeCounit : freeRep W ⟶ W :=
  mkHom (freeCounitMap W) (freeCounitMap_equivariant W)

@[simp]
theorem freeCounit_hom : (freeCounit W).hom.hom = freeCounitMap W := rfl

/-- **Every representation is a quotient of the free module on its elements.** -/
theorem freeCounit_surjective : Function.Surjective (freeCounit W).hom.hom := fun w =>
  ⟨Finsupp.single w 1, by
    show freeCounitMap W (Finsupp.single w 1) = w
    rw [freeCounitMap_single, one_smul]⟩

end

end InverseGalois.CFT.Tate

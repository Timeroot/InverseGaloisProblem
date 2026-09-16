/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.TensorOrbit

/-!
# A free action on the places leaves no cohomology outside the units

A finite group acts on an abelian group carrying a valuation onto the free abelian group on a set
of places the group permutes, and on a module.  A class of the first cohomology with coefficients
in the tensor product comes from the kernel of the valuation as soon as its valuation is a
coboundary at every place on the subgroup fixing that place.  **When no automorphism but the
identity fixes a place there is nothing to check**: a cocycle vanishes at the identity, so the
condition holds with the trivial correction, and *every* class comes from the kernel of the
valuation.

This is what makes the coefficients of an obstruction independent of the places it is read at.  In
the intended reading the abelian group is a group of units of a number field which are allowed
order at a prescribed set of places, and the set of places splits into a part carrying
decomposition groups and a part on which the Galois group acts freely because the places there
split completely.  Valuing only at the free part leaves coefficients in the units having no order
anywhere in the allowed set, a group whose rank is that of the field and which therefore does not
grow when the allowed set does.

## Main results

* `InverseGalois.CFT.mem_range_map_tensorSubInclRep_of_free`: **every class with coefficients in
  the tensor product comes from the kernel of the valuation, when the action on the places is
  free.**

## Tags

group cohomology, permutation module, free action, S-unit, tensor product, decomposition group
-/

namespace InverseGalois.CFT

open CategoryTheory MulAction TensorProduct groupCohomology

section Free

variable {Q : Type} [Group Q] [Finite Q] {A : Type} [CommGroup A] [MulDistribMulAction Q A]
variable (C : Type) [CommGroup C] [MulDistribMulAction Q C]
variable {X : Type} [MulAction Q X] [DecidableEq X]
variable (g : Additive A →+ (X →₀ ℤ))
variable (B : Subgroup A) [IsStableSubgroup Q B]

/-- **Every class with coefficients in the tensor product comes from the kernel of the valuation,
when no automorphism but the identity fixes a place.**  A one cocycle vanishes at the identity, so
its valuation at a place is a coboundary on the subgroup fixing that place for the trivial reason
that the subgroup is trivial. -/
theorem mem_range_map_tensorSubInclRep_of_free (hg : Function.Surjective g)
    (hB : ∀ a : A, a ∈ B ↔ g (Additive.ofMul a) = 0)
    (hgeq : ∀ (σ : Q) (a : A) (x : X),
      g (Additive.ofMul (σ • a)) x = g (Additive.ofMul a) (σ⁻¹ • x))
    (hfree : ∀ (x : X) (ρ : Q), ρ • x = x → ρ = 1)
    (y : H1 (Rep.ofDistribMulAction ℤ Q (Additive A ⊗[ℤ] Additive C))) :
    y ∈ LinearMap.range (groupCohomology.map (MonoidHom.id Q)
      (A := Rep.ofDistribMulAction ℤ Q (Additive ↥B ⊗[ℤ] Additive C))
      (tensorSubInclRep Q C B) 1).hom := by
  induction y using H1_induction_on with
  | @h z =>
    refine mem_range_map_tensorSubInclRep_of_forall_stabilizer C g B hg hB hgeq _ z.2 fun x => ?_
    refine ⟨0, fun ρ hρ => ?_⟩
    have hρ1 : ρ = 1 := hfree x ρ hρ
    subst hρ1
    have hone : z.1 1 = (0 : Additive A ⊗[ℤ] Additive C) := cocycles₁_map_one z
    rw [hone]
    simp

end Free

end InverseGalois.CFT

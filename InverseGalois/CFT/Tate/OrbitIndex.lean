/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Fibers

/-!
# Indexing the orbits by the fibres of an invariant map

The places of a Galois extension of number fields lying above one place of the base field form one
orbit of the Galois group, so the orbits are indexed by the places of the base field.  That
description of the orbits is the one arithmetic supplies, and the description as the quotient by the
orbit relation is the one the computation of a Herbrand quotient produces; this file compares them.

An invariant map out of a set carrying a group action, admitting a section that meets every orbit,
identifies the quotient by the orbit relation with the target of the map.  Under that identification
the canonical representative of an orbit and the value of the section lie in the same orbit, so any
invariant quantity may be summed or multiplied over either index set with the same result.  For the
order of the stabiliser this is the invariance of the order of a decomposition group along a place
of the base field.

## Main definitions

* `InverseGalois.CFT.orbitOut`: the canonical representative of an orbit, as a point of it.
* `InverseGalois.CFT.orbitsEquivOfFibers`: **the orbits are indexed by the target of an invariant
  map with a section meeting every orbit.**

## Main results

* `InverseGalois.CFT.prod_orbits_out_eq_prod_of_fibers`: an invariant quantity has the same product
  over the orbits and over the target of the map.
* `InverseGalois.CFT.prod_card_stabilizer_orbits_eq_of_fibers`: **the product of the orders of the
  stabilisers over the orbits is the product over the target of the map.**

## Tags

group action, orbit, invariant map, decomposition group, place
-/

namespace InverseGalois.CFT

open MulAction

section OrbitOut

variable {G X : Type*} [Group G] [MulAction G X]

/-- The canonical representative of an orbit, as a point of that orbit. -/
noncomputable def orbitOut (ω : orbitRel.Quotient G X) : ω.orbit :=
  ⟨ω.out, orbitRel.Quotient.mem_orbit.mpr ω.out_eq'⟩

@[simp]
theorem coe_orbitOut (ω : orbitRel.Quotient G X) : (orbitOut ω : X) = ω.out := rfl

end OrbitOut

section OrbitIndex

variable {G X I : Type*} [Group G] [MulAction G X] {f : X → I} {x₀ : I → X}
  (hf : ∀ (g : G) (x : X), f (g • x) = f x) (hsec : ∀ i : I, f (x₀ i) = i)
  (hfib : ∀ x : X, ∃ g : G, g • x₀ (f x) = x)

include hf hsec hfib

/-- **The orbits of a set carrying a group action are indexed by the target of an invariant map**
that admits a section meeting every orbit. -/
def orbitsEquivOfFibers : orbitRel.Quotient G X ≃ I where
  toFun := Quotient.lift f fun a b h => by
    obtain ⟨g, hg⟩ := orbitRel_apply.mp h
    rw [← hg, hf]
  invFun i := Quotient.mk'' (x₀ i)
  left_inv := by
    refine Quotient.ind fun x => Quotient.sound' ?_
    obtain ⟨g, hg⟩ := hfib x
    exact orbitRel_apply.mpr ⟨g⁻¹, inv_smul_eq_iff.mpr hg.symm⟩
  right_inv i := hsec i

@[simp]
theorem orbitsEquivOfFibers_symm_apply (i : I) :
    (orbitsEquivOfFibers hf hsec hfib).symm i = Quotient.mk'' (x₀ i) := rfl

theorem orbitsEquivOfFibers_apply (ω : orbitRel.Quotient G X) :
    orbitsEquivOfFibers hf hsec hfib ω = f ω.out := by
  conv_lhs => rw [← Quotient.out_eq' ω]
  rfl

/-- An invariant quantity has the same product over the orbits and over the target of the map. -/
theorem prod_orbits_out_eq_prod_of_fibers {M : Type*} [CommMonoid M] [Fintype I]
    [Fintype (orbitRel.Quotient G X)] (φ : X → M) (hφ : ∀ (g : G) (x : X), φ (g • x) = φ x) :
    ∏ ω : orbitRel.Quotient G X, φ ω.out = ∏ i : I, φ (x₀ i) := by
  refine Fintype.prod_equiv (orbitsEquivOfFibers hf hsec hfib) _ _ fun ω => ?_
  rw [orbitsEquivOfFibers_apply]
  obtain ⟨g, hg⟩ := hfib ω.out
  calc φ ω.out = φ (g • x₀ (f ω.out)) := by rw [hg]
    _ = φ (x₀ (f ω.out)) := hφ _ _

/-- **The product of the orders of the stabilisers over the orbits is the product over the target of
the map**: the order of a decomposition group depends only on the place of the base field. -/
theorem prod_card_stabilizer_orbits_eq_of_fibers [Fintype I]
    [Fintype (orbitRel.Quotient G X)] :
    ∏ ω : orbitRel.Quotient G X, (Nat.card ↥(stabilizer G ω.out) : ℚ)
      = ∏ i : I, (Nat.card ↥(stabilizer G (x₀ i)) : ℚ) :=
  prod_orbits_out_eq_prod_of_fibers hf hsec hfib
    (fun x => (Nat.card ↥(stabilizer G x) : ℚ)) fun g x =>
      congrArg Nat.cast
        (Nat.card_congr (stabilizerEquivStabilizer (a := x) (b := g • x) (g := g) rfl).symm.toEquiv)

end OrbitIndex

end InverseGalois.CFT

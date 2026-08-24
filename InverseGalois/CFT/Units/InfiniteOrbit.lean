/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.InfiniteFamily
import InverseGalois.CFT.Local.InfiniteHerbrand
import InverseGalois.CFT.Tate.FamilyOrbits
import InverseGalois.CFT.Tate.FamilyRestrictOrbit

/-!
# The local factor of the ideles at an infinite place of the base field

This is the archimedean counterpart of the local factor at a finite place.  The infinite places of a
cyclic extension of number fields lying above a fixed infinite place of the base field form one
orbit of the Galois group, the units of the completions at them form a family of modules over that
orbit, and the sections of the family are the local factor of the group of ideles there.

The sections over an orbit are the module induced from the decomposition group of one of its points,
and the units of the completion at an infinite place have Herbrand quotient the order of that group,
so the local factor does too: word for word the statement at a finite place.

## Main results

* `InverseGalois.CFT.stabAut_orbitFamily_infiniteUnits`: the action of the decomposition group of an
  infinite place on the units of the completion there, read off from the family of all completions.
* `InverseGalois.CFT.herbrand_orbitFamily_infiniteUnits`: **the local factor of the ideles at an
  infinite place of the base field has Herbrand quotient the order of the decomposition group.**
* `InverseGalois.CFT.exists_normHom_orbitFamily_infiniteUnits`: **a fixed section of the local factor
  at an infinite place of the base field is a norm as soon as its value at one place above it is a
  local norm.**

## Tags

number field, idele, infinite place, decomposition group, Herbrand quotient, family of modules
-/

namespace InverseGalois.CFT

open MulAction NumberField

section InfiniteOrbit

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
  {ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K)} (w₀ : ω.orbit)

/-- The stabiliser of an infinite place of the orbit, as a subgroup fixing the corresponding point
of the orbit. -/
theorem smul_orbit_of_mem_stabilizer_infinite
    (g : ↥(stabilizer Gal(K/k) (w₀ : InfinitePlace K))) : (g : Gal(K/k)) • w₀ = w₀ :=
  Subtype.ext (mem_stabilizer_iff.mp g.2)

/-- A Galois automorphism fixing a point of an orbit of infinite places fixes the underlying
place. -/
theorem mem_stabilizer_of_smul_orbit_infinite (g : Gal(K/k)) (h : g • w₀ = w₀) :
    g ∈ stabilizer Gal(K/k) (w₀ : InfinitePlace K) :=
  congrArg Subtype.val h

/-- **The action of the decomposition group of an infinite place on the units of the completion
there**, read off from the family of all completions. -/
theorem stabAut_orbitFamily_infiniteUnits (g : ↥(stabilizer Gal(K/k) (w₀ : InfinitePlace K)))
    (a : Additive (w₀ : InfinitePlace K).Completionˣ) :
    stabAut w₀ (smul_orbit_of_mem_stabilizer_infinite w₀)
        (orbitFamily (infiniteRingFamily (k := k) (K := K)).unitsFamily ω) g a
      = smulUnitsAut (G := ↥(stabilizer Gal(K/k) (w₀ : InfinitePlace K)))
          (R := (w₀ : InfinitePlace K).Completion) g a := by
  rw [stabAut_orbitFamily (infiniteRingFamily (k := k) (K := K)).unitsFamily w₀
    (smul_orbit_of_mem_stabilizer_infinite w₀) (fun h => mem_stabilizer_iff.mp h.2) g a]
  exact transport_infiniteUnitsFamily _ (g : Gal(K/k)) (mem_stabilizer_iff.mp g.2) a

/-- **The local factor of the ideles at an infinite place of the base field has Herbrand quotient
the order of the decomposition group.**  The units of the completions at the places above it are a
family of modules over one orbit of the Galois group, whose sections are the module induced from the
decomposition group of one of them. -/
theorem herbrand_orbitFamily_infiniteUnits [IsGalois k K] [Finite Gal(K/k)] [Fintype ω.orbit]
    {σ : Gal(K/k)} (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ) {n : ℕ}
    (hn : Nat.card Gal(K/k) = n) :
    herbrand ((orbitFamily (infiniteRingFamily (k := k) (K := K)).unitsFamily ω).familyAut σ) n
      = Nat.card ↥(stabilizer Gal(K/k) (w₀ : InfinitePlace K)) := by
  haveI : Fintype ↥(stabilizer Gal(K/k) (w₀ : InfinitePlace K)) := Fintype.ofFinite _
  have hstab : stabilizer Gal(K/k) w₀ = stabilizer Gal(K/k) (w₀ : InfinitePlace K) :=
    stabilizer_orbit_coe w₀
  have hstabcard : Nat.card ↥(stabilizer Gal(K/k) w₀)
      = Nat.card ↥(stabilizer Gal(K/k) (w₀ : InfinitePlace K)) :=
    congrArg (fun H : Subgroup Gal(K/k) => Nat.card ↥H) hstab
  have hH : ∀ g : Gal(K/k), g • w₀ = w₀ →
      g ∈ stabilizer Gal(K/k) (w₀ : InfinitePlace K) := fun _ h => congrArg Subtype.val h
  have hgen' : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ⁻¹ := fun g => by
    rw [Subgroup.zpowers_inv]
    exact hgen g
  have hdm : period (orbitShift ↥ω.orbit σ) w₀
      * Nat.card ↥(stabilizer Gal(K/k) (w₀ : InfinitePlace K)) = n := by
    rw [show orbitShift (↥ω.orbit) σ = (toPerm σ⁻¹ : Equiv.Perm ↥ω.orbit) from rfl,
      period_eq_card_orbit hgen' w₀, ← hstabcard, card_orbit_mul_card_stabilizer, hn]
  have hσn : σ ^ n = 1 := by
    rw [← hn]
    exact pow_card_eq_one'
  have hturn : (orbitTurn σ w₀ hH)
      ^ Nat.card ↥(stabilizer Gal(K/k) (w₀ : InfinitePlace K)) = 1 :=
    orbitTurn_pow w₀ hH hσn hdm
  have key : stabAut w₀ (smul_orbit_of_mem_stabilizer_infinite w₀)
        (orbitFamily (infiniteRingFamily (k := k) (K := K)).unitsFamily ω) (orbitTurn σ w₀ hH)
      = smulUnitsAut (G := ↥(stabilizer Gal(K/k) (w₀ : InfinitePlace K)))
          (R := (w₀ : InfinitePlace K).Completion) (orbitTurn σ w₀ hH) :=
    AddEquiv.ext (stabAut_orbitFamily_infiniteUnits w₀ (orbitTurn σ w₀ hH))
  rw [herbrand_familyAut_orbit w₀ (exists_pow_orbitShift_apply_eq w₀ hgen) hH
    (smul_orbit_of_mem_stabilizer_infinite w₀) _ hturn hdm, key]
  exact herbrand_infiniteUnits_eq_card (w₀ : InfinitePlace K)
    (mem_zpowers_orbitTurn w₀ hH hgen (smul_orbit_of_mem_stabilizer_infinite w₀)) rfl

/-- **A fixed section of the units of the completions above an infinite place of the base field is a
norm as soon as its value at one of those places is a local norm** for the decomposition group
there.  The places above the given one form a single orbit, and the sections over it are the module
induced from the decomposition group of any one of them. -/
theorem exists_normHom_orbitFamily_infiniteUnits [Finite Gal(K/k)] [Fintype ω.orbit]
    {σ : Gal(K/k)} (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ) {n : ℕ}
    (hn : Nat.card Gal(K/k) = n)
    (hH : ∀ g : Gal(K/k), g • w₀ = w₀ → g ∈ stabilizer Gal(K/k) (w₀ : InfinitePlace K))
    {f : ∀ z : ω.orbit, Additive (z : InfinitePlace K).Completionˣ}
    (hf : (orbitFamily (infiniteRingFamily (k := k) (K := K)).unitsFamily ω).familyAut σ f = f)
    (h : ∃ b, normHom (smulUnitsAut (G := ↥(stabilizer Gal(K/k) (w₀ : InfinitePlace K)))
        (R := (w₀ : InfinitePlace K).Completion) (orbitTurn σ w₀ hH))
        (Nat.card ↥(stabilizer Gal(K/k) (w₀ : InfinitePlace K))) b = f w₀) :
    ∃ u,
      normHom ((orbitFamily (infiniteRingFamily (k := k) (K := K)).unitsFamily ω).familyAut σ) n u
        = f := by
  haveI : Fintype ↥(stabilizer Gal(K/k) (w₀ : InfinitePlace K)) := Fintype.ofFinite _
  have hstabcard : Nat.card ↥(stabilizer Gal(K/k) w₀)
      = Nat.card ↥(stabilizer Gal(K/k) (w₀ : InfinitePlace K)) :=
    congrArg (fun H : Subgroup Gal(K/k) => Nat.card ↥H) (stabilizer_orbit_coe w₀)
  have key : stabAut w₀ (smul_orbit_of_mem_stabilizer_infinite w₀)
        (orbitFamily (infiniteRingFamily (k := k) (K := K)).unitsFamily ω) (orbitTurn σ w₀ hH)
      = smulUnitsAut (G := ↥(stabilizer Gal(K/k) (w₀ : InfinitePlace K)))
          (R := (w₀ : InfinitePlace K).Completion) (orbitTurn σ w₀ hH) :=
    AddEquiv.ext (stabAut_orbitFamily_infiniteUnits w₀ (orbitTurn σ w₀ hH))
  refine exists_normHom_familyAut_orbit w₀ (exists_pow_orbitShift_apply_eq w₀ hgen) hH
    (smul_orbit_of_mem_stabilizer_infinite w₀) _ (orbitTurn_pow_card w₀ hH rfl)
    (period_orbitShift_mul_card w₀ hgen hn hstabcard) hf ?_
  rw [key]
  exact h

end InfiniteOrbit

end InverseGalois.CFT

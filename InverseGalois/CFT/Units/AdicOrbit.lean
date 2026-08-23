/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.AdicFamily
import InverseGalois.CFT.Local.AdicHerbrand
import InverseGalois.CFT.Tate.FamilyOrbits

/-!
# The local factor of the ideles at a finite place of the base field

The finite places of a cyclic extension of number fields lying above a fixed place of the base field
form one orbit of the Galois group, and the units of the completions at them form a family of
modules over that orbit.  The sections of the family are the local factor of the group of ideles
there.

Restricting the family of all completions to one orbit and applying the presentation of the sections
over an orbit as an induced module computes the Herbrand quotient of that local factor: it is the
Herbrand quotient of the units of the completion at one of the places for the action of its
decomposition group, and that is the order of the decomposition group.

## Main results

* `InverseGalois.CFT.stabAut_orbitFamily_adicUnits`: the action of the decomposition group of a
  place on the units of the completion there, read off from the family of all completions.
* `InverseGalois.CFT.herbrand_orbitFamily_adicUnits`: **the local factor of the ideles at a finite
  place of the base field has Herbrand quotient the order of the decomposition group.**

## Tags

number field, idele, decomposition group, Herbrand quotient, family of modules
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

section AdicOrbit

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [NumberField K]
  {ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K))} (v₀ : ω.orbit)

omit [NumberField K] in
/-- The stabiliser of a place of the orbit, as a subgroup fixing the corresponding point of the
orbit. -/
theorem smul_orbit_of_mem_stabilizer
    (g : ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K)))) : (g : Gal(K/k)) • v₀ = v₀ :=
  Subtype.ext (mem_stabilizer_iff.mp g.2)

/-- **The action of the decomposition group of a place on the units of the completion there**, read
off from the family of all completions. -/
theorem stabAut_orbitFamily_adicUnits
    (g : ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K))))
    (a : Additive ((v₀ : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ) :
    stabAut v₀ (smul_orbit_of_mem_stabilizer v₀)
        (orbitFamily (adicRingFamily (k := k) (K := K)).unitsFamily ω) g a
      = smulUnitsAut (G := ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K))))
          (R := (v₀ : HeightOneSpectrum (𝓞 K)).adicCompletion K) g a := by
  rw [stabAut_orbitFamily (adicRingFamily (k := k) (K := K)).unitsFamily v₀
    (smul_orbit_of_mem_stabilizer v₀) (fun h => mem_stabilizer_iff.mp h.2) g a]
  exact transport_adicUnitsFamily _ (g : Gal(K/k)) (mem_stabilizer_iff.mp g.2) a

/-- **The local factor of the ideles at a finite place of the base field has Herbrand quotient the
order of the decomposition group.**  The units of the completions at the places above it are a
family of modules over one orbit of the Galois group, whose sections are the module induced from the
decomposition group of one of them. -/
theorem herbrand_orbitFamily_adicUnits [Finite Gal(K/k)] [Fintype ω.orbit] {σ : Gal(K/k)}
    (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ) {n : ℕ} (hn : Nat.card Gal(K/k) = n) :
    herbrand ((orbitFamily (adicRingFamily (k := k) (K := K)).unitsFamily ω).familyAut σ) n
      = Nat.card ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K))) := by
  haveI : Fintype ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K))) := Fintype.ofFinite _
  haveI : NeZero (Nat.card ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K)))) :=
    ⟨Nat.card_pos.ne'⟩
  have hstab : stabilizer Gal(K/k) v₀ = stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K)) :=
    stabilizer_orbit_coe v₀
  have hstabcard : Nat.card ↥(stabilizer Gal(K/k) v₀)
      = Nat.card ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K))) :=
    congrArg (fun H : Subgroup Gal(K/k) => Nat.card ↥H) hstab
  have hH : ∀ g : Gal(K/k), g • v₀ = v₀ →
      g ∈ stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K)) := fun _ h => congrArg Subtype.val h
  have hgen' : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ⁻¹ := fun g => by
    rw [Subgroup.zpowers_inv]
    exact hgen g
  have hdm : period (orbitShift ↥ω.orbit σ) v₀
      * Nat.card ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K))) = n := by
    rw [show orbitShift (↥ω.orbit) σ = (toPerm σ⁻¹ : Equiv.Perm ↥ω.orbit) from rfl,
      period_eq_card_orbit hgen' v₀, ← hstabcard, card_orbit_mul_card_stabilizer, hn]
  have hσn : σ ^ n = 1 := by
    rw [← hn]
    exact pow_card_eq_one'
  have hturn : (orbitTurn σ v₀ hH)
      ^ Nat.card ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K))) = 1 :=
    orbitTurn_pow v₀ hH hσn hdm
  have key : stabAut v₀ (smul_orbit_of_mem_stabilizer v₀)
        (orbitFamily (adicRingFamily (k := k) (K := K)).unitsFamily ω) (orbitTurn σ v₀ hH)
      = smulUnitsAut (G := ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K))))
          (R := (v₀ : HeightOneSpectrum (𝓞 K)).adicCompletion K) (orbitTurn σ v₀ hH) :=
    AddEquiv.ext (stabAut_orbitFamily_adicUnits v₀ (orbitTurn σ v₀ hH))
  rw [herbrand_familyAut_orbit v₀ (exists_pow_orbitShift_apply_eq v₀ hgen) hH
    (smul_orbit_of_mem_stabilizer v₀) _ hturn hdm, key]
  exact herbrand_adicUnits_eq_card (v₀ : HeightOneSpectrum (𝓞 K))
    (mem_zpowers_orbitTurn v₀ hH hgen (smul_orbit_of_mem_stabilizer v₀)) hturn rfl

end AdicOrbit

end InverseGalois.CFT

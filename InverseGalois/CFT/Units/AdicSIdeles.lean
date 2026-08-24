/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.FamilyRestrictOrbit
import InverseGalois.CFT.Tate.OrbitIndex
import InverseGalois.CFT.Units.AdicOrbit

/-!
# The finite part of the ideles that are units outside a set of places

Fix a set of finite places of a Galois extension of number fields, stable under the Galois group.
An idele that is a unit outside that set is, at each place, an element of a subgroup of the local
factor: the whole multiplicative group of the completion at a place of the set, and the units of the
valuation ring at every other place.  Those subgroups are carried onto one another by the Galois
transports, because the transports are isometries, so they form an invariant family of subgroups of
the family of unit groups of the completions.

The contribution of one orbit to the Herbrand quotient is then read off from the ambient
computation.  Above a place of the set the subgroup is everything, so the orbit contributes the
order of the decomposition group; above a place outside the set the subgroup is the units of the
valuation ring, and if the decomposition group fixes a uniformizer — that is, if the place is
unramified — both Tate groups of the orbit vanish.

## Main definitions

* `InverseGalois.CFT.adicSUnits`: **the local subgroup at a place**: everything inside the set, the
  units of the valuation ring outside it.
* `InverseGalois.CFT.adicSIdeleFamily`: **the family of local subgroups whose sections are the
  finite part of the ideles that are units outside the set.**

## Main results

* `InverseGalois.CFT.unitVal_adicUnitsFamily_map`: the Galois transports preserve the valuation of a
  unit.
* `InverseGalois.CFT.map_adicSUnits`: the family of local subgroups is invariant.
* `InverseGalois.CFT.herbrand_orbitFamily_adicSUnits_of_mem`: **an orbit above a place of the set
  contributes the order of the decomposition group.**
* `InverseGalois.CFT.subsingleton_tate_orbitFamily_adicSUnits_of_notMem`: **an unramified orbit above
  a place outside the set contributes nothing.**
* `InverseGalois.CFT.exists_normHom_orbitFamily_adicSUnits_of_mem`: **a fixed section over an orbit
  above a place of the set is a norm as soon as its value at one place above it is a local norm.**
* `InverseGalois.CFT.exists_normHom_orbitFamily_adicSUnits_of_notMem`: **a fixed section over an
  unramified orbit above a place outside the set is always a norm.**
* `InverseGalois.CFT.exists_normHom_adicSIdeleFamily`: **the finite part of an idele that is a unit
  outside the set is a norm as soon as it is a local norm at one place above each place of the
  set**, provided every place outside the set is unramified.

## Tags

number field, idele, S-unit, decomposition group, Herbrand quotient, family of modules
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped WithZero

section AdicSIdeles

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [NumberField K]

/-! ### The Galois transports preserve the valuation -/

/-- **The Galois transports preserve the valuation of a unit**, because the isomorphism between the
completion at a place and the completion at its image is an isometry. -/
theorem unitVal_adicUnitsFamily_map (g : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K))
    (a : Additive (v.adicCompletion K)ˣ) :
    unitVal ((adicRingFamily (k := k) (K := K)).unitsFamily.map g v a) = unitVal a := by
  show WithZero.log (Valued.v (adicCompletionGalEquiv v g
      ((Additive.toMul a : (v.adicCompletion K)ˣ) : v.adicCompletion K)))
    = WithZero.log (Valued.v ((Additive.toMul a : (v.adicCompletion K)ˣ) : v.adicCompletion K))
  rw [valued_adicCompletionGalEquiv]

/-! ### The family of local subgroups -/

variable (T : Set (HeightOneSpectrum (𝓞 K))) [DecidablePred (· ∈ T)]

/-- **The local subgroup at a place** cut out by a set of places: the whole group of units of the
completion at a place of the set, and the units of the valuation ring at every other place. -/
def adicSUnits (v : HeightOneSpectrum (𝓞 K)) : AddSubgroup (Additive (v.adicCompletion K)ˣ) :=
  if v ∈ T then ⊤ else (unitVal (A := v.adicCompletion K)).ker

theorem adicSUnits_of_mem {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ T) : adicSUnits T v = ⊤ :=
  if_pos hv

theorem adicSUnits_of_notMem {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ T) :
    adicSUnits T v = (unitVal (A := v.adicCompletion K)).ker :=
  if_neg hv

variable (hT : ∀ (g : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), g • v ∈ T ↔ v ∈ T)

include hT

/-- **The family of local subgroups cut out by an invariant set of places is invariant.** -/
theorem map_adicSUnits (g : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)) :
    (adicSUnits T v).map ((adicRingFamily (k := k) (K := K)).unitsFamily.map g v).toAddMonoidHom
      = adicSUnits T (g • v) := by
  by_cases hv : v ∈ T
  · rw [adicSUnits_of_mem T hv, adicSUnits_of_mem T ((hT g v).mpr hv)]
    exact AddSubgroup.map_top_of_surjective _
      ((adicRingFamily (k := k) (K := K)).unitsFamily.map g v).surjective
  · rw [adicSUnits_of_notMem T hv, adicSUnits_of_notMem T fun h => hv ((hT g v).mp h)]
    ext b
    simp only [AddSubgroup.mem_map, AddMonoidHom.mem_ker, AddEquiv.coe_toAddMonoidHom]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [unitVal_adicUnitsFamily_map]
      exact ha
    · intro hb
      refine ⟨((adicRingFamily (k := k) (K := K)).unitsFamily.map g v).symm b, ?_,
        ((adicRingFamily (k := k) (K := K)).unitsFamily.map g v).apply_symm_apply b⟩
      rw [← unitVal_adicUnitsFamily_map g v, AddEquiv.apply_symm_apply]
      exact hb

/-- **The family of local subgroups whose sections are the finite part of the ideles that are units
outside a set of places.** -/
noncomputable def adicSIdeleFamily : FamilyAction (fun v => ↥(adicSUnits T v)) Gal(K/k) :=
  (adicRingFamily (k := k) (K := K)).unitsFamily.restrict (adicSUnits T) (map_adicSUnits T hT)

theorem adicSIdeleFamily_eq :
    adicSIdeleFamily T hT
      = (adicRingFamily (k := k) (K := K)).unitsFamily.restrict (adicSUnits T)
          (map_adicSUnits T hT) :=
  rfl

end AdicSIdeles

/-! ### The contribution of one orbit -/

section Orbit

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [NumberField K]
  {ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K))} (v₀ : ω.orbit)

omit [NumberField K] in
/-- A Galois automorphism fixing a point of an orbit fixes the underlying place. -/
theorem mem_stabilizer_of_smul_orbit (g : Gal(K/k)) (h : g • v₀ = v₀) :
    g ∈ stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K)) :=
  congrArg Subtype.val h

variable [Finite Gal(K/k)] [Fintype ω.orbit] (T : Set (HeightOneSpectrum (𝓞 K)))
  [DecidablePred (· ∈ T)]
  (hT : ∀ (g : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), g • v ∈ T ↔ v ∈ T)
  {σ : Gal(K/k)} (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ) {n : ℕ}
  (hn : Nat.card Gal(K/k) = n)

include hT hgen hn

/-- **An orbit above a place of the set contributes the order of the decomposition group**, exactly
as it does to the whole finite part of the ideles: the local subgroup there is everything. -/
theorem herbrand_orbitFamily_adicSUnits_of_mem (hv₀ : (v₀ : HeightOneSpectrum (𝓞 K)) ∈ T) :
    herbrand ((orbitFamily (adicSIdeleFamily T hT) ω).familyAut σ) n
      = Nat.card ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K))) := by
  haveI : Fintype ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K))) := Fintype.ofFinite _
  have hstabcard : Nat.card ↥(stabilizer Gal(K/k) v₀)
      = Nat.card ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K))) :=
    congrArg (fun H : Subgroup Gal(K/k) => Nat.card ↥H) (stabilizer_orbit_coe v₀)
  rw [adicSIdeleFamily_eq, herbrand_orbitFamily_restrict_top
    (adicRingFamily (k := k) (K := K)).unitsFamily (adicSUnits T) (map_adicSUnits T hT) v₀
    (exists_pow_orbitShift_apply_eq v₀ hgen) (mem_stabilizer_of_smul_orbit v₀)
    (smul_orbit_of_mem_stabilizer v₀) (fun g => mem_stabilizer_iff.mp g.2)
    (orbitTurn_pow_card v₀ (mem_stabilizer_of_smul_orbit v₀) rfl)
    (period_orbitShift_mul_card v₀ hgen hn hstabcard) (adicSUnits_of_mem T hv₀)]
  exact herbrand_orbitFamily_adicUnits v₀ hgen hn

/-- **An unramified orbit above a place outside the set contributes nothing**: the local subgroup
there is the units of the valuation ring, and both of their Tate groups vanish when the
decomposition group fixes a uniformizer. -/
theorem subsingleton_tate_orbitFamily_adicSUnits_of_notMem
    (hv₀ : (v₀ : HeightOneSpectrum (𝓞 K)) ∉ T)
    (π : ((v₀ : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ)
    (hπfix : ∀ g : ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K))),
      g • (π : (v₀ : HeightOneSpectrum (𝓞 K)).adicCompletion K)
        = (π : (v₀ : HeightOneSpectrum (𝓞 K)).adicCompletion K))
    (hπval : unitVal (Additive.ofMul π) = 1) :
    Subsingleton (tateH0 ((orbitFamily (adicSIdeleFamily T hT) ω).familyAut σ) n)
      ∧ Subsingleton (tateHm1 ((orbitFamily (adicSIdeleFamily T hT) ω).familyAut σ) n) := by
  haveI : Fintype ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K))) := Fintype.ofFinite _
  haveI : NeZero (Nat.card ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K)))) :=
    ⟨Nat.card_pos.ne'⟩
  have hstabcard : Nat.card ↥(stabilizer Gal(K/k) v₀)
      = Nat.card ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K))) :=
    congrArg (fun H : Subgroup Gal(K/k) => Nat.card ↥H) (stabilizer_orbit_coe v₀)
  have hz := orbitTurn_pow_card (σ := σ) v₀ (mem_stabilizer_of_smul_orbit v₀) rfl
  have hsub := subsingleton_tate_adicUnits (k := k) (v₀ : HeightOneSpectrum (𝓞 K))
    (mem_zpowers_orbitTurn v₀ (mem_stabilizer_of_smul_orbit v₀) hgen
      (smul_orbit_of_mem_stabilizer v₀)) hz rfl π hπfix hπval
  rw [adicSIdeleFamily_eq]
  exact ⟨subsingleton_tateH0_orbitFamily_restrict
      (adicRingFamily (k := k) (K := K)).unitsFamily (adicSUnits T) (map_adicSUnits T hT) v₀
      (exists_pow_orbitShift_apply_eq v₀ hgen) (mem_stabilizer_of_smul_orbit v₀)
      (smul_orbit_of_mem_stabilizer v₀) (fun g => mem_stabilizer_iff.mp g.2) hz
      (period_orbitShift_mul_card v₀ hgen hn hstabcard) (adicSUnits_of_notMem T hv₀) _
      (fun a => (stabAut_orbitFamily_adicUnits v₀ _ _).symm) hsub.1,
    subsingleton_tateHm1_orbitFamily_restrict
      (adicRingFamily (k := k) (K := K)).unitsFamily (adicSUnits T) (map_adicSUnits T hT) v₀
      (exists_pow_orbitShift_apply_eq v₀ hgen) (mem_stabilizer_of_smul_orbit v₀)
      (smul_orbit_of_mem_stabilizer v₀) (fun g => mem_stabilizer_iff.mp g.2) hz
      (period_orbitShift_mul_card v₀ hgen hn hstabcard) (adicSUnits_of_notMem T hv₀) _
      (fun a => (stabAut_orbitFamily_adicUnits v₀ _ _).symm) hsub.2⟩

/-- **A fixed section over an orbit above a place of the set is a norm as soon as its value at one
place above it is a local norm.**  The local subgroup at a place of the set is the whole group of
units of the completion there, so nothing is lost by reading the statement in the ambient family. -/
theorem exists_normHom_orbitFamily_adicSUnits_of_mem (hv₀ : (v₀ : HeightOneSpectrum (𝓞 K)) ∈ T)
    (hH : ∀ g : Gal(K/k), g • v₀ = v₀ → g ∈ stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K)))
    {f : ∀ z : ω.orbit, ↥(adicSUnits T (z : HeightOneSpectrum (𝓞 K)))}
    (hf : (orbitFamily (adicSIdeleFamily T hT) ω).familyAut σ f = f)
    (h : ∃ b, normHom (smulUnitsAut (G := ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K))))
        (R := (v₀ : HeightOneSpectrum (𝓞 K)).adicCompletion K) (orbitTurn σ v₀ hH))
        (Nat.card ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K)))) b
      = ((f v₀ : ↥(adicSUnits T (v₀ : HeightOneSpectrum (𝓞 K)))) :
          Additive ((v₀ : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ)) :
    ∃ u, normHom ((orbitFamily (adicSIdeleFamily T hT) ω).familyAut σ) n u = f := by
  haveI : Fintype ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K))) := Fintype.ofFinite _
  have hstabcard : Nat.card ↥(stabilizer Gal(K/k) v₀)
      = Nat.card ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K))) :=
    congrArg (fun H : Subgroup Gal(K/k) => Nat.card ↥H) (stabilizer_orbit_coe v₀)
  have key : stabAut v₀ (smul_orbit_of_mem_stabilizer v₀)
        (orbitFamily (adicRingFamily (k := k) (K := K)).unitsFamily ω) (orbitTurn σ v₀ hH)
      = smulUnitsAut (G := ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K))))
          (R := (v₀ : HeightOneSpectrum (𝓞 K)).adicCompletion K) (orbitTurn σ v₀ hH) :=
    AddEquiv.ext (stabAut_orbitFamily_adicUnits v₀ (orbitTurn σ v₀ hH))
  refine exists_normHom_orbitFamily_restrict_top
    (adicRingFamily (k := k) (K := K)).unitsFamily (adicSUnits T) (map_adicSUnits T hT) v₀
    (exists_pow_orbitShift_apply_eq v₀ hgen) hH (smul_orbit_of_mem_stabilizer v₀)
    (fun g => mem_stabilizer_iff.mp g.2) (orbitTurn_pow_card v₀ hH rfl)
    (period_orbitShift_mul_card v₀ hgen hn hstabcard) (adicSUnits_of_mem T hv₀) hf ?_
  rw [key]
  exact h

/-- **A fixed section over an unramified orbit above a place outside the set is always a norm**: the
local subgroup there is the units of the valuation ring, whose upper Tate group vanishes. -/
theorem exists_normHom_orbitFamily_adicSUnits_of_notMem
    (hv₀ : (v₀ : HeightOneSpectrum (𝓞 K)) ∉ T)
    (π : ((v₀ : HeightOneSpectrum (𝓞 K)).adicCompletion K)ˣ)
    (hπfix : ∀ g : ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K))),
      g • (π : (v₀ : HeightOneSpectrum (𝓞 K)).adicCompletion K)
        = (π : (v₀ : HeightOneSpectrum (𝓞 K)).adicCompletion K))
    (hπval : unitVal (Additive.ofMul π) = 1)
    {f : ∀ z : ω.orbit, ↥(adicSUnits T (z : HeightOneSpectrum (𝓞 K)))}
    (hf : (orbitFamily (adicSIdeleFamily T hT) ω).familyAut σ f = f) :
    ∃ u, normHom ((orbitFamily (adicSIdeleFamily T hT) ω).familyAut σ) n u = f :=
  haveI := (subsingleton_tate_orbitFamily_adicSUnits_of_notMem v₀ T hT hgen hn hv₀ π hπfix hπval).1
  exists_normHom_of_subsingleton f hf

end Orbit

/-! ### All the orbits at once -/

section AllOrbits

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [NumberField K] [Finite Gal(K/k)]
  (T : Set (HeightOneSpectrum (𝓞 K))) [DecidablePred (· ∈ T)]
  (hT : ∀ (g : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), g • v ∈ T ↔ v ∈ T)
  {σ : Gal(K/k)} (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ) {n : ℕ}
  (hn : Nat.card Gal(K/k) = n)

include hT hgen hn

/-- **The finite part of an idele that is a unit outside the set is a norm as soon as it is a local
norm at one place above each place of the set.**  At a place outside the set nothing has to be
assumed, because there the local subgroup is the units of the valuation ring and every fixed element
of them is already a norm once the decomposition group fixes a uniformizer. -/
theorem exists_normHom_adicSIdeleFamily
    (hunram : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T →
      ∃ π : (v.adicCompletion K)ˣ,
        (∀ g : ↥(stabilizer Gal(K/k) v),
            g • (π : v.adicCompletion K) = (π : v.adicCompletion K))
          ∧ unitVal (Additive.ofMul π) = 1)
    {f : ∀ v : HeightOneSpectrum (𝓞 K), ↥(adicSUnits T v)}
    (hf : (adicSIdeleFamily T hT).familyAut σ f = f)
    (h : ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)), ω.out ∈ T → ∃ b,
      normHom (smulUnitsAut (G := ↥(stabilizer Gal(K/k) ω.out))
          (R := (ω.out).adicCompletion K)
          (orbitTurn σ (orbitOut ω) (mem_stabilizer_of_smul_orbit (orbitOut ω))))
        (Nat.card ↥(stabilizer Gal(K/k) ω.out)) b
      = ((f ω.out : ↥(adicSUnits T ω.out)) : Additive ((ω.out).adicCompletion K)ˣ)) :
    ∃ u, normHom ((adicSIdeleFamily T hT).familyAut σ) n u = f := by
  refine exists_normHom_familyAut_orbits (adicSIdeleFamily T hT) σ n fun ω => ?_
  haveI : Fintype ω.orbit := Fintype.ofFinite _
  by_cases hv : ω.out ∈ T
  · exact exists_normHom_orbitFamily_adicSUnits_of_mem (orbitOut ω) T hT hgen hn hv
      (mem_stabilizer_of_smul_orbit (orbitOut ω)) (familyAut_orbitFamily_restrict _ hf) (h ω hv)
  · obtain ⟨π, hπfix, hπval⟩ := hunram _ hv
    exact exists_normHom_orbitFamily_adicSUnits_of_notMem (orbitOut ω) T hT hgen hn hv π hπfix hπval
      (familyAut_orbitFamily_restrict _ hf)

end AllOrbits

end InverseGalois.CFT

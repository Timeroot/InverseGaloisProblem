/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Fibers
import InverseGalois.CFT.Tate.FamilyOrbit
import InverseGalois.CFT.Tate.FamilyReindex

/-!
# The sections of a family of modules, orbit by orbit

A set carrying a group action is the disjoint union of its orbits, so the sections of a family of
modules indexed by it are the product over the orbits of the sections over one orbit.  For a finite
cyclic group each of those factors is the module induced from the decomposition group of a point,
and its Herbrand quotient is the Herbrand quotient of the module at that point under a full turn of
the orbit.

This is the shape of the group of ideles of a Galois extension of number fields: the places above a
place of the base field form one orbit, and the local factor there is induced from the
decomposition group.  The two statements proved here are the two ways that decomposition is used —
the finitely many orbits that contribute multiply their contributions, and orbits whose
contribution is cohomologically trivial may be present in any number without affecting the answer.

## Main definitions

* `InverseGalois.CFT.orbitFamily`: the restriction of a family of modules to one orbit of the index
  set.

## Main results

* `InverseGalois.CFT.stabAut_orbitFamily`: the action of the stabiliser of a point of an orbit on
  the module there is its action as a subgroup of the whole group.
* `InverseGalois.CFT.herbrand_familyAut_orbits`: **the Herbrand quotient of the sections of a family
  is the product over the orbits of the Herbrand quotient of the sections over one orbit.**
* `InverseGalois.CFT.herbrand_familyAut_orbits_eq_one`: the sections have Herbrand quotient one as
  soon as the sections over every orbit have vanishing Tate groups.
* `InverseGalois.CFT.herbrand_familyAut_orbits_split`: **the Herbrand quotient of the sections is
  the product over the finitely many named orbits**, as soon as the sections over the other orbits
  have vanishing Tate groups.
* `InverseGalois.CFT.herbrand_orbitFamily`: **the contribution of one orbit is the Herbrand quotient
  of the module at a point of it under a full turn of the orbit.**
* `InverseGalois.CFT.familyAut_orbitFamily_restrict`: the restriction to an orbit of a section fixed
  by a generator is fixed.
* `InverseGalois.CFT.exists_normHom_orbitFamily`: **a fixed section over one orbit is a norm as soon
  as its value at a point of the orbit is a norm for the decomposition group there.**

## Tags

Tate cohomology, Herbrand quotient, orbit, decomposition group, idele
-/

namespace InverseGalois.CFT

open MulAction

variable {G X : Type*} [Group G] [MulAction G X] {σ : G}
  {M : X → Type*} [∀ x, AddCommGroup (M x)] (F : FamilyAction M G)

/-! ### The restriction to one orbit -/

/-- **The restriction of a family of modules to one orbit of the index set.** -/
def orbitFamily (ω : orbitRel.Quotient G X) : FamilyAction (fun z : ω.orbit => M (z : X)) G :=
  (F.reindex (selfEquivSigmaOrbits' G X).symm equivariant_selfEquivSigmaOrbits).sigmaFiber ω

/-- **A transport for the restriction to an orbit is a transport for the whole family.** -/
theorem orbitFamily_transport {ω : orbitRel.Quotient G X} {g : G} {x y : ω.orbit} (h : g • x = y)
    (h' : g • (x : X) = (y : X)) (a : M (x : X)) :
    (orbitFamily F ω).transport h a = F.transport h' a := by
  subst h
  rfl

/-- **The action of the stabiliser of a point of an orbit on the module there is its action as a
subgroup of the whole group.** -/
theorem stabAut_orbitFamily {ω : orbitRel.Quotient G X} (x₀ : ω.orbit)
    {H : Subgroup G} (hH' : ∀ g : ↥H, (g : G) • x₀ = x₀)
    (hH'' : ∀ g : ↥H, (g : G) • (x₀ : X) = (x₀ : X)) (g : ↥H) (a : M (x₀ : X)) :
    stabAut x₀ hH' (orbitFamily F ω) g a = F.transport (hH'' g) a :=
  orbitFamily_transport F (hH' g) (hH'' g) a

/-- The action of a generator on the sections over one orbit is the action on the whole family. -/
theorem familyAut_orbitFamily_apply {ω : orbitRel.Quotient G X} (f : ∀ z : ω.orbit, M (z : X))
    (x : ω.orbit) :
    (orbitFamily F ω).familyAut σ f x = F.transport (smul_inv_smul σ (x : X)) (f (σ⁻¹ • x)) :=
  orbitFamily_transport F (smul_inv_smul σ x) (smul_inv_smul σ (x : X)) _

/-- **The restriction to an orbit of a section fixed by a generator is fixed.** -/
theorem familyAut_orbitFamily_restrict {ω : orbitRel.Quotient G X} {f : ∀ x, M x}
    (hf : F.familyAut σ f = f) :
    (orbitFamily F ω).familyAut σ (fun z : ω.orbit => f (z : X))
      = fun z : ω.orbit => f (z : X) := by
  funext x
  rw [familyAut_orbitFamily_apply]
  exact congrFun hf (x : X)

/-! ### The product over the orbits -/

/-- **The Herbrand quotient of the sections of a family is the product over the orbits of the
Herbrand quotient of the sections over one orbit.** -/
theorem herbrand_familyAut_orbits [Fintype (orbitRel.Quotient G X)] (n : ℕ) :
    herbrand (F.familyAut σ) n
      = ∏ ω : orbitRel.Quotient G X, herbrand ((orbitFamily F ω).familyAut σ) n := by
  rw [herbrand_familyAut_reindex F (selfEquivSigmaOrbits' G X).symm
    equivariant_selfEquivSigmaOrbits σ n]
  exact herbrand_familyAut_sigma _ σ n

/-- The upper Tate group of the sections vanishes as soon as it vanishes over every orbit. -/
theorem subsingleton_tateH0_familyAut_orbits (n : ℕ)
    (h : ∀ ω : orbitRel.Quotient G X, Subsingleton (tateH0 ((orbitFamily F ω).familyAut σ) n)) :
    Subsingleton (tateH0 (F.familyAut σ) n) :=
  subsingleton_tateH0_familyAut_reindex F (selfEquivSigmaOrbits' G X).symm
    equivariant_selfEquivSigmaOrbits σ n (subsingleton_tateH0_familyAut_sigma _ σ n h)

/-- The lower Tate group of the sections vanishes as soon as it vanishes over every orbit. -/
theorem subsingleton_tateHm1_familyAut_orbits (n : ℕ)
    (h : ∀ ω : orbitRel.Quotient G X, Subsingleton (tateHm1 ((orbitFamily F ω).familyAut σ) n)) :
    Subsingleton (tateHm1 (F.familyAut σ) n) :=
  subsingleton_tateHm1_familyAut_reindex F (selfEquivSigmaOrbits' G X).symm
    equivariant_selfEquivSigmaOrbits σ n (subsingleton_tateHm1_familyAut_sigma _ σ n h)

/-- **The sections of a family have Herbrand quotient one as soon as the sections over every orbit
have vanishing Tate groups.**  This is what the places outside a finite set contribute to the
Herbrand quotient of the group of ideles. -/
theorem herbrand_familyAut_orbits_eq_one (n : ℕ)
    (h0 : ∀ ω : orbitRel.Quotient G X, Subsingleton (tateH0 ((orbitFamily F ω).familyAut σ) n))
    (hm1 : ∀ ω : orbitRel.Quotient G X, Subsingleton (tateHm1 ((orbitFamily F ω).familyAut σ) n)) :
    herbrand (F.familyAut σ) n = 1 := by
  rw [herbrand_familyAut_reindex F (selfEquivSigmaOrbits' G X).symm
    equivariant_selfEquivSigmaOrbits σ n]
  exact herbrand_familyAut_sigma_eq_one _ σ n h0 hm1

/-- **The Herbrand quotient of the sections of a family is the product over the finitely many named
orbits**, as soon as the sections over the other orbits have vanishing Tate groups.  This is the
Herbrand quotient of the group of ideles of a Galois extension of number fields that are units
outside a finite set of places of the base field: only the places in that set contribute. -/
theorem herbrand_familyAut_orbits_split (n : ℕ) (p : orbitRel.Quotient G X → Prop)
    [DecidablePred p] [Fintype {ω // p ω}]
    (h0 : ∀ ω : {ω // ¬ p ω},
      Subsingleton (tateH0 ((orbitFamily F (ω : orbitRel.Quotient G X)).familyAut σ) n))
    (hm1 : ∀ ω : {ω // ¬ p ω},
      Subsingleton (tateHm1 ((orbitFamily F (ω : orbitRel.Quotient G X)).familyAut σ) n)) :
    herbrand (F.familyAut σ) n
      = ∏ ω : {ω // p ω}, herbrand ((orbitFamily F (ω : orbitRel.Quotient G X)).familyAut σ) n := by
  rw [herbrand_familyAut_reindex F (selfEquivSigmaOrbits' G X).symm
    equivariant_selfEquivSigmaOrbits σ n]
  exact herbrand_familyAut_sigma_split _ σ n p h0 hm1

/-! ### The contribution of one orbit -/

/-- The stabiliser of a point of an orbit is its stabiliser in the whole set. -/
theorem stabilizer_orbit_coe {ω : orbitRel.Quotient G X} (x₀ : ω.orbit) :
    stabilizer G x₀ = stabilizer G (x₀ : X) := by
  ext g
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-- **The contribution of one orbit is the Herbrand quotient of the module at a point of it under a
full turn of the orbit.**  Transporting the modules over the orbit to the module at the point
presents the sections as the module induced from the decomposition group of the point. -/
theorem herbrand_orbitFamily [Finite G] (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    {ω : orbitRel.Quotient G X} [Fintype ω.orbit] (x₀ : ω.orbit) {n m : ℕ}
    (hn : Nat.card G = n) (hm : Nat.card ↥(stabilizer G x₀) = m) :
    herbrand ((orbitFamily F ω).familyAut σ) n
      = herbrand (stabAut x₀ (fun g => mem_stabilizer_iff.mp g.2) (orbitFamily F ω)
          (orbitTurn σ x₀ fun _ h => mem_stabilizer_iff.mpr h)) m := by
  have hgen' : ∀ g : G, g ∈ Subgroup.zpowers σ⁻¹ := fun g => by
    rw [Subgroup.zpowers_inv]
    exact hgen g
  refine herbrand_familyAut_orbit x₀
    (exists_pow_orbitShift_apply_eq x₀ hgen) (fun _ h => mem_stabilizer_iff.mpr h)
    (fun g => mem_stabilizer_iff.mp g.2) (orbitFamily F ω) ?_ ?_
  · rw [← hm]
    exact pow_card_eq_one'
  · rw [show orbitShift (↥ω.orbit) σ = (toPerm σ⁻¹ : Equiv.Perm ↥ω.orbit) from rfl,
      period_eq_card_orbit hgen' x₀, ← hm, card_orbit_mul_card_stabilizer, hn]

/-- **A fixed section over one orbit is a norm as soon as its value at a point of the orbit is a
norm for the decomposition group there.**  Transporting the modules over the orbit to the module at
the point presents the sections as the module induced from the decomposition group, and Shapiro's
lemma reads a norm there as a norm here. -/
theorem exists_normHom_orbitFamily [Finite G] (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    {ω : orbitRel.Quotient G X} [Fintype ω.orbit] (x₀ : ω.orbit) {n m : ℕ}
    (hn : Nat.card G = n) (hm : Nat.card ↥(stabilizer G x₀) = m)
    {f : ∀ z : ω.orbit, M (z : X)} (hf : (orbitFamily F ω).familyAut σ f = f)
    (h : ∃ b, normHom (stabAut x₀ (fun g => mem_stabilizer_iff.mp g.2) (orbitFamily F ω)
        (orbitTurn σ x₀ fun _ hg => mem_stabilizer_iff.mpr hg)) m b = f x₀) :
    ∃ u, normHom ((orbitFamily F ω).familyAut σ) n u = f := by
  have hgen' : ∀ g : G, g ∈ Subgroup.zpowers σ⁻¹ := fun g => by
    rw [Subgroup.zpowers_inv]
    exact hgen g
  refine exists_normHom_familyAut_orbit x₀
    (exists_pow_orbitShift_apply_eq x₀ hgen) (fun _ hg => mem_stabilizer_iff.mpr hg)
    (fun g => mem_stabilizer_iff.mp g.2) (orbitFamily F ω) ?_ ?_ hf h
  · rw [← hm]
    exact pow_card_eq_one'
  · rw [show orbitShift (↥ω.orbit) σ = (toPerm σ⁻¹ : Equiv.Perm ↥ω.orbit) from rfl,
      period_eq_card_orbit hgen' x₀, ← hm, card_orbit_mul_card_stabilizer, hn]

end InverseGalois.CFT

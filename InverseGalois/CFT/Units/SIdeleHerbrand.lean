/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Prod
import InverseGalois.CFT.Units.AdicIdeleHerbrand
import InverseGalois.CFT.Units.ArchimedeanIdeles
import InverseGalois.CFT.Units.SUnitHerbrand

/-!
# The Herbrand quotient of the ideles that are units outside a finite set of places

An idele of a number field has an archimedean part and a finite part, and the group of ideles that
are units outside a finite set `S` of places containing the infinite ones is the product of the two.
The Herbrand quotient of each factor has been computed: the archimedean part contributes the product
of the orders of the decomposition groups at the infinite places of the base field, and the finite
part contributes the product of the orders of the decomposition groups at the orbits of the chosen
finite places.

Multiplying them gives the Herbrand quotient of the whole group, and comparing it with the Herbrand
quotient of the group of `S`-units gives the identity that drives the first inequality of class field
theory: the two products are literally the same, so the Herbrand quotient of the `S`-ideles is the
Herbrand quotient of the `S`-units times the degree of the extension.

## Main definitions

* `InverseGalois.CFT.sIdeleAut`: the action of a Galois automorphism on the ideles that are units
  outside the chosen places.

## Main results

* `InverseGalois.CFT.herbrand_sIdeleAut`: **the ideles that are units outside the chosen places have
  Herbrand quotient the product of the orders of the decomposition groups** at the infinite places
  of the base field and at the orbits of the chosen finite places.
* `InverseGalois.CFT.herbrand_sIdeleAut_eq_sUnits_mul`: **the Herbrand quotient of the `S`-ideles is
  the Herbrand quotient of the `S`-units times the degree of the extension.**

## Tags

number field, idele, S-unit, decomposition group, Herbrand quotient, first inequality
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

section SIdeleHerbrand

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] {Y : Type*} [Fintype Y] [MulAction Gal(K/k) Y]
  [Fintype (orbitRel.Quotient Gal(K/k) Y)] {ι : Y → HeightOneSpectrum (𝓞 K)}
  (hι : ∀ (g : Gal(K/k)) (y : Y), ι (g • y) = g • ι y) [DecidablePred (· ∈ Set.range ι)]

include hι

/-- The action of a Galois automorphism on the ideles that are units outside the chosen places: the
units of the completion at every infinite place, and the units of the valuation ring at every finite
place other than the chosen ones. -/
noncomputable def sIdeleAut (σ : Gal(K/k)) :=
  prodAut ((infiniteRingFamily (k := k) (K := K)).unitsFamily.familyAut σ)
    ((adicSIdeleFamily (Set.range ι) (smul_mem_range_iff hι)).familyAut σ)

omit [NumberField k] [IsGalois k K] [Fintype Y] [Fintype (orbitRel.Quotient Gal(K/k) Y)] in
/-- The action on the `S`-ideles is the product of the archimedean and the finite actions. -/
theorem sIdeleAut_eq (σ : Gal(K/k)) :
    sIdeleAut hι σ
      = prodAut ((infiniteRingFamily (k := k) (K := K)).unitsFamily.familyAut σ)
          ((adicSIdeleFamily (Set.range ι) (smul_mem_range_iff hι)).familyAut σ) :=
  rfl

variable (hinj : Function.Injective ι)

include hinj

omit [Fintype Y] in
/-- **The ideles that are units outside the chosen places have Herbrand quotient the product of the
orders of the decomposition groups** at the infinite places of the base field and at the orbits of
the chosen finite places. -/
theorem herbrand_sIdeleAut
    (hunram : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Set.range ι →
      ∃ π : (v.adicCompletion K)ˣ,
        (∀ g : ↥(stabilizer Gal(K/k) v),
            g • (π : v.adicCompletion K) = (π : v.adicCompletion K))
          ∧ unitVal (Additive.ofMul π) = 1)
    {σ : Gal(K/k)} (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ) {n : ℕ}
    (hn : Nat.card Gal(K/k) = n) :
    herbrand (sIdeleAut hι σ) n
      = (∏ v : InfinitePlace k, (Nat.card ↥(stabilizer Gal(K/k) (placeAbove k K v)) : ℚ))
        * ∏ o : orbitRel.Quotient Gal(K/k) Y, (Nat.card ↥(stabilizer Gal(K/k) o.out) : ℚ) := by
  rw [sIdeleAut_eq, herbrand_prodAut, herbrand_infiniteUnitsFamily hgen hn,
    herbrand_adicSIdeleFamily hι hinj (smul_mem_range_iff hι) hunram hgen hn]

/-- **The Herbrand quotient of the ideles that are units outside the chosen places is the Herbrand
quotient of the `S`-units times the degree of the extension.**  The two computations produce the same
product of the orders of the decomposition groups, so everything except the degree cancels.  This is
the identity behind the first inequality of class field theory: dividing the `S`-ideles by the
`S`-units leaves a group of Herbrand quotient the degree. -/
theorem herbrand_sIdeleAut_eq_sUnits_mul
    (hunram : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Set.range ι →
      ∃ π : (v.adicCompletion K)ˣ,
        (∀ g : ↥(stabilizer Gal(K/k) v),
            g • (π : v.adicCompletion K) = (π : v.adicCompletion K))
          ∧ unitVal (Additive.ofMul π) = 1)
    {σ : Gal(K/k)} (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ) {n : ℕ} [NeZero n]
    (hn : Nat.card Gal(K/k) = n) :
    herbrand (sIdeleAut hι σ) n = herbrand (sUnitsAut hι σ) n * n := by
  rw [herbrand_sIdeleAut hι hinj hunram hgen hn, herbrand_sUnitsAut_mul hι hinj hgen hn]

end SIdeleHerbrand

end InverseGalois.CFT

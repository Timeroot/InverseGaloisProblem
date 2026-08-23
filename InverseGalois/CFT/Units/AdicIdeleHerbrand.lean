/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.OrbitRange
import InverseGalois.CFT.Units.AdicSIdeles

/-!
# The Herbrand quotient of the finite part of the ideles

Fix a finite set of finite places of a cyclic extension of number fields, carried into itself by the
Galois group and presented as the range of an equivariant injection from an abstract finite set of
indices, and suppose that every place outside it is unramified in the sense that its decomposition
group fixes a uniformizer.  The ideles that are units outside the chosen places then have a Herbrand
quotient, and only the chosen places contribute to it.

Each orbit of chosen places contributes the order of the decomposition group there, and every other
orbit contributes nothing because both Tate groups of the units of the valuation ring vanish at an
unramified place.  The answer is therefore the product over the orbits of the abstract index set of
the orders of the decomposition groups — literally the factor appearing in the Herbrand quotient of
the group of `S`-units, so that the two cancel in the Herbrand quotient of the idele class group.

## Main results

* `InverseGalois.CFT.herbrand_adicSIdeleFamily`: **the finite part of the ideles that are units
  outside a finite invariant set of unramified-complement places has Herbrand quotient the product
  of the orders of the decomposition groups at the chosen places.**

## Tags

number field, idele, S-unit, decomposition group, Herbrand quotient
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

section IdeleHerbrand

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  {Y : Type*} [MulAction Gal(K/k) Y]
  [Fintype (orbitRel.Quotient Gal(K/k) Y)] {ι : Y → HeightOneSpectrum (𝓞 K)}
  (hι : ∀ (g : Gal(K/k)) (y : Y), ι (g • y) = g • ι y) (hinj : Function.Injective ι)
  [DecidablePred (· ∈ Set.range ι)]
  (hT : ∀ (g : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)),
    g • v ∈ Set.range ι ↔ v ∈ Set.range ι)

include hι hinj hT

set_option maxHeartbeats 800000 in
/-- **The finite part of the ideles that are units outside a finite invariant set of places whose
complement is unramified has Herbrand quotient the product of the orders of the decomposition groups
at the chosen places.**  Only the chosen places contribute: at every other place the local subgroup
is the units of the valuation ring, whose Tate groups vanish because the decomposition group fixes a
uniformizer. -/
theorem herbrand_adicSIdeleFamily
    (hunram : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Set.range ι →
      ∃ π : (v.adicCompletion K)ˣ,
        (∀ g : ↥(stabilizer Gal(K/k) v),
            g • (π : v.adicCompletion K) = (π : v.adicCompletion K))
          ∧ unitVal (Additive.ofMul π) = 1)
    {σ : Gal(K/k)} (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ) {n : ℕ}
    (hn : Nat.card Gal(K/k) = n) :
    herbrand ((adicSIdeleFamily (Set.range ι) hT).familyAut σ) n
      = ∏ o : orbitRel.Quotient Gal(K/k) Y, (Nat.card ↥(stabilizer Gal(K/k) o.out) : ℚ) := by
  haveI : Module.Finite k K := Module.Finite.of_restrictScalars_finite ℚ k K
  haveI : Fintype {ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)) //
      ω.out ∈ Set.range ι} := Fintype.ofEquiv _ (orbitRangeEquiv hι hinj)
  haveI : DecidablePred fun ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)) =>
      ω.out ∈ Set.range ι := Classical.decPred _
  have h0 : ∀ ω : {ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)) //
        ¬ ω.out ∈ Set.range ι},
      Subsingleton (tateH0 ((orbitFamily (adicSIdeleFamily (Set.range ι) hT)
        (ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)))).familyAut σ) n) := by
    intro ω
    haveI : Fintype (ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K))).orbit :=
      Fintype.ofFinite _
    obtain ⟨π, hπfix, hπval⟩ := hunram _ ω.2
    exact (subsingleton_tate_orbitFamily_adicSUnits_of_notMem (orbitOut _) (Set.range ι) hT hgen hn
      ω.2 π hπfix hπval).1
  have hm1 : ∀ ω : {ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)) //
        ¬ ω.out ∈ Set.range ι},
      Subsingleton (tateHm1 ((orbitFamily (adicSIdeleFamily (Set.range ι) hT)
        (ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)))).familyAut σ) n) := by
    intro ω
    haveI : Fintype (ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K))).orbit :=
      Fintype.ofFinite _
    obtain ⟨π, hπfix, hπval⟩ := hunram _ ω.2
    exact (subsingleton_tate_orbitFamily_adicSUnits_of_notMem (orbitOut _) (Set.range ι) hT hgen hn
      ω.2 π hπfix hπval).2
  rw [herbrand_familyAut_orbits_split (adicSIdeleFamily (Set.range ι) hT) n
    (fun ω => ω.out ∈ Set.range ι) h0 hm1]
  refine Eq.trans (Finset.prod_congr rfl fun ω _ => ?_) (prod_card_stabilizer_orbitRange hι hinj)
  haveI : Fintype (ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K))).orbit :=
    Fintype.ofFinite _
  exact herbrand_orbitFamily_adicSUnits_of_mem (orbitOut _) (Set.range ι) hT hgen hn ω.2

end IdeleHerbrand

end InverseGalois.CFT

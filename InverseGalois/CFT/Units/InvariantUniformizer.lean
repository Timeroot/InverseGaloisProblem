/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.AdicUnramified
import InverseGalois.CFT.Tate.FamilyInvariant
import InverseGalois.CFT.Units.AdicSIdeles

/-!
# A Galois invariant family of uniformizers

A uniformizer at a place of a number field is at best fixed by the decomposition group there, never
by the whole Galois group, which moves the place.  What can be asked of a whole family of
uniformizers, one at every place, is that the automorphism carrying one place to another carry the
chosen uniformizer at the first to the chosen uniformizer at the second: the family is then a fixed
section of the family of local unit groups.

Such a family exists on the places that carry a uniformizer fixed by their decomposition group,
because the decomposition group is exactly the stabiliser and the transport of a value fixed by the
stabiliser of a place is fixed by the stabiliser of the image place.  Those places are all but
finitely many: an element of the base field of valuation minus one at a place gives one, and only
the places dividing the different fail to provide such an element.

## Main definitions

* `InverseGalois.CFT.fixedUniformizerPlaces`: **the places carrying a uniformizer fixed by their
  decomposition group.**

## Main results

* `InverseGalois.CFT.finite_compl_fixedUniformizerPlaces`: **all but finitely many places carry
  one.**
* `InverseGalois.CFT.exists_familyAut_eq_self_unitVal_eq_one`: **a Galois invariant section of the
  family of local unit groups whose value at each of those places is a uniformizer.**

## Tags

number field, uniformizer, decomposition group, idele, family of modules, invariant section
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

noncomputable section

variable (k K : Type*) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-! ### The places carrying a fixed uniformizer -/

/-- **The places carrying a uniformizer fixed by their decomposition group**, read as the indices at
which the family of local unit groups has a value of valuation one fixed by the stabiliser. -/
def fixedUniformizerPlaces : Set (HeightOneSpectrum (𝓞 K)) :=
  (adicRingFamily (k := k) (K := K)).unitsFamily.stabFixedSet fun _ a => unitVal a = 1

omit [NumberField k] in
theorem mem_fixedUniformizerPlaces {v : HeightOneSpectrum (𝓞 K)} :
    v ∈ fixedUniformizerPlaces k K ↔
      ∃ a : Additive (v.adicCompletion K)ˣ, unitVal a = 1 ∧ ∀ (g : Gal(K/k)) (hg : g • v = v),
        (adicRingFamily (k := k) (K := K)).unitsFamily.transport hg a = a :=
  Iff.rfl

omit [NumberField k] in
variable {k K} in
/-- A place carrying a uniformizer fixed by its decomposition group is one of them: the action of
the decomposition group is the transport by an automorphism fixing the place. -/
theorem mem_fixedUniformizerPlaces_of_exists {v : HeightOneSpectrum (𝓞 K)}
    (h : ∃ π : (v.adicCompletion K)ˣ,
      (∀ g : ↥(stabilizer Gal(K/k) v), g • (π : v.adicCompletion K) = (π : v.adicCompletion K))
        ∧ unitVal (Additive.ofMul π) = 1) :
    v ∈ fixedUniformizerPlaces k K := by
  obtain ⟨π, hfix, hval⟩ := h
  refine ⟨Additive.ofMul π, hval, fun g hg => ?_⟩
  rw [transport_adicUnitsFamily v g hg]
  refine Additive.toMul.injective (Units.ext ?_)
  rw [coe_smulUnitsAut_apply]
  exact hfix ⟨g, mem_stabilizer_iff.mpr hg⟩

/-- **All but finitely many places carry a uniformizer fixed by their decomposition group**: only
those dividing the different can fail to. -/
theorem finite_compl_fixedUniformizerPlaces : (fixedUniformizerPlaces k K)ᶜ.Finite :=
  Set.Finite.subset (finite_setOf_not_exists_fixedUniformizer k) fun _ hv hex =>
    hv (mem_fixedUniformizerPlaces_of_exists hex)

/-! ### The invariant family -/

omit [NumberField k] in
variable {k K} in
/-- The transports preserve the valuation, so they carry a uniformizer to a uniformizer. -/
theorem unitVal_unitsFamily_map_eq_one (g : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K))
    (a : Additive (v.adicCompletion K)ˣ) (ha : unitVal a = 1) :
    unitVal ((adicRingFamily (k := k) (K := K)).unitsFamily.map g v a) = 1 := by
  rw [unitVal_adicUnitsFamily_map]
  exact ha

omit [NumberField k] in
/-- **A Galois invariant section of the family of local unit groups whose value at every place
carrying a uniformizer fixed by its decomposition group is a uniformizer.**  The values are
transports of chosen ones along the orbits, so the valuation is carried along with them. -/
theorem exists_familyAut_eq_self_unitVal_eq_one :
    ∃ s : ∀ v : HeightOneSpectrum (𝓞 K), Additive (v.adicCompletion K)ˣ,
      (∀ g : Gal(K/k), (adicRingFamily (k := k) (K := K)).unitsFamily.familyAut g s = s) ∧
        ∀ v ∈ fixedUniformizerPlaces k K, unitVal (s v) = 1 :=
  (adicRingFamily (k := k) (K := K)).unitsFamily.exists_familyAut_eq_self_stabFixedSet
    fun g v a ha => unitVal_unitsFamily_map_eq_one g v a ha

end

end InverseGalois.CFT

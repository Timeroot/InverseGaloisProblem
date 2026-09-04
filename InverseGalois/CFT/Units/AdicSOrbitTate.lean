/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.FamilyRestrictCoind
import InverseGalois.CFT.Units.IdeleOrbitTate
import InverseGalois.CFT.Units.UnramifiedTateRep

/-!
# The complete cohomology of the ideles that are units outside a set of places

Fix a set of finite places of a Galois extension of number fields, stable under the Galois group.
The ideles that are units outside that set are the sections of a family of subgroups of the family
of local factors: the whole multiplicative group of a completion at a place of the set, the units of
the valuation ring at every other place.  The places above one place of the base field form a single
orbit, so the contribution of that place is the complete cohomology of the decomposition group of a
place above it with coefficients in the subgroup there.

Above a place of the set the subgroup is everything, and the contribution is the same as for the
whole group of ideles.  Above a place outside the set the subgroup is the units of a valuation ring,
and at an unramified place those have no complete cohomology at all.  So the cohomology of the
ideles that are units outside the set is concentrated at the places of the set, as soon as every
place outside it is unramified: this is the finite-level shape of the group of ideles that the
arithmetic of class formations uses in place of the full restricted product.

## Main results

* `InverseGalois.CFT.adicSOrbitTateEquiv_of_mem`: **above a place of the set the contribution is the
  complete cohomology of the decomposition group with coefficients in the units of the completion**,
  exactly as for the whole group of ideles.
* `InverseGalois.CFT.isZero_tateModule_orbitSectionsRep_adicSIdeleFamily`: **above an unramified
  place outside the set the contribution vanishes.**
* `InverseGalois.CFT.isZero_tateModule_adicSIdeleFamily`: **the ideles that are units outside the
  set have no complete cohomology in a degree as soon as no local factor at a place of the set has
  any**, provided every place outside the set is unramified.

## Tags

number field, idele, S-unit, decomposition group, Tate cohomology, Shapiro's lemma
-/

namespace InverseGalois.CFT

open CategoryTheory IsDedekindDomain MulAction NumberField Tate

noncomputable section

/-! ### One place of the base field -/

section Orbit

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] {ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K))} (v₀ : ω.orbit)
  (T : Set (HeightOneSpectrum (𝓞 K))) [DecidablePred (· ∈ T)]
  (hT : ∀ (g : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), g • v ∈ T ↔ v ∈ T)

/-- **Above a place of the set, the ideles that are units outside the set contribute the complete
cohomology of the decomposition group with coefficients in the units of the completion**, exactly as
the whole group of ideles does: the local subgroup at such a place is everything. -/
def adicSOrbitTateEquiv_of_mem (hv₀ : (v₀ : HeightOneSpectrum (𝓞 K)) ∈ T) (n : ℤ) :
    tateModule (orbitSectionsRep (orbitFamily (adicSIdeleFamily T hT) ω)) n
      ≃ₗ[ℤ] tateModule
        (repOfAddAut (smulUnitsAut (G := ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K))))
          (R := (v₀ : HeightOneSpectrum (𝓞 K)).adicCompletion K))) n :=
  restrictTopOrbitTateEquiv (adicRingFamily (k := k) (K := K)).unitsFamily (adicSUnits T)
    (map_adicSUnits T hT) v₀ (exists_smul_eq_orbit v₀) (mem_stabilizer_of_smul_orbit v₀)
    (smul_orbit_of_mem_stabilizer v₀) (fun g => mem_stabilizer_iff.mp g.2)
    (adicSUnits_of_mem T hv₀) _ (fun g a => (stabAut_orbitFamily_adicUnits v₀ g a).symm) n

/-- **Above an unramified place outside the set, the ideles that are units outside the set
contribute nothing**: the local subgroup there is the units of a valuation ring of an unramified
extension, whose complete cohomology vanishes in every degree. -/
theorem isZero_tateModule_orbitSectionsRep_adicSIdeleFamily
    (hv₀ : (v₀ : HeightOneSpectrum (𝓞 K)) ∉ T)
    (hunr : Algebra.IsUnramifiedAt (𝓞 k) (v₀ : HeightOneSpectrum (𝓞 K)).asIdeal) (n : ℤ) :
    Limits.IsZero (tateModule (orbitSectionsRep (orbitFamily (adicSIdeleFamily T hT) ω)) n) :=
  isZero_tateModule_orbitSectionsRep_restrict (adicRingFamily (k := k) (K := K)).unitsFamily
    (adicSUnits T) (map_adicSUnits T hT) v₀ (exists_smul_eq_orbit v₀)
    (mem_stabilizer_of_smul_orbit v₀) (smul_orbit_of_mem_stabilizer v₀)
    (fun g => mem_stabilizer_iff.mp g.2) (adicSUnits_of_notMem T hv₀) _
    (fun g _ => (stabAut_orbitFamily_adicUnits v₀ g _).symm) n
    (isZero_tateModule_adicKerUnitVal (v₀ : HeightOneSpectrum (𝓞 K)) hunr n)

end Orbit

/-! ### All the places at once -/

section AllOrbits

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]
  (v₀ : ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)), ω.orbit)
  (T : Set (HeightOneSpectrum (𝓞 K))) [DecidablePred (· ∈ T)]
  (hT : ∀ (g : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), g • v ∈ T ↔ v ∈ T)

/-- **The ideles that are units outside a set of places have no complete cohomology in a degree as
soon as no local factor at a place of the set has any**, provided every place outside the set is
unramified.  The cohomology is a product over the places of the base field, and outside the set the
factors are the units of the valuation rings of unramified extensions. -/
theorem isZero_tateModule_adicSIdeleFamily (n : ℤ)
    (hunr : ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)),
      ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)) ∉ T →
        Algebra.IsUnramifiedAt (𝓞 k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).asIdeal)
    (h : ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)),
      ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)) ∈ T →
        Limits.IsZero (tateModule (repOfAddAut (smulUnitsAut
          (G := ↥(stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))))
          (R := ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).adicCompletion K))) n)) :
    Limits.IsZero (tateModule (orbitSectionsRep (adicSIdeleFamily T hT)) n) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  haveI : ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)),
      Subsingleton ↥(tateModule (orbitSectionsRep (orbitFamily (adicSIdeleFamily T hT) ω)) n) := by
    intro ω
    refine ModuleCat.isZero_iff_subsingleton.1 ?_
    by_cases hv : ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)) ∈ T
    · haveI := ModuleCat.isZero_iff_subsingleton.1 (h ω hv)
      exact ModuleCat.isZero_iff_subsingleton.2
        (adicSOrbitTateEquiv_of_mem (v₀ ω) T hT hv n).injective.subsingleton
    · exact isZero_tateModule_orbitSectionsRep_adicSIdeleFamily (v₀ ω) T hT hv (hunr ω hv) n
  exact (tateOrbitsEquiv (adicSIdeleFamily T hT) n).injective.subsingleton

end AllOrbits

end

end InverseGalois.CFT

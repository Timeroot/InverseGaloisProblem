/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.FamilyCoind
import InverseGalois.CFT.Units.AdicOrbit
import InverseGalois.CFT.Units.AdicSIdeles

/-!
# The complete cohomology of the local factor of the ideles at a finite place

The finite places of a Galois extension of number fields lying above a fixed place of the base field
form one orbit of the Galois group, and the units of the completions at them form a family of
modules over that orbit whose sections are the local factor of the group of ideles there.  The
sections of a family over a transitive orbit are coinduced from the module at a base point, and
coinduction is transparent to complete cohomology.

So the complete cohomology of the local factor is the complete cohomology of the decomposition group
of one place above the given one, with coefficients in the units of the completion there.  This is
the local statement behind the description of the cohomology of the ideles as a product of local
contributions, one for each place of the base field, and unlike the Herbrand computation of the same
family it needs no hypothesis on the Galois group beyond finiteness.

## Main results

* `InverseGalois.CFT.orbitStabRep_adicUnits`: the representation of the decomposition group carried
  by the family is the action on the units of the completion.
* `InverseGalois.CFT.adicOrbitTateEquiv`: **the complete cohomology of the local factor of the
  ideles at a finite place of the base field is the complete cohomology of the decomposition group
  with coefficients in the units of the completion at one place above it.**

## Tags

number field, idele, decomposition group, Tate cohomology, Shapiro's lemma, coinduced representation
-/

namespace InverseGalois.CFT

open CategoryTheory IsDedekindDomain MulAction NumberField Tate

noncomputable section

variable {k K : Type} [Field k] [Field K] [Algebra k K] [NumberField K]
  {ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K))} (v₀ : ω.orbit)

omit [NumberField K] in
/-- **The places above a place of the base field form a single orbit**: some automorphism carries
any one of them to the chosen one. -/
theorem exists_smul_eq_orbit (y : ω.orbit) : ∃ g : Gal(K/k), g • y = v₀ :=
  MulAction.exists_smul_eq Gal(K/k) y v₀

/-- **The representation of the decomposition group carried by the family of completions above a
place is the action on the units of the completion there.** -/
theorem orbitStabRep_adicUnits :
    orbitStabRep v₀ (smul_orbit_of_mem_stabilizer v₀)
        (orbitFamily (adicRingFamily (k := k) (K := K)).unitsFamily ω)
      = repOfAddAut (smulUnitsAut (G := ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K))))
          (R := (v₀ : HeightOneSpectrum (𝓞 K)).adicCompletion K)) :=
  congrArg repOfAddAut
    (MonoidHom.ext fun g => AddEquiv.ext (stabAut_orbitFamily_adicUnits v₀ g))

variable [Finite Gal(K/k)]

/-- **The complete cohomology of the local factor of the ideles at a finite place of the base field
is the complete cohomology of the decomposition group with coefficients in the units of the
completion at one place above it.**  The places above the given one form a single orbit, so the
sections of the family of units of the completions at them are coinduced from the module at any one
of them, and coinduction is transparent to complete cohomology. -/
def adicOrbitTateEquiv (n : ℤ) :
    tateModule
        (orbitSectionsRep (orbitFamily (adicRingFamily (k := k) (K := K)).unitsFamily ω)) n
      ≃ₗ[ℤ] tateModule
        (repOfAddAut (smulUnitsAut (G := ↥(stabilizer Gal(K/k) (v₀ : HeightOneSpectrum (𝓞 K))))
          (R := (v₀ : HeightOneSpectrum (𝓞 K)).adicCompletion K))) n := by
  rw [← orbitStabRep_adicUnits v₀]
  exact orbitTateEquiv v₀ (exists_smul_eq_orbit v₀) (mem_stabilizer_of_smul_orbit v₀)
    (smul_orbit_of_mem_stabilizer v₀) _ n

end

end InverseGalois.CFT

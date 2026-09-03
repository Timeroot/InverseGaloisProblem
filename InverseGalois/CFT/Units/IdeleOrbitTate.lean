/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.FamilyProduct
import InverseGalois.CFT.Units.AdicOrbitTate

/-!
# The complete cohomology of the ideles as a product over the places of the base field

The places of a Galois extension of number fields lying above a fixed place of the base field form
one orbit of the Galois group, so the local factors of the group of ideles are the sections of the
family of units of the completions over one orbit, and the whole group is the product of them over
the orbits.  Complete cohomology turns that product into a product, and each factor is coinduced,
so each factor contributes the complete cohomology of a decomposition group.

The result is the description of the cohomology of the ideles that class field theory uses: **in
every degree the complete cohomology of the group of ideles is the product, over the places of the
base field, of the complete cohomology of the decomposition group of a place above it with
coefficients in the units of the completion there.**  The finite places and the infinite ones are
treated separately, the two arguments differing only in the family they are applied to, and no
hypothesis is placed on the Galois group beyond finiteness.

## Main results

* `InverseGalois.CFT.adicIdeleTateEquiv`: **the complete cohomology of the finite part of the
  ideles is the product over the finite places of the base field of the complete cohomology of a
  decomposition group with coefficients in the units of a completion.**
* `InverseGalois.CFT.infiniteIdeleTateEquiv`: **the same statement for the infinite part.**
* `InverseGalois.CFT.isZero_tateModule_adicIdele`,
  `InverseGalois.CFT.isZero_tateModule_infiniteIdele`: the ideles have no complete cohomology in a
  degree as soon as no local factor has any.

## Tags

number field, idele, decomposition group, Tate cohomology, Shapiro's lemma, product
-/

namespace InverseGalois.CFT

open CategoryTheory IsDedekindDomain MulAction NumberField Tate

noncomputable section

/-! ### The finite places -/

section Finite

variable {k K : Type} [Field k] [Field K] [Algebra k K] [NumberField K] [Finite Gal(K/k)]
  (v₀ : ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)), ω.orbit)

/-- **The complete cohomology of the finite part of the group of ideles is the product over the
finite places of the base field of the complete cohomology of the decomposition group of a place
above it with coefficients in the units of the completion there.**  The places of the extension
split into one orbit for each place of the base field, the sections of the family of units of the
completions split accordingly, and the sections over one orbit are coinduced from the module at a
chosen place above the given one. -/
def adicIdeleTateEquiv (n : ℤ) :
    tateModule (orbitSectionsRep (adicRingFamily (k := k) (K := K)).unitsFamily) n ≃+
      ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)),
        tateModule (repOfAddAut (smulUnitsAut
          (G := ↥(stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))))
          (R := ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).adicCompletion K))) n :=
  (tateOrbitsEquiv (adicRingFamily (k := k) (K := K)).unitsFamily n).trans <|
    AddEquiv.piCongrRight fun ω => (adicOrbitTateEquiv (v₀ ω) n).toAddEquiv

/-- **The finite part of the group of ideles has no complete cohomology in a degree as soon as no
local factor has any.** -/
theorem isZero_tateModule_adicIdele (n : ℤ)
    (h : ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)),
      Limits.IsZero (tateModule (repOfAddAut (smulUnitsAut
        (G := ↥(stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))))
        (R := ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).adicCompletion K))) n)) :
    Limits.IsZero
      (tateModule (orbitSectionsRep (adicRingFamily (k := k) (K := K)).unitsFamily) n) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  haveI : ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)),
      Subsingleton ↥(tateModule (repOfAddAut (smulUnitsAut
        (G := ↥(stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))))
        (R := ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).adicCompletion K))) n) := fun ω =>
    ModuleCat.isZero_iff_subsingleton.1 (h ω)
  exact (adicIdeleTateEquiv v₀ n).injective.subsingleton

end Finite

/-! ### The infinite places -/

section Archimedean

variable {k K : Type} [Field k] [Field K] [Algebra k K] [Finite Gal(K/k)]
  (w₀ : ∀ ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K), ω.orbit)

/-- **The complete cohomology of the infinite part of the group of ideles is the product over the
infinite places of the base field of the complete cohomology of the decomposition group of a place
above it with coefficients in the units of the completion there.** -/
def infiniteIdeleTateEquiv (n : ℤ) :
    tateModule (orbitSectionsRep (infiniteRingFamily (k := k) (K := K)).unitsFamily) n ≃+
      ∀ ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K),
        tateModule (repOfAddAut (smulUnitsAut
          (G := ↥(stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K)))
          (R := ((w₀ ω : ω.orbit) : InfinitePlace K).Completion))) n :=
  (tateOrbitsEquiv (infiniteRingFamily (k := k) (K := K)).unitsFamily n).trans <|
    AddEquiv.piCongrRight fun ω => (infiniteOrbitTateEquiv (w₀ ω) n).toAddEquiv

/-- **The infinite part of the group of ideles has no complete cohomology in a degree as soon as no
local factor has any.** -/
theorem isZero_tateModule_infiniteIdele (n : ℤ)
    (h : ∀ ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K),
      Limits.IsZero (tateModule (repOfAddAut (smulUnitsAut
        (G := ↥(stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K)))
        (R := ((w₀ ω : ω.orbit) : InfinitePlace K).Completion))) n)) :
    Limits.IsZero
      (tateModule (orbitSectionsRep (infiniteRingFamily (k := k) (K := K)).unitsFamily) n) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  haveI : ∀ ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K),
      Subsingleton ↥(tateModule (repOfAddAut (smulUnitsAut
        (G := ↥(stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K)))
        (R := ((w₀ ω : ω.orbit) : InfinitePlace K).Completion))) n) := fun ω =>
    ModuleCat.isZero_iff_subsingleton.1 (h ω)
  exact (infiniteIdeleTateEquiv w₀ n).injective.subsingleton

end Archimedean

end

end InverseGalois.CFT

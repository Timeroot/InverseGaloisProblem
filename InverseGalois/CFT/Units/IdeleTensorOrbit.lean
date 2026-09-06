/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.FamilyTensorFull
import InverseGalois.CFT.Units.AdicOrbitTate

/-!
# The twisted cohomology of the ideles as a product over the places of the base field

The description of the complete cohomology of the group of ideles as a product of local
contributions survives tensoring the coefficients with a representation whose underlying module is a
vector space over a prime field.  Tensoring commutes with the product of the local factors because
the coefficients are finitely presented, and it commutes with coinduction from a decomposition
group, so the two operations may be performed in either order.

The result is the form of the local-global description that the twisted coefficients of a lifting
problem need: **in every degree the complete cohomology of the group of ideles tensored with a
representation is the product, over the places of the base field, of the complete cohomology of the
decomposition group of a place above it with coefficients in the units of the completion there
tensored with the restriction of the representation.**  The finite places and the infinite ones are
treated separately, the two arguments differing only in the family they are applied to.

## Main results

* `InverseGalois.CFT.adicIdeleTensorTateEquiv`: **the twisted complete cohomology of the finite part
  of the ideles is the product over the finite places of the base field of the twisted complete
  cohomology of a decomposition group.**
* `InverseGalois.CFT.infiniteIdeleTensorTateEquiv`: **the same statement for the infinite part.**
* `InverseGalois.CFT.isZero_tateModule_adicIdeleTensor`,
  `InverseGalois.CFT.isZero_tateModule_infiniteIdeleTensor`: the twisted ideles have no complete
  cohomology in a degree as soon as no local factor has any.

## Tags

number field, idele, decomposition group, Tate cohomology, Shapiro's lemma, tensor product
-/

namespace InverseGalois.CFT

open CategoryTheory IsDedekindDomain MulAction NumberField Tate

noncomputable section

/-! ### The finite places -/

section Finite

variable {k K : Type} [Field k] [Field K] [Algebra k K] [NumberField K] [Finite Gal(K/k)]
  (v₀ : ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)), ω.orbit)
  (W : Rep ℤ Gal(K/k)) {p d : ℕ} [Fact p.Prime] (e : ↥W.V ≃+ (Fin d → ZMod p))

include e in
/-- **The twisted complete cohomology of the finite part of the group of ideles is the product over
the finite places of the base field of the twisted complete cohomology of the decomposition group of
a place above it.**  The places of the extension split into one orbit for each place of the base
field, tensoring with a vector space over a prime field commutes with the product over the places,
and the sections over one orbit are coinduced from a chosen place above the given one. -/
def adicIdeleTensorTateEquiv (n : ℤ) :
    tateModule
        (tensorObj (orbitSectionsRep (adicRingFamily (k := k) (K := K)).unitsFamily) W) n ≃+
      ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)),
        tateModule (tensorObj
            (repOfAddAut (smulUnitsAut
              (G := ↥(stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))))
              (R := ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).adicCompletion K)))
            (resObj (stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))) W)) n := by
  refine (tateTensorOrbitsEquivOfEquivPi (adicRingFamily (k := k) (K := K)).unitsFamily W e v₀
    (fun ω => mem_stabilizer_of_smul_orbit (v₀ ω))
    (fun ω => smul_orbit_of_mem_stabilizer (v₀ ω)) n).trans (AddEquiv.piCongrRight fun ω => ?_)
  rw [orbitStabRep_adicUnits (v₀ ω)]

include e in
/-- **The twisted finite part of the group of ideles has no complete cohomology in a degree as soon
as no local factor has any.** -/
theorem isZero_tateModule_adicIdeleTensor (n : ℤ)
    (h : ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)),
      Limits.IsZero (tateModule (tensorObj
        (repOfAddAut (smulUnitsAut
          (G := ↥(stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))))
          (R := ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).adicCompletion K)))
        (resObj (stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))) W)) n)) :
    Limits.IsZero (tateModule
      (tensorObj (orbitSectionsRep (adicRingFamily (k := k) (K := K)).unitsFamily) W) n) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  haveI : ∀ ω : orbitRel.Quotient Gal(K/k) (HeightOneSpectrum (𝓞 K)),
      Subsingleton ↥(tateModule (tensorObj
        (repOfAddAut (smulUnitsAut
          (G := ↥(stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))))
          (R := ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K)).adicCompletion K)))
        (resObj (stabilizer Gal(K/k) ((v₀ ω : ω.orbit) : HeightOneSpectrum (𝓞 K))) W)) n) :=
    fun ω => ModuleCat.isZero_iff_subsingleton.1 (h ω)
  exact (adicIdeleTensorTateEquiv v₀ W e n).injective.subsingleton

end Finite

/-! ### The infinite places -/

section Archimedean

variable {k K : Type} [Field k] [Field K] [Algebra k K] [Finite Gal(K/k)]
  (w₀ : ∀ ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K), ω.orbit)
  (W : Rep ℤ Gal(K/k)) {p d : ℕ} [Fact p.Prime] (e : ↥W.V ≃+ (Fin d → ZMod p))

include e in
/-- **The twisted complete cohomology of the infinite part of the group of ideles is the product
over the infinite places of the base field of the twisted complete cohomology of the decomposition
group of a place above it.** -/
def infiniteIdeleTensorTateEquiv (n : ℤ) :
    tateModule
        (tensorObj (orbitSectionsRep (infiniteRingFamily (k := k) (K := K)).unitsFamily) W) n ≃+
      ∀ ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K),
        tateModule (tensorObj
            (repOfAddAut (smulUnitsAut
              (G := ↥(stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K)))
              (R := ((w₀ ω : ω.orbit) : InfinitePlace K).Completion)))
            (resObj (stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K)) W)) n := by
  refine (tateTensorOrbitsEquivOfEquivPi (infiniteRingFamily (k := k) (K := K)).unitsFamily W e w₀
    (fun ω => mem_stabilizer_of_smul_orbit_infinite (w₀ ω))
    (fun ω => smul_orbit_of_mem_stabilizer_infinite (w₀ ω)) n).trans
    (AddEquiv.piCongrRight fun ω => ?_)
  rw [orbitStabRep_infiniteUnits (w₀ ω)]

include e in
/-- **The twisted infinite part of the group of ideles has no complete cohomology in a degree as
soon as no local factor has any.** -/
theorem isZero_tateModule_infiniteIdeleTensor (n : ℤ)
    (h : ∀ ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K),
      Limits.IsZero (tateModule (tensorObj
        (repOfAddAut (smulUnitsAut
          (G := ↥(stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K)))
          (R := ((w₀ ω : ω.orbit) : InfinitePlace K).Completion)))
        (resObj (stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K)) W)) n)) :
    Limits.IsZero (tateModule
      (tensorObj (orbitSectionsRep (infiniteRingFamily (k := k) (K := K)).unitsFamily) W) n) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  haveI : ∀ ω : orbitRel.Quotient Gal(K/k) (InfinitePlace K),
      Subsingleton ↥(tateModule (tensorObj
        (repOfAddAut (smulUnitsAut
          (G := ↥(stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K)))
          (R := ((w₀ ω : ω.orbit) : InfinitePlace K).Completion)))
        (resObj (stabilizer Gal(K/k) ((w₀ ω : ω.orbit) : InfinitePlace K)) W)) n) :=
    fun ω => ModuleCat.isZero_iff_subsingleton.1 (h ω)
  exact (infiniteIdeleTensorTateEquiv w₀ W e n).injective.subsingleton

end Archimedean

end

end InverseGalois.CFT

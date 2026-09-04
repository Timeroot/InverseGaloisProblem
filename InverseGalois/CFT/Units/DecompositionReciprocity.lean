/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.CyclicProduct
import InverseGalois.CFT.Brauer.PlaceCrossedProduct
import InverseGalois.CFT.Units.DecompositionInvariant
import InverseGalois.CFT.Units.OrbitPlaces

/-!
# Reciprocity for the invariants of the decomposition groups

A two-cocycle of the Galois group of an extension of number fields with values in the units of the
top field has a localisation at each finite place: restrict it to the decomposition group there,
and read the result on the Galois group of the completions.  The crossed product of the
localisation is the algebra of the global crossed product extended to the completion, so **the
invariant at a place of the Brauer class of a global crossed product is the invariant of the class
of the decomposition group at a place above it**.  The two invariants of local class field theory
that the repository carries, one attached to a Brauer class of the base and one attached to a class
of a decomposition group, are thereby the same invariant read twice.

The product formula for the invariants of a Brauer class of a number field then becomes a statement
about decomposition groups, and it has a consequence no purely local argument can reach: if the
localisations are coboundaries at every finite place but one, and the class is split at every
infinite place, then the remaining invariant is the inverse of a product of trivial ones, hence
trivial, and the Albert-Brauer-Hasse-Noether theorem makes the global cocycle a coboundary.  **One
place may be left out of a local-global hypothesis for free**, and which place is left out is
immaterial.

## Main definitions

* `InverseGalois.CFT.decompositionClass`: the class of the decomposition group at a finite place
  attached to a two-cocycle of the whole Galois group.

## Main results

* `InverseGalois.CFT.placeInvariant_eq_decompositionInvariant`: **the invariant at a finite place
  of the class of a global crossed product is the invariant of the class of the decomposition
  group at a place above it.**
* `InverseGalois.CFT.isMulCoboundary₂_localCocycle_of_forall_ne`: **a global two-cocycle whose
  localisations are coboundaries away from one finite place, and which is split at every infinite
  place, has a coboundary localisation at that place as well.**
* `InverseGalois.CFT.isMulCoboundary₂_of_forall_ne`: **such a cocycle is a coboundary.**

## Tags

number field, Brauer group, crossed product, decomposition group, invariant, reciprocity,
Albert-Brauer-Hasse-Noether
-/

set_option synthInstance.maxHeartbeats 1000000

namespace InverseGalois.CFT

open CategoryTheory IsDedekindDomain MulAction NumberField Tate groupCohomology

attribute [local instance] isGalois_adicCompletion

noncomputable section

section Localisation

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (w : HeightOneSpectrum (𝓞 K)) {f : Gal(K/k) × Gal(K/k) → Kˣ}

variable (k) in
/-- **The class of the decomposition group at a finite place attached to a two-cocycle of the whole
Galois group**: the class in degree two of the localisation of the cocycle. -/
def decompositionClass (hf : IsMulCocycle₂ f) :
    Multiplicative ↥(tateModule (decompositionUnitsRep k w) 2) :=
  Multiplicative.ofAdd ((decompositionTwoIso k w).hom.hom
    (H2π (completionUnitsRep k w)
      (cocyclesOfIsMulCocycle₂ (isMulCocycle₂_localCocycle k w hf))))

variable (k) in
/-- The Brauer class attached to a class of the decomposition group is the crossed product of the
class read on the Galois group of the completions. -/
theorem decompositionBrauer_eq_brauerOfH2
    (z : Multiplicative ↥(tateModule (decompositionUnitsRep k w) 2)) :
    decompositionBrauer k w z
      = brauerOfH2 ((decompositionTwoIso k w).symm.toLinearEquiv (Multiplicative.toAdd z)) :=
  rfl

variable (k) in
/-- The Brauer class attached to the class of a localised cocycle is the crossed product of that
cocycle. -/
theorem decompositionBrauer_decompositionClass (hf : IsMulCocycle₂ f) :
    decompositionBrauer k w (decompositionClass k w hf)
      = (⟦CrossedProduct.csa (isMulCocycle₂_localCocycle k w hf)⟧ :
          BrauerGroup ((primeUnder (𝓞 k) w).adicCompletion k)) := by
  have hinv : ∀ x : ↥(groupCohomology (completionUnitsRep k w) 2),
      (decompositionTwoIso k w).symm.toLinearEquiv ((decompositionTwoIso k w).hom.hom x) = x :=
    fun _ => by simp
  rw [decompositionBrauer_eq_brauerOfH2, decompositionClass, _root_.toAdd_ofAdd, hinv]
  exact brauerOfH2_apply _

variable (k) in
/-- **The invariant at a finite place of the class of a global crossed product is the invariant of
the class of the decomposition group at a place above it.** -/
theorem placeInvariant_eq_decompositionInvariant (hf : IsMulCocycle₂ f) :
    placeInvariant k (primeUnder (𝓞 k) w) (⟦CrossedProduct.csa hf⟧ : BrauerGroup k)
      = decompositionInvariant k w (decompositionClass k w hf) := by
  rw [placeInvariant_apply, baseChangeHom_mk_csa_adicCompletion k w hf,
    decompositionInvariant_apply, decompositionBrauer_decompositionClass]

end Localisation

/-! ### One place left out -/

section Reciprocity

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (w : HeightOneSpectrum (𝓞 K)) {f : Gal(K/k) × Gal(K/k) → Kˣ}

variable (k) in
/-- **A global two-cocycle whose localisations are coboundaries away from one finite place, and
which is split at every infinite place, has a coboundary localisation at that place as well.**  The
product of all the invariants is trivial, and every factor but one is known to be. -/
theorem isMulCoboundary₂_localCocycle_of_forall_ne (hf : IsMulCocycle₂ f)
    (hout : ∀ W : HeightOneSpectrum (𝓞 K), primeUnder (𝓞 k) W ≠ primeUnder (𝓞 k) w →
      IsMulCoboundary₂ (localCocycle k W f))
    (hinf : ∀ u : InfinitePlace k,
      infinitePlaceInvariant k u (⟦CrossedProduct.csa hf⟧ : BrauerGroup k) = 1) :
    IsMulCoboundary₂ (localCocycle k w f) := by
  refine (placeInvariant_mk_csa_eq_one_iff k w hf).1 ?_
  have hfin : ∀ v ∉ ({primeUnder (𝓞 k) w} : Finset (HeightOneSpectrum (𝓞 k))),
      placeInvariant k v (⟦CrossedProduct.csa hf⟧ : BrauerGroup k) = 1 := by
    intro v hv
    obtain ⟨W, rfl⟩ := exists_primeUnder_eq (𝓞 k) (𝓞 K) v
    exact (placeInvariant_mk_csa_eq_one_iff k W hf).2
      (hout W (by simpa using hv))
  have hprod := prod_placeInvariant_mul_prod_infinitePlaceInvariant_eq_one k
    (⟦CrossedProduct.csa hf⟧ : BrauerGroup k) {primeUnder (𝓞 k) w} hfin
  rw [Finset.prod_singleton] at hprod
  simpa [hinf] using hprod

variable (k) in
/-- **A global two-cocycle whose localisations are coboundaries away from one finite place, and
which is split at every infinite place, is a coboundary.**  Its invariant at the place left out is
trivial as well, so all of its local invariants vanish, and the theorem of Albert, Brauer, Hasse and
Noether applies. -/
theorem isMulCoboundary₂_of_forall_ne (hf : IsMulCocycle₂ f)
    (hout : ∀ W : HeightOneSpectrum (𝓞 K), primeUnder (𝓞 k) W ≠ primeUnder (𝓞 k) w →
      IsMulCoboundary₂ (localCocycle k W f))
    (hinf : ∀ u : InfinitePlace k,
      infinitePlaceInvariant k u (⟦CrossedProduct.csa hf⟧ : BrauerGroup k) = 1) :
    IsMulCoboundary₂ f := by
  refine (CrossedProduct.mk_csa_eq_one_iff hf).1
    (eq_one_of_forall_invariant_eq_one k _ (fun v => ?_) hinf)
  obtain ⟨W, rfl⟩ := exists_primeUnder_eq (𝓞 k) (𝓞 K) v
  by_cases hW : primeUnder (𝓞 k) W = primeUnder (𝓞 k) w
  · rw [hW]
    exact (placeInvariant_mk_csa_eq_one_iff k w hf).2
      (isMulCoboundary₂_localCocycle_of_forall_ne k w hf hout hinf)
  · exact (placeInvariant_mk_csa_eq_one_iff k W hf).2 (hout W hW)

end Reciprocity

end

end InverseGalois.CFT

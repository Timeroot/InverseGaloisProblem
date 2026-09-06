/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.H2Surjective
import InverseGalois.CFT.Brauer.PlaceInvariant
import InverseGalois.CFT.TateCohomology.GroupCongr
import InverseGalois.CFT.Units.CompletionHilbert90
import InverseGalois.CFT.Units.IdeleRep

/-!
# The invariant of a class of the decomposition group at a finite place

The decomposition group at a finite place of a Galois extension of number fields is the Galois
group of the completion of the top field over the completion of the base, and the two groups act on
the same object: the units of the completion.  Complete cohomology in degree two is ordinary second
cohomology, so a class of the decomposition group with coefficients in those units is a class of
the Galois group of a finite Galois extension of local fields, hence — through the crossed product
construction — a Brauer class of the completion of the base split by the completion of the top
field.  The invariant map of local class field theory then reads it as a rational modulo the
integers.

Everything in that chain is an isomorphism except the last step, and the last step is injective, so
**the complete cohomology in degree two of a decomposition group at a finite place embeds into the
rationals modulo the integers**, by a map killed by the degree of the local extension.  This is the
local half of the invariant-theoretic description of a fundamental class.

## Main definitions

* `InverseGalois.CFT.decompositionUnitsRep`, `InverseGalois.CFT.completionUnitsRep`: the two
  representations on the units of the completion at a finite place, of the decomposition group and
  of the Galois group of the completion.
* `InverseGalois.CFT.decompositionTwoIso`: **the second cohomology of the Galois group of the
  completion is the complete cohomology in degree two of the decomposition group.**
* `InverseGalois.CFT.decompositionInvariant`: **the invariant of a class of the decomposition group
  at a finite place.**

## Main results

* `InverseGalois.CFT.decompositionInvariant_injective`: **a class of the decomposition group at a
  finite place is determined by its invariant.**
* `InverseGalois.CFT.decompositionInvariant_pow_finrank`: the invariant is killed by the degree of
  the extension of the completions, hence by the order of the decomposition group.

## Tags

number field, decomposition group, local invariant, Brauer group, Tate cohomology
-/

namespace InverseGalois.CFT

open CategoryTheory IsDedekindDomain Module MulAction NumberField Tate

attribute [local instance] isGalois_adicCompletion

noncomputable section

section Decomposition

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (w : HeightOneSpectrum (𝓞 K))

variable (k) in
/-- The representation of the decomposition group at a finite place on the units of the completion
of the top field there. -/
abbrev decompositionUnitsRep : Rep ℤ ↥(stabilizer Gal(K/k) w) :=
  repOfAddAut (smulUnitsAut (G := ↥(stabilizer Gal(K/k) w)) (R := w.adicCompletion K))

variable (k) in
/-- The representation of the Galois group of the completion at a finite place on the units of the
completion. -/
abbrev completionUnitsRep :
    Rep ℤ Gal(w.adicCompletion K/(primeUnder (𝓞 k) w).adicCompletion k) :=
  Rep.ofMulDistribMulAction
    Gal(w.adicCompletion K/(primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K)ˣ

variable (k) in
/-- The comparison of the two representations on the units of a completion.  They have the same
underlying group, and the decomposition group acts through its identification with the Galois group
of the completion. -/
def decompositionUnitsHom :
    (Action.res _ ((stabilizerAlgEquiv k w : ↥(stabilizer Gal(K/k) w) →*
        Gal(w.adicCompletion K/(primeUnder (𝓞 k) w).adicCompletion k)))).obj
        (completionUnitsRep k w) ⟶
      decompositionUnitsRep k w where
  hom := ModuleCat.ofHom LinearMap.id
  comm σ := by
    ext u
    exact congrArg Additive.ofMul (Units.ext rfl)

variable (k) in
/-- **The second cohomology of the Galois group of the completion at a finite place is the complete
cohomology in degree two of the decomposition group there.**  The two groups are isomorphic and the
isomorphism matches their actions on the units of the completion. -/
def decompositionTwoIso :
    groupCohomology (completionUnitsRep k w) 2 ≅ tateModule (decompositionUnitsRep k w) 2 :=
  groupCohomologyCongr (stabilizerAlgEquiv k w) (decompositionUnitsHom k w)
    Function.bijective_id 2

variable (k) in
/-- The complete cohomology in degree two of a decomposition group at a finite place, read as a
Brauer class of the completion of the base split by the completion of the top field. -/
def decompositionBrauer :
    Multiplicative ↥(tateModule (decompositionUnitsRep k w) 2) →*
      BrauerGroup.{0, 0} ((primeUnder (𝓞 k) w).adicCompletion k) :=
  ((BrauerGroup.relative ((primeUnder (𝓞 k) w).adicCompletion k)
        (w.adicCompletion K)).subtype).comp <|
    (brauerRelativeEquiv.toMonoidHom).comp
      (AddEquiv.toMultiplicative
        (decompositionTwoIso k w).symm.toLinearEquiv.toAddEquiv).toMonoidHom

variable (k) in
/-- The Brauer class attached to a class of the decomposition group is split by the completion of
the top field. -/
theorem decompositionBrauer_mem_relative
    (z : Multiplicative ↥(tateModule (decompositionUnitsRep k w) 2)) :
    decompositionBrauer k w z ∈ BrauerGroup.relative
      ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K) :=
  (brauerRelativeEquiv _).2

variable (k) in
/-- **The invariant of a class of the decomposition group at a finite place.**  The class is a
class of the Galois group of the completion, hence a Brauer class of the completion of the base
split by the completion of the top field, and the invariant map of local class field theory reads
it as a rational modulo the integers. -/
def decompositionInvariant :
    Multiplicative ↥(tateModule (decompositionUnitsRep k w) 2) →* Multiplicative QModZ :=
  (localInvariantHom ((primeUnder (𝓞 k) w).adicCompletion k)
      (isUnitValGen_one
        (valued_adicCompletion_surjective (primeUnder (𝓞 k) w)))).comp (decompositionBrauer k w)

variable (k) in
theorem decompositionInvariant_apply
    (z : Multiplicative ↥(tateModule (decompositionUnitsRep k w) 2)) :
    decompositionInvariant k w z
      = localInvariantHom ((primeUnder (𝓞 k) w).adicCompletion k)
          (isUnitValGen_one (valued_adicCompletion_surjective (primeUnder (𝓞 k) w)))
          (decompositionBrauer k w z) := rfl

variable (k) in
/-- **A class of the decomposition group at a finite place is determined by its invariant.**  The
crossed product construction is an isomorphism onto the relative Brauer group, and the invariant
map of a local field is injective. -/
theorem decompositionInvariant_injective :
    Function.Injective (decompositionInvariant k w) := by
  obtain ⟨p, e, hres⟩ := exists_hasResidueChar_adicCompletion (primeUnder (𝓞 k) w)
  have h1 := localInvariantHom_injective ((primeUnder (𝓞 k) w).adicCompletion k) hres
    (isUnitValGen_one (valued_adicCompletion_surjective (primeUnder (𝓞 k) w)))
  exact ((h1.comp Subtype.val_injective).comp brauerRelativeEquiv.injective).comp
    (AddEquiv.toMultiplicative _).injective

variable (k) in
/-- The invariant of a class of the decomposition group at a finite place is killed by the degree
of the extension of the completions there. -/
theorem decompositionInvariant_pow_finrank
    (z : Multiplicative ↥(tateModule (decompositionUnitsRep k w) 2)) :
    decompositionInvariant k w z
        ^ finrank ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K) = 1 := by
  rw [decompositionInvariant_apply, ← map_pow]
  refine (pow_finrank_eq_one_of_mem_relative (L := w.adicCompletion K) _
    (decompositionBrauer_mem_relative k w z)) ▸ ?_
  exact map_one _

end Decomposition

end

end InverseGalois.CFT

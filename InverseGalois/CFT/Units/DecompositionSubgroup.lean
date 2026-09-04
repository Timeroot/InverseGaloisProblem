/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.TateClassCount
import InverseGalois.CFT.Units.DecompositionFundamental

/-!
# The decomposition group at a finite place is a local class formation

A subgroup of the decomposition group at a finite place is again the automorphism group of the
completion of the top field, this time over the subfield the subgroup fixes; that subfield is an
intermediate field of a finite extension of a local field, hence itself a local field, and the
completion is a finite Galois extension of it.  So the whole local theory is available on every
subgroup at once, and not only on the decomposition group itself.

Two consequences are what a class formation asks for.  Hilbert's theorem 90 gives the vanishing of
the first cohomology of the units of the completion over any subgroup.  Local reciprocity over the
fixed subfield counts the relative Brauer group of the completion over it, and the crossed product
construction turns that count into the statement that the complete cohomology in degree two of the
subgroup has exactly as many elements as the subgroup.  The fundamental class of the decomposition
group is annihilated by exactly the multiples of the order of the decomposition group, so the
classical hypotheses of Tate's theorem hold on every subgroup.

**The units of the completion at a finite place are therefore the module of a class formation for
the decomposition group there**, and the theorems of Tate and of Tate and Nakayama apply to them:
the complete cohomology of the trivial integral representation in a degree is the complete
cohomology of the units two degrees higher, and tensoring with a representation flat over the
integers does the same.  This is the local half of the comparison between the global fundamental
class and the local ones.

## Main definitions

* `InverseGalois.CFT.decompositionFixedField`: the subfield of the completion fixed by a subgroup
  of the decomposition group.
* `InverseGalois.CFT.decompositionSubgroupAlgEquiv`: **a subgroup of the decomposition group is the
  automorphism group of the completion over the subfield it fixes.**
* `InverseGalois.CFT.decompositionSubgroupCohomologyIso`: the cohomology of the two groups with
  coefficients in the units of the completion agrees.
* `InverseGalois.CFT.tateLocalUnitsEquiv`: **Tate's theorem for the units of a completion at a
  finite place.**
* `InverseGalois.CFT.tateNakayamaLocalUnits`: **the theorem of Tate and Nakayama for the units of a
  completion at a finite place.**

## Main results

* `InverseGalois.CFT.isZero_tateModule_resObj_decompositionUnits_one`: **the complete cohomology of
  the units of the completion in degree one vanishes on every subgroup of the decomposition
  group.**
* `InverseGalois.CFT.natCard_tateModule_resObj_decompositionUnits_two`: **the complete cohomology
  of the units of the completion in degree two has exactly as many elements as the subgroup**, on
  every subgroup of the decomposition group.
* `InverseGalois.CFT.natCard_stabilizer_eq_finrank`: the order of a decomposition group is the
  degree of the extension of the completions.
* `InverseGalois.CFT.isTateClassTwo_localFundamentalClass`: **the classical hypotheses of Tate's
  theorem hold for the units of the completion, on every subgroup of the decomposition group.**

## Tags

number field, decomposition group, local field, class formation, Hilbert's theorem 90,
local reciprocity, Tate cohomology, Tate-Nakayama
-/

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open CategoryTheory IsDedekindDomain Module MulAction NumberField Tate

attribute [local instance] isGalois_adicCompletion

noncomputable section

section Subgroup

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (w : HeightOneSpectrum (𝓞 K)) (S : Subgroup ↥(stabilizer Gal(K/k) w))

/-! ### A subgroup of the decomposition group as an automorphism group -/

variable (k) in
/-- The subgroup of the automorphism group of the completion at a finite place named by a subgroup
of the decomposition group there. -/
abbrev decompositionMapSubgroup :
    Subgroup Gal(w.adicCompletion K/(primeUnder (𝓞 k) w).adicCompletion k) :=
  S.map (stabilizerAlgEquiv k w).toMonoidHom

variable (k) in
/-- **The subfield of the completion at a finite place fixed by a subgroup of the decomposition
group there.**  It is an intermediate field of a finite extension of a local field, hence itself a
local field. -/
abbrev decompositionFixedField :
    IntermediateField ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K) :=
  IntermediateField.fixedField (decompositionMapSubgroup k w S)

variable (k) in
/-- **A subgroup of the decomposition group at a finite place is the automorphism group of the
completion over the subfield it fixes.**  The decomposition group is the automorphism group of the
completion, and a subgroup of a finite Galois group is the automorphism group over its fixed
field. -/
def decompositionSubgroupAlgEquiv :
    ↥S ≃* Gal(w.adicCompletion K/↥(decompositionFixedField k w S)) :=
  (S.equivMapOfInjective (stabilizerAlgEquiv k w).toMonoidHom
      (stabilizerAlgEquiv k w).injective).trans
    (IntermediateField.subgroupEquivAlgEquiv (decompositionMapSubgroup k w S))

variable (k) in
@[simp]
theorem decompositionSubgroupAlgEquiv_apply (σ : ↥S) (z : w.adicCompletion K) :
    decompositionSubgroupAlgEquiv k w S σ z = (σ : ↥(stabilizer Gal(K/k) w)) • z := rfl

/-! ### The cohomology of a subgroup -/

variable (k) in
/-- The representation of the automorphism group of the completion at a finite place over the
subfield fixed by a subgroup of the decomposition group, on the units of the completion. -/
abbrev subgroupCompletionUnitsRep :
    Rep ℤ Gal(w.adicCompletion K/↥(decompositionFixedField k w S)) :=
  Rep.ofMulDistribMulAction Gal(w.adicCompletion K/↥(decompositionFixedField k w S))
    (w.adicCompletion K)ˣ

variable (k) in
/-- The comparison of the two representations on the units of a completion at a finite place: the
one of a subgroup of the decomposition group, and the one of the automorphism group of the
completion over the subfield the subgroup fixes.  They have the same underlying group, and the
subgroup acts through its identification with that automorphism group. -/
def decompositionSubgroupUnitsHom :
    (Action.res _ ((decompositionSubgroupAlgEquiv k w S :
        ↥S →* Gal(w.adicCompletion K/↥(decompositionFixedField k w S))))).obj
        (subgroupCompletionUnitsRep k w S) ⟶
      resObj S (decompositionUnitsRep k w) where
  hom := ModuleCat.ofHom LinearMap.id
  comm σ := by
    ext u
    exact congrArg Additive.ofMul (Units.ext rfl)

variable (k) in
/-- **The cohomology of a subgroup of the decomposition group at a finite place with coefficients
in the units of the completion is the cohomology of the automorphism group of the completion over
the subfield the subgroup fixes.** -/
def decompositionSubgroupCohomologyIso (n : ℕ) :
    groupCohomology (subgroupCompletionUnitsRep k w S) n ≅
      groupCohomology (resObj S (decompositionUnitsRep k w)) n :=
  groupCohomologyCongr (decompositionSubgroupAlgEquiv k w S)
    (decompositionSubgroupUnitsHom k w S) Function.bijective_id n

/-! ### Degree one -/

variable (k) in
/-- **The complete cohomology of the units of the completion at a finite place in degree one
vanishes on every subgroup of the decomposition group there.**  The subgroup is the automorphism
group of the completion over the subfield it fixes, and the completion is a finite extension of
that subfield, so Hilbert's theorem 90 applies. -/
theorem isZero_tateModule_resObj_decompositionUnits_one :
    Limits.IsZero (tateModule (resObj S (decompositionUnitsRep k w)) 1) := by
  haveI : Unique ↥(groupCohomology (subgroupCompletionUnitsRep k w S) 1) :=
    groupCohomology.H1ofAutOnUnitsUnique ↥(decompositionFixedField k w S) (w.adicCompletion K)
  refine Limits.IsZero.of_iso ?_ (decompositionSubgroupCohomologyIso k w S 1).symm
  exact isZero_of_forall_eq_zero fun x => Subsingleton.elim x 0

/-! ### Degree two -/

variable (k) in
/-- **The complete cohomology in degree two of a subgroup of the decomposition group at a finite
place is the relative Brauer group of the completion over the subfield the subgroup fixes.** -/
def decompositionSubgroupBrauerEquiv :
    Multiplicative ↥(tateModule (resObj S (decompositionUnitsRep k w)) 2) ≃*
      ↥(BrauerGroup.relative ↥(decompositionFixedField k w S) (w.adicCompletion K)) :=
  (AddEquiv.toMultiplicative
    (decompositionSubgroupCohomologyIso k w S 2).symm.toLinearEquiv.toAddEquiv).trans
      brauerRelativeEquiv

variable (k) in
/-- The complete cohomology in degree two of a subgroup of the decomposition group at a finite
place is finite. -/
theorem finite_tateModule_resObj_decompositionUnits_two :
    Finite ↥(tateModule (resObj S (decompositionUnitsRep k w)) 2) := by
  obtain ⟨p, e, hres⟩ := exists_hasResidueChar_adicCompletion (primeUnder (𝓞 k) w)
  haveI := finite_relative_tower (K := (primeUnder (𝓞 k) w).adicCompletion k)
    ↥(decompositionFixedField k w S) (w.adicCompletion K) hres
    (isUnitValGen_one (valued_adicCompletion_surjective (primeUnder (𝓞 k) w)))
  haveI : Finite (Multiplicative ↥(tateModule (resObj S (decompositionUnitsRep k w)) 2)) :=
    Finite.of_equiv _ (decompositionSubgroupBrauerEquiv k w S).symm.toEquiv
  exact Finite.of_equiv _ (Multiplicative.toAdd (α := _))

variable (k) in
/-- **The complete cohomology in degree two of a subgroup of the decomposition group at a finite
place has exactly as many elements as the subgroup.**  It is the relative Brauer group of the
completion over the subfield the subgroup fixes, which local reciprocity counts by the degree, and
that degree is the order of the automorphism group. -/
theorem natCard_tateModule_resObj_decompositionUnits_two :
    Nat.card ↥(tateModule (resObj S (decompositionUnitsRep k w)) 2) = Nat.card ↥S := by
  obtain ⟨p, e, hres⟩ := exists_hasResidueChar_adicCompletion (primeUnder (𝓞 k) w)
  have h1 : Nat.card ↥(tateModule (resObj S (decompositionUnitsRep k w)) 2)
      = Nat.card ↥(BrauerGroup.relative ↥(decompositionFixedField k w S)
        (w.adicCompletion K)) :=
    Nat.card_congr ((Multiplicative.toAdd (α :=
      ↥(tateModule (resObj S (decompositionUnitsRep k w)) 2))).symm.trans
        (decompositionSubgroupBrauerEquiv k w S).toEquiv)
  rw [h1, card_relative_eq_finrank_tower (K := (primeUnder (𝓞 k) w).adicCompletion k)
      ↥(decompositionFixedField k w S) (w.adicCompletion K) hres
      (isUnitValGen_one (valued_adicCompletion_surjective (primeUnder (𝓞 k) w))),
    ← IsGalois.card_aut_eq_finrank ↥(decompositionFixedField k w S) (w.adicCompletion K)]
  exact (Nat.card_congr (decompositionSubgroupAlgEquiv k w S).toEquiv).symm

/-! ### The hypotheses of Tate's theorem -/

variable (k) in
/-- **The order of a decomposition group at a finite place is the degree of the extension of the
completions there.** -/
theorem natCard_stabilizer_eq_finrank :
    Nat.card ↥(stabilizer Gal(K/k) w)
      = finrank ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K) := by
  rw [Nat.card_congr (stabilizerAlgEquiv k w).toEquiv]
  exact IsGalois.card_aut_eq_finrank ((primeUnder (𝓞 k) w).adicCompletion k)
    (w.adicCompletion K)

variable (k) in
/-- **Only the multiples of the order of the decomposition group at a finite place annihilate the
fundamental class there.**  The order of the fundamental class is the degree of the extension of
the completions, which is the order of the decomposition group. -/
theorem dvd_of_zsmul_localFundamentalClass_eq_zero (m : ℤ)
    (hm : m • Multiplicative.toAdd (localFundamentalClass k w) = 0) :
    (Nat.card ↥(stabilizer Gal(K/k) w) : ℤ) ∣ m := by
  have hord : addOrderOf (Multiplicative.toAdd (localFundamentalClass k w))
      = orderOf (localFundamentalClass k w) := rfl
  rw [natCard_stabilizer_eq_finrank k w, ← orderOf_localFundamentalClass k w, ← hord]
  exact addOrderOf_dvd_iff_zsmul_eq_zero.2 hm

variable (k) in
/-- **The classical hypotheses of Tate's theorem hold for the units of the completion at a finite
place, on every subgroup of the decomposition group there.**  The cohomology vanishes in degree one
by Hilbert's theorem 90, it has exactly as many elements as the subgroup in degree two by local
reciprocity, and the fundamental class is annihilated by exactly the multiples of the order of the
decomposition group. -/
theorem isTateClassTwo_localFundamentalClass :
    IsTateClassTwo S (decompositionUnitsRep k w)
      (Multiplicative.toAdd (localFundamentalClass k w)) :=
  isTateClassTwo_of_card_le S (isZero_tateModule_resObj_decompositionUnits_one k w S)
    (finite_tateModule_resObj_decompositionUnits_two k w S)
    (natCard_tateModule_resObj_decompositionUnits_two k w S).le
    (dvd_of_zsmul_localFundamentalClass_eq_zero k w)

/-! ### Tate's theorem at a finite place -/

variable (k) in
/-- **Tate's theorem for the units of a completion at a finite place**: the complete cohomology of
the trivial integral representation of the decomposition group in a degree is the complete
cohomology of the units of the completion two degrees higher. -/
def tateLocalUnitsEquiv (n : ℤ) :
    tateModule (Rep.trivial ℤ ↥(stabilizer Gal(K/k) w) ℤ) n ≃ₗ[ℤ]
      tateModule (decompositionUnitsRep k w) (n + 1 + 1) :=
  tateTheoremTwoEquivOfCard (decompositionUnitsRep k w)
    (Multiplicative.toAdd (localFundamentalClass k w))
    (fun H => isZero_tateModule_resObj_decompositionUnits_one k w H)
    (fun H => finite_tateModule_resObj_decompositionUnits_two k w H)
    (fun H => (natCard_tateModule_resObj_decompositionUnits_two k w H).le)
    (dvd_of_zsmul_localFundamentalClass_eq_zero k w) n

variable (k) in
/-- **The theorem of Tate and Nakayama for the units of a completion at a finite place**: for
coefficients flat over the integers, the complete cohomology of a representation of the
decomposition group in a degree is the complete cohomology of its tensor product with the units of
the completion two degrees higher. -/
def tateNakayamaLocalUnits (M : Rep ℤ ↥(stabilizer Gal(K/k) w)) (hM : Module.Flat ℤ ↥M.V)
    (n : ℤ) :
    tateModule M n ≃ₗ[ℤ] tateModule (tensorObj (decompositionUnitsRep k w) M) (n + 1 + 1) :=
  tateNakayamaFlatEquivOfCard (decompositionUnitsRep k w)
    (Multiplicative.toAdd (localFundamentalClass k w))
    (fun H => isZero_tateModule_resObj_decompositionUnits_one k w H)
    (fun H => finite_tateModule_resObj_decompositionUnits_two k w H)
    (fun H => (natCard_tateModule_resObj_decompositionUnits_two k w H).le)
    (dvd_of_zsmul_localFundamentalClass_eq_zero k w) M hM n

end Subgroup

end

end InverseGalois.CFT

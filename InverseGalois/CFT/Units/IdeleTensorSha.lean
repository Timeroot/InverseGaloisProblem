/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.IdeleTensorTorsion

/-!
# The locally trivial classes with coefficients killed by a prime

The units of a number field, its ideles and its idele classes stay short exact after tensoring with
coefficients killed by a prime, so the long exact sequence of complete cohomology reads the kernel
of the map from the units to the ideles in one degree as the image of the connecting map coming out
of the idele classes one degree lower.  Since the cohomology of the ideles is the product over the
places of the cohomology of the completions, that kernel is the group of everywhere locally trivial
classes.

**So the locally trivial classes of the units tensored with coefficients killed by a prime are a
quotient of the complete cohomology of the idele classes tensored with the same coefficients, one
degree lower.**  The statement holds in every degree and needs no hypothesis on the extension beyond
finiteness of its Galois group; the whole content is the Hasse principle for powers, which is what
kept the tensored sequence exact.

The same reading applies to the elements killed by the prime of the three groups, whose sequence
stays exact after tensoring with anything.  That case is what measures the failure of the theorem of
Tate and Nakayama for coefficients with torsion, since the elements of the idele classes killed by
the prime are the first derived tensor product of the idele classes with such coefficients.

## Main results

* `InverseGalois.CFT.range_tateδ_tensor_ideleClass`: **the locally trivial classes of the units
  tensored with coefficients killed by a prime are exactly the image of the connecting map** from
  the complete cohomology of the idele classes tensored with the same coefficients.
* `InverseGalois.CFT.isZero_tateModule_tensor_ideleClass_globalUnits`: the units tensored with such
  coefficients have no locally trivial classes in a degree in which the idele classes tensored with
  them have no complete cohomology one degree lower.
* `InverseGalois.CFT.range_tateδ_tensor_ideleClassTorsion`,
  `InverseGalois.CFT.isZero_tateModule_tensor_ideleClassTorsion`: the same two statements for the
  elements of the three groups killed by the prime.

## Tags

number field, idele class group, Tate cohomology, Tate-Shafarevich group, tensor product
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open CategoryTheory Tate

noncomputable section

variable {k K : Type} [Field k] [Field K] [NumberField K] [Algebra k K] [Finite Gal(K/k)]
  {p : ℕ} (hp : p.Prime) (W : Rep ℤ Gal(K/k))

/-! ### The units, the ideles and the idele classes -/

section Full

variable (hW : ∀ w : ↥W.V, p • w = 0)

include hp hW

/-- The classes produced by the connecting map die in the ideles. -/
theorem tateMap_tateδ_tensor_ideleClass_eq_zero (n : ℤ)
    (y : ↥(tateModule (tensorObj (ideleClassRep k K) W) n)) :
    tateMap (tensorHomLeft W (globalUnitsToIdele k K)) (n + 1)
        (tateδ (tensorSeq_ideleClassShortComplex_shortExact_of_nsmul hp W hW) n y) = 0 :=
  (tateExact_δ_map (tensorSeq_ideleClassShortComplex_shortExact_of_nsmul hp W hW)
    n).apply_apply_eq_zero y

/-- Every class of the units tensored with coefficients killed by a prime which dies in the ideles
comes from the complete cohomology of the idele classes one degree lower. -/
theorem exists_tateδ_tensor_ideleClass_eq (n : ℤ)
    (x : ↥(tateModule (tensorObj (globalUnitsRep k K) W) (n + 1)))
    (hx : tateMap (tensorHomLeft W (globalUnitsToIdele k K)) (n + 1) x = 0) :
    ∃ y : ↥(tateModule (tensorObj (ideleClassRep k K) W) n),
      tateδ (tensorSeq_ideleClassShortComplex_shortExact_of_nsmul hp W hW) n y = x :=
  (tateExact_δ_map (tensorSeq_ideleClassShortComplex_shortExact_of_nsmul hp W hW) n x).1 hx

/-- **The locally trivial classes of the units tensored with coefficients killed by a prime are
exactly the image of the connecting map** coming out of the complete cohomology of the idele classes
tensored with the same coefficients, one degree lower.  The kernel on the right is the group of
everywhere locally trivial classes, because the cohomology of the ideles is the product over the
places of the cohomology of the completions. -/
theorem range_tateδ_tensor_ideleClass (n : ℤ) :
    LinearMap.range (tateδ (tensorSeq_ideleClassShortComplex_shortExact_of_nsmul hp W hW) n).hom
      = LinearMap.ker (tateMap (tensorHomLeft W (globalUnitsToIdele k K)) (n + 1)).hom := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker]
  refine ⟨?_, exists_tateδ_tensor_ideleClass_eq hp W hW n x⟩
  rintro ⟨y, rfl⟩
  exact tateMap_tateδ_tensor_ideleClass_eq_zero hp W hW n y

/-- **The units tensored with coefficients killed by a prime have no locally trivial classes in a
degree in which the idele classes tensored with the same coefficients have no complete cohomology
one degree lower.** -/
theorem isZero_tateModule_tensor_ideleClass_globalUnits (n : ℤ)
    (h : Limits.IsZero (tateModule (tensorObj (ideleClassRep k K) W) n)) :
    LinearMap.ker (tateMap (tensorHomLeft W (globalUnitsToIdele k K)) (n + 1)).hom = ⊥ := by
  rw [← range_tateδ_tensor_ideleClass hp W hW n]
  refine le_antisymm ?_ bot_le
  rintro _ ⟨y, rfl⟩
  rw [eq_zero_of_isZero h y, map_zero]
  exact Submodule.zero_mem _

/-- **The idele classes tensored with coefficients killed by a prime have no complete cohomology in
a degree in which the ideles tensored with them have none and the units tensored with them have none
one degree higher.** -/
theorem isZero_tateModule_tensor_ideleClass (n : ℤ)
    (h₂ : Limits.IsZero (tateModule (tensorObj (ideleRep k K) W) n))
    (h₁ : Limits.IsZero (tateModule (tensorObj (globalUnitsRep k K) W) (n + 1))) :
    Limits.IsZero (tateModule (tensorObj (ideleClassRep k K) W) n) :=
  isZero_tateModule_X₃ (tensorSeq_ideleClassShortComplex_shortExact_of_nsmul hp W hW) n h₂ h₁

end Full

/-! ### The elements killed by the prime -/

section Torsion

include hp

/-- The classes produced by the connecting map of the sequence of the elements killed by the prime
die in the ideles. -/
theorem tateMap_tateδ_tensor_ideleClassTorsion_eq_zero (n : ℤ)
    (y : ↥(tateModule (tensorObj (torsionRep (ideleClassAutHom k K) (p : ℤ)) W) n)) :
    tateMap (tensorHomLeft W (globalUnitsToIdeleTorsion k K (p : ℤ))) (n + 1)
        (tateδ (tensorSeq_ideleClassTorsionShortComplex_shortExact hp W) n y) = 0 :=
  (tateExact_δ_map (tensorSeq_ideleClassTorsionShortComplex_shortExact hp W)
    n).apply_apply_eq_zero y

/-- Every class of the roots of unity of the field tensored with the coefficients which dies in the
ideles comes from the complete cohomology of the idele classes killed by the prime, tensored with
the same coefficients, one degree lower. -/
theorem exists_tateδ_tensor_ideleClassTorsion_eq (n : ℤ)
    (x : ↥(tateModule (tensorObj (torsionRep (globalUnitsAut (k := k) (K := K)) (p : ℤ)) W)
      (n + 1)))
    (hx : tateMap (tensorHomLeft W (globalUnitsToIdeleTorsion k K (p : ℤ))) (n + 1) x = 0) :
    ∃ y : ↥(tateModule (tensorObj (torsionRep (ideleClassAutHom k K) (p : ℤ)) W) n),
      tateδ (tensorSeq_ideleClassTorsionShortComplex_shortExact hp W) n y = x :=
  (tateExact_δ_map (tensorSeq_ideleClassTorsionShortComplex_shortExact hp W) n x).1 hx

/-- **The everywhere locally trivial classes of the roots of unity of the field tensored with the
coefficients are exactly the image of the connecting map** coming out of the complete cohomology of
the idele classes killed by the prime, tensored with the same coefficients, one degree lower. -/
theorem range_tateδ_tensor_ideleClassTorsion (n : ℤ) :
    LinearMap.range (tateδ (tensorSeq_ideleClassTorsionShortComplex_shortExact hp W) n).hom
      = LinearMap.ker
        (tateMap (tensorHomLeft W (globalUnitsToIdeleTorsion k K (p : ℤ))) (n + 1)).hom := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker]
  refine ⟨?_, exists_tateδ_tensor_ideleClassTorsion_eq hp W n x⟩
  rintro ⟨y, rfl⟩
  exact tateMap_tateδ_tensor_ideleClassTorsion_eq_zero hp W n y

/-- **The idele classes killed by a prime, tensored with any coefficients, have no complete
cohomology in a degree in which the ideles killed by the prime have none after tensoring and the
roots of unity of the field have none one degree higher.**  This is the term that measures the
failure of the theorem of Tate and Nakayama for coefficients with torsion. -/
theorem isZero_tateModule_tensor_ideleClassTorsion (n : ℤ)
    (h₂ : Limits.IsZero (tateModule (tensorObj (torsionRep (ideleAutHom k K) (p : ℤ)) W) n))
    (h₁ : Limits.IsZero
      (tateModule (tensorObj (torsionRep (globalUnitsAut (k := k) (K := K)) (p : ℤ)) W) (n + 1))) :
    Limits.IsZero (tateModule (tensorObj (torsionRep (ideleClassAutHom k K) (p : ℤ)) W) n) :=
  isZero_tateModule_X₃ (tensorSeq_ideleClassTorsionShortComplex_shortExact hp W) n h₂ h₁

end Torsion

end

end InverseGalois.CFT

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.BaseChange
import InverseGalois.CFT.Brauer.SmoothInvariant
import InverseGalois.CFT.Local.AdicHerbrand
import InverseGalois.CFT.Local.AdicLocalField
import InverseGalois.CFT.Local.AdicUnits

/-!
# The invariant of a Brauer class at a finite place of a number field

A central simple algebra over a number field can be completed at a finite place, and the resulting
central simple algebra over a local field has an invariant, a rational number modulo the integers.
This assignment is the localization of the Brauer group at the place: it is the composition of base
change to the completion with the invariant map of local class field theory, and it vanishes exactly
on the classes that the completion splits.

The completion of a number field at a finite place satisfies every hypothesis of the local theory:
it is complete, its value group is the integers, its residue field is finite, hence it is a proper
metric space, and it has characteristic zero, hence is perfect.  The residue characteristic that the
local invariant map needs is the characteristic of the residue field, which is available for every
place.

Transporting along the identification of the Brauer group of a perfect field with the smooth second
cohomology of its absolute Galois group turns base change into a homomorphism of cohomology groups
and the invariant into a homomorphism out of the smooth second cohomology, without any continuity
argument about the map of Galois groups.

## Main definitions

* `InverseGalois.CFT.smoothBaseChange`: base change of the smooth second cohomology of an absolute
  Galois group with coefficients in the units of an algebraic closure.
* `InverseGalois.CFT.placeInvariant`: **the invariant of a Brauer class of a number field at a
  finite place.**
* `InverseGalois.CFT.smoothPlaceInvariant`: the invariant at a finite place, read on the smooth
  second cohomology of the absolute Galois group.

## Main results

* `InverseGalois.CFT.smoothBaseChange_self`, `InverseGalois.CFT.smoothBaseChange_comp`: base change
  of the smooth second cohomology is functorial in the field.
* `InverseGalois.CFT.placeInvariant_eq_one_iff`: **a Brauer class of a number field has trivial
  invariant at a place exactly when the completion at that place splits it.**

## Tags

Brauer group, number field, local invariant, localization, class field theory
-/

set_option synthInstance.maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

open scoped Valued WithZero

/-! ### Base change of the smooth second cohomology -/

section BaseChange

universe u

/-- **Base change of the smooth second cohomology of an absolute Galois group** with coefficients
in the units of an algebraic closure, read through the Brauer group. -/
noncomputable def smoothBaseChange (k K : Type u) [Field k] [PerfectField k] [Field K]
    [PerfectField K] [Algebra k K] :
    SmoothH2 Gal(AlgebraicClosure k/k) (AlgebraicClosure k)ˣ →*
      SmoothH2 Gal(AlgebraicClosure K/K) (AlgebraicClosure K)ˣ :=
  (smoothBrauerEquiv K).symm.toMonoidHom.comp
    ((BrauerGroup.baseChangeHom K).comp (smoothBrauerEquiv k).toMonoidHom)

@[simp]
theorem smoothBrauerEquiv_smoothBaseChange (k K : Type u) [Field k] [PerfectField k] [Field K]
    [PerfectField K] [Algebra k K]
    (z : SmoothH2 Gal(AlgebraicClosure k/k) (AlgebraicClosure k)ˣ) :
    smoothBrauerEquiv K (smoothBaseChange k K z)
      = BrauerGroup.baseChangeHom K (smoothBrauerEquiv k z) :=
  (smoothBrauerEquiv K).apply_symm_apply _

/-- Base change along the identity extension is the identity. -/
theorem smoothBaseChange_self (k : Type u) [Field k] [PerfectField k] :
    smoothBaseChange k k = MonoidHom.id _ := by
  refine MonoidHom.ext fun z => (smoothBrauerEquiv k).injective ?_
  rw [smoothBrauerEquiv_smoothBaseChange, BrauerGroup.baseChangeHom_self, MonoidHom.id_apply,
    MonoidHom.id_apply]

/-- Base change of the smooth second cohomology is functorial in the field. -/
theorem smoothBaseChange_comp (k K L : Type u) [Field k] [PerfectField k] [Field K]
    [PerfectField K] [Field L] [PerfectField L] [Algebra k K] [Algebra K L] [Algebra k L]
    [IsScalarTower k K L] :
    (smoothBaseChange K L).comp (smoothBaseChange k K) = smoothBaseChange k L := by
  refine MonoidHom.ext fun z => (smoothBrauerEquiv L).injective ?_
  rw [MonoidHom.coe_comp, Function.comp_apply, smoothBrauerEquiv_smoothBaseChange,
    smoothBrauerEquiv_smoothBaseChange, smoothBrauerEquiv_smoothBaseChange,
    ← BrauerGroup.baseChangeHom_comp k K L, MonoidHom.coe_comp, Function.comp_apply]

end BaseChange

/-! ### The completion at a finite place is perfect -/

section Perfect

variable {k : Type*} [Field k] [NumberField k]

instance charZero_adicCompletion (v : HeightOneSpectrum (𝓞 k)) :
    CharZero (v.adicCompletion k) :=
  charZero_of_injective_algebraMap (algebraMap k (v.adicCompletion k)).injective

end Perfect

/-! ### The invariant at a finite place -/

section Place

variable {k : Type} [Field k] [NumberField k]

variable (k) in
/-- **The invariant of a Brauer class of a number field at a finite place**: base change the
algebra to the completion, and take the invariant of local class field theory. -/
noncomputable def placeInvariant (v : HeightOneSpectrum (𝓞 k)) :
    BrauerGroup.{0, 0} k →* Multiplicative QModZ :=
  (localInvariantHom (v.adicCompletion k)
      (isUnitValGen_one (valued_adicCompletion_surjective v))).comp
    (BrauerGroup.baseChangeHom (v.adicCompletion k))

theorem placeInvariant_apply (v : HeightOneSpectrum (𝓞 k)) (x : BrauerGroup.{0, 0} k) :
    placeInvariant k v x
      = localInvariantHom (v.adicCompletion k)
          (isUnitValGen_one (valued_adicCompletion_surjective v))
          (BrauerGroup.baseChangeHom (v.adicCompletion k) x) := rfl

/-- **A Brauer class of a number field has trivial invariant at a place exactly when the completion
at that place splits it.**  The invariant map of a local field is injective. -/
theorem placeInvariant_eq_one_iff (v : HeightOneSpectrum (𝓞 k)) (x : BrauerGroup.{0, 0} k) :
    placeInvariant k v x = 1 ↔ x ∈ BrauerGroup.relative k (v.adicCompletion k) := by
  obtain ⟨p, e, hres⟩ := exists_hasResidueChar_adicCompletion v
  rw [BrauerGroup.relative, MonoidHom.mem_ker, placeInvariant_apply]
  refine ⟨fun h => localInvariantHom_injective (v.adicCompletion k) hres
    (isUnitValGen_one (valued_adicCompletion_surjective v)) ?_, fun h => by rw [h, map_one]⟩
  rw [h, map_one]

/-- A class split by the completion at a place has trivial invariant there. -/
theorem placeInvariant_eq_one_of_mem_relative (v : HeightOneSpectrum (𝓞 k))
    {x : BrauerGroup.{0, 0} k} (hx : x ∈ BrauerGroup.relative k (v.adicCompletion k)) :
    placeInvariant k v x = 1 :=
  (placeInvariant_eq_one_iff v x).2 hx

end Place

/-! ### The invariant at a finite place on the smooth second cohomology -/

section Smooth

variable {k : Type} [Field k] [NumberField k]

variable (k) in
/-- The invariant at a finite place, read on the smooth second cohomology of the absolute Galois
group with coefficients in the units of an algebraic closure. -/
noncomputable def smoothPlaceInvariant (v : HeightOneSpectrum (𝓞 k)) :
    SmoothH2 Gal(AlgebraicClosure k/k) (AlgebraicClosure k)ˣ →* Multiplicative QModZ :=
  (placeInvariant k v).comp (smoothBrauerEquiv k).toMonoidHom

theorem smoothPlaceInvariant_apply (v : HeightOneSpectrum (𝓞 k))
    (z : SmoothH2 Gal(AlgebraicClosure k/k) (AlgebraicClosure k)ˣ) :
    smoothPlaceInvariant k v z = placeInvariant k v (smoothBrauerEquiv k z) := rfl

/-- The invariant at a finite place is the local invariant of the base change of the cohomology
class to the completion. -/
theorem smoothPlaceInvariant_eq_smoothLocalInvariantEquiv {p e : ℕ}
    (v : HeightOneSpectrum (𝓞 k)) (hres : HasResidueChar (v.adicCompletion k) p e)
    (z : SmoothH2 Gal(AlgebraicClosure k/k) (AlgebraicClosure k)ˣ) :
    smoothPlaceInvariant k v z
      = smoothLocalInvariantEquiv (v.adicCompletion k) hres
          (isUnitValGen_one (valued_adicCompletion_surjective v))
          (smoothBaseChange k (v.adicCompletion k) z) := by
  rw [smoothPlaceInvariant_apply, placeInvariant_apply, smoothLocalInvariantEquiv_apply,
    ← smoothBrauerEquiv_apply, smoothBrauerEquiv_smoothBaseChange]

end Smooth

end InverseGalois.CFT

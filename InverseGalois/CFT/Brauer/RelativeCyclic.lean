/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.CyclicNormResidue
import InverseGalois.CFT.Brauer.RelativeHasse
import InverseGalois.CFT.Units.CompletionCyclic

/-!
# When a cyclic extension of number fields splits a Brauer class

A cyclic extension of a local field splits exactly the classes killed by its degree.  The completion
of a cyclic extension of number fields at a prime is a cyclic extension of the completion at the
prime below, so at a finite place the condition for the completion of the extension to split a
Brauer class of the base is that the invariant there be killed by the local degree.

Combining this with the Hasse principle for the relative Brauer group gives a criterion for a class
to be split by the whole extension: its invariant at each finite place is killed by the local
degree, and each real place of the extension splits it.  The complex places impose no condition,
and neither does a finite place whose local degree is one.

## Main results

* `InverseGalois.CFT.mem_relative_adicCompletion_iff_pow_placeInvariant`: **the completion of a
  cyclic extension at a prime splits a Brauer class of the base exactly when the invariant at the
  prime below is killed by the local degree.**
* `InverseGalois.CFT.mem_relative_iff_forall_pow_placeInvariant`: **a cyclic extension of number
  fields splits a Brauer class exactly when every local degree kills the invariant at the place
  below and every real place of the extension splits the class.**

## Tags

Brauer group, number field, cyclic extension, local degree, local invariant, Hasse principle,
class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain Module NumberField

section RelativeCyclic

variable {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L] [Algebra k L]
  [IsGalois k L] [IsCyclic Gal(L/k)]

/-- **The completion of a cyclic extension of number fields at a prime splits a Brauer class of the
base exactly when the invariant at the prime below is killed by the local degree.**  The completion
is a cyclic extension of the completion below, and a cyclic extension of a local field splits
exactly the classes killed by its degree. -/
theorem mem_relative_adicCompletion_iff_pow_placeInvariant (w : HeightOneSpectrum (𝓞 L))
    (x : BrauerGroup.{0, 0} k) :
    x ∈ BrauerGroup.relative k (w.adicCompletion L) ↔
      placeInvariant k (primeUnder (𝓞 k) w) x
          ^ finrank ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion L) = 1 := by
  haveI := isGalois_adicCompletion k w
  haveI := isCyclic_algEquiv_adicCompletion k w
  obtain ⟨σ₀, hσ₀⟩ :=
    IsCyclic.exists_generator (α := w.adicCompletion L
      ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion L)
  obtain ⟨p, e, hres⟩ := exists_hasResidueChar_adicCompletion (primeUnder (𝓞 k) w)
  rw [mem_relative_adicCompletion_iff_baseChange,
    relative_eq_brauerTorsion_of_cyclic hσ₀ hres
      (isUnitValGen_one (valued_adicCompletion_surjective (primeUnder (𝓞 k) w))),
    mem_brauerTorsion, placeInvariant_apply]
  refine ⟨fun h => by rw [← map_pow, h, map_one], fun h => ?_⟩
  refine localInvariantHom_injective ((primeUnder (𝓞 k) w).adicCompletion k) hres
    (isUnitValGen_one (valued_adicCompletion_surjective (primeUnder (𝓞 k) w))) ?_
  rw [map_pow, h, map_one]

/-- **A cyclic extension of number fields splits a Brauer class exactly when every local degree
kills the invariant at the place below and every real place of the extension splits the class.**
The complex places impose no condition. -/
theorem mem_relative_iff_forall_pow_placeInvariant (x : BrauerGroup.{0, 0} k) :
    x ∈ BrauerGroup.relative k L ↔
      (∀ w : HeightOneSpectrum (𝓞 L), placeInvariant k (primeUnder (𝓞 k) w) x
          ^ finrank ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion L) = 1) ∧
      (∀ U : InfinitePlace L, U.IsReal → x ∈ BrauerGroup.relative k U.Completion) := by
  rw [mem_relative_iff_forall_completion]
  refine and_congr (forall_congr' fun w => ?_) Iff.rfl
  exact mem_relative_adicCompletion_iff_pow_placeInvariant w x

end RelativeCyclic

end InverseGalois.CFT

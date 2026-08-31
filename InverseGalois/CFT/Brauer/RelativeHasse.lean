/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.TotalInvariant
import InverseGalois.CFT.Units.CompletionGalois

/-!
# The Hasse principle for the relative Brauer group

A Brauer class of a number field is split by a finite extension exactly when it is split by every
completion of that extension.  One direction is monotonicity of the relative Brauer group: a class
split by the extension is split by anything containing it.  The other is the
Albert-Brauer-Hasse-Noether theorem applied over the extension, together with the functoriality of
base change: the completion of the base-changed class at a place of the extension and the base
change of the original class to that completion are the same class read two ways.

At a complex place the completion is isomorphic to the complex numbers over the base, so it splits
everything and imposes no condition; only the finite places and the real places of the extension
are left.  At a finite place the condition can be tested one step lower, over the completion of the
base at the prime below, again by functoriality of base change.  Since the completion of the
extension is a finite Galois extension of the completion of the base, this is a condition of local
class field theory.

## Main results

* `InverseGalois.CFT.relative_completion_eq_top_of_isComplex_extension`: a complex place of an
  extension splits every Brauer class of the base.
* `InverseGalois.CFT.mem_relative_iff_forall_completion`: **a Brauer class of a number field is
  split by a finite extension exactly when it is split by every completion of that extension**, the
  complex places imposing no condition.
* `InverseGalois.CFT.mem_relative_adicCompletion_iff_baseChange`: **splitting by a completion of the
  extension is a condition over the completion of the base.**

## Tags

Brauer group, number field, completion, Hasse principle, relative Brauer group,
Albert-Brauer-Hasse-Noether, class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

section RelativeHasse

variable {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L] [Algebra k L]

/-! ### The completions of the extension split what the extension splits -/

omit [NumberField k] in
/-- A class split by an extension is split by each of its finite completions. -/
theorem mem_relative_adicCompletion_of_mem_relative (w : HeightOneSpectrum (𝓞 L))
    {x : BrauerGroup.{0, 0} k} (hx : x ∈ BrauerGroup.relative k L) :
    x ∈ BrauerGroup.relative k (w.adicCompletion L) :=
  BrauerGroup.relative_le_relative k L (w.adicCompletion L) hx

omit [NumberField k] [NumberField L] in
/-- A class split by an extension is split by each of its infinite completions. -/
theorem mem_relative_infiniteCompletion_of_mem_relative (U : InfinitePlace L)
    {x : BrauerGroup.{0, 0} k} (hx : x ∈ BrauerGroup.relative k L) :
    x ∈ BrauerGroup.relative k U.Completion :=
  BrauerGroup.relative_le_relative k L U.Completion hx

/-! ### A complex place of the extension imposes no condition -/

omit [NumberField k] [NumberField L] in
/-- **A complex place of an extension splits every Brauer class of the base.**  The completion
there is isomorphic over the base to the complex numbers, which are algebraically closed. -/
theorem relative_completion_eq_top_of_isComplex_extension {U : InfinitePlace L}
    (hU : U.IsComplex) : BrauerGroup.relative k U.Completion = ⊤ := by
  letI : Algebra k ℂ := (U.embedding.comp (algebraMap k L)).toAlgebra
  have hmap : ∀ r : k,
      NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hU
          (algebraMap k U.Completion r) = algebraMap k ℂ r := by
    intro r
    rw [IsScalarTower.algebraMap_apply k L U.Completion]
    exact NumberField.InfinitePlace.Completion.extensionEmbedding_coe U (algebraMap k L r)
  let e : U.Completion ≃ₐ[k] ℂ := AlgEquiv.ofRingEquiv hmap
  have htop : BrauerGroup.relative k ℂ = ⊤ := BrauerGroup.relative_eq_top_of_isAlgClosed ℂ
  exact eq_top_iff.mpr (htop ▸ relative_le_relative_of_algHom e.symm.toAlgHom)

/-! ### The Hasse principle -/

omit [NumberField k] in
/-- **A Brauer class of a number field is split by a finite extension exactly when it is split by
every completion of that extension.**  The complex places impose no condition, so only the finite
places and the real places of the extension appear. -/
theorem mem_relative_iff_forall_completion (x : BrauerGroup.{0, 0} k) :
    x ∈ BrauerGroup.relative k L ↔
      (∀ w : HeightOneSpectrum (𝓞 L), x ∈ BrauerGroup.relative k (w.adicCompletion L)) ∧
      (∀ U : InfinitePlace L, U.IsReal → x ∈ BrauerGroup.relative k U.Completion) := by
  refine ⟨fun hx => ⟨fun w => mem_relative_adicCompletion_of_mem_relative w hx,
    fun U _ => mem_relative_infiniteCompletion_of_mem_relative U hx⟩, fun hx => ?_⟩
  obtain ⟨hfin, hinf⟩ := hx
  rw [BrauerGroup.relative, MonoidHom.mem_ker]
  refine eq_one_of_forall_invariant_eq_one L (BrauerGroup.baseChangeHom L x)
    (fun w => ?_) fun U => ?_
  · rw [placeInvariant_eq_one_iff, BrauerGroup.relative, MonoidHom.mem_ker,
      ← MonoidHom.comp_apply, BrauerGroup.baseChangeHom_comp k L (w.adicCompletion L)]
    exact hfin w
  · rw [infinitePlaceInvariant_eq_one_iff, BrauerGroup.relative, MonoidHom.mem_ker,
      ← MonoidHom.comp_apply, BrauerGroup.baseChangeHom_comp k L U.Completion]
    rcases U.isReal_or_isComplex with hU | hU
    · exact hinf U hU
    · have hmem : x ∈ BrauerGroup.relative k U.Completion := by
        rw [relative_completion_eq_top_of_isComplex_extension (k := k) hU]
        exact Subgroup.mem_top x
      exact hmem

/-! ### Testing a finite place over the completion of the base -/

/-- **Splitting by a completion of the extension is a condition over the completion of the base.**
Base change along the base field, the completion of the base and the completion of the extension is
functorial, so the two ways of reading the base change of a class agree. -/
theorem mem_relative_adicCompletion_iff_baseChange (w : HeightOneSpectrum (𝓞 L))
    (x : BrauerGroup.{0, 0} k) :
    x ∈ BrauerGroup.relative k (w.adicCompletion L) ↔
      BrauerGroup.baseChangeHom ((primeUnder (𝓞 k) w).adicCompletion k) x ∈
        BrauerGroup.relative ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion L) := by
  rw [BrauerGroup.relative, BrauerGroup.relative, MonoidHom.mem_ker, MonoidHom.mem_ker,
    ← MonoidHom.comp_apply,
    BrauerGroup.baseChangeHom_comp k ((primeUnder (𝓞 k) w).adicCompletion k)
      (w.adicCompletion L)]

end RelativeHasse

end InverseGalois.CFT

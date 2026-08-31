/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.CompletionGalois

/-!
# The Galois group of a completion is a subgroup of the Galois group

Let `K / k` be a Galois extension of number fields and let `w` be a prime of `K`.  An automorphism
of the completion of `K` at `w` over the completion of `k` at the prime below carries `K` into
itself, and the resulting automorphism of `K` determines it, because `K` is dense in its completion
and an automorphism of a finite extension of a complete field is continuous.  Restriction is
therefore an injective group homomorphism from the Galois group of the completion to the Galois
group of the extension.

In particular the Galois group of the completion inherits any property of the Galois group of the
extension that passes to subgroups.  The one that matters here is being cyclic: **the completion of
a cyclic extension of number fields is a cyclic extension of the completion below**, which is what
turns local class field theory for cyclic extensions into a statement about a place of a global
cyclic extension.

## Main definitions

* `InverseGalois.CFT.restrictToBaseHom`: **restriction of an automorphism of the completion to the
  extension**, as a group homomorphism.

## Main results

* `InverseGalois.CFT.restrictToBase_injective`: an automorphism of the completion is determined by
  its restriction to the extension.
* `InverseGalois.CFT.isCyclic_algEquiv_adicCompletion`: **the completion of a cyclic extension of
  number fields is a cyclic extension of the completion below.**

## Tags

number field, completion, decomposition group, cyclic extension, local field
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

section CompletionCyclic

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (w : HeightOneSpectrum (𝓞 K))

variable (k) in
/-- **An automorphism of the completion is determined by its restriction to the extension.**  The
automorphism is continuous, the extension is dense in the completion, and the restriction records
its values there. -/
theorem restrictToBase_injective : Function.Injective (restrictToBase k w) := by
  intro τ₁ τ₂ h
  refine AlgEquiv.ext fun z => ?_
  refine UniformSpace.Completion.induction_on z
    (isClosed_eq (continuous_algEquiv k w τ₁) (continuous_algEquiv k w τ₂)) fun x => ?_
  calc τ₁ ((x : WithVal (w.valuation K)) : w.adicCompletion K)
      = toAdicCompletion w (restrictToBase k w τ₁ x) :=
        (toAdicCompletion_restrictToBase k w τ₁ x).symm
    _ = toAdicCompletion w (restrictToBase k w τ₂ x) := by rw [h]
    _ = τ₂ ((x : WithVal (w.valuation K)) : w.adicCompletion K) :=
        toAdicCompletion_restrictToBase k w τ₂ x

variable (k) in
/-- **Restriction of an automorphism of the completion to the extension**, as a group
homomorphism. -/
noncomputable def restrictToBaseHom :
    (w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K) →*
      Gal(K/k) where
  toFun := restrictToBase k w
  map_one' := by
    refine AlgEquiv.ext fun x => FaithfulSMul.algebraMap_injective K (w.adicCompletion K) ?_
    simp only [algebraMap_adicCompletion_eq, toAdicCompletion_restrictToBase, AlgEquiv.one_apply]
  map_mul' τ₁ τ₂ := by
    refine AlgEquiv.ext fun x => FaithfulSMul.algebraMap_injective K (w.adicCompletion K) ?_
    simp only [algebraMap_adicCompletion_eq, AlgEquiv.mul_apply, toAdicCompletion_restrictToBase]

variable (k) in
@[simp]
theorem restrictToBaseHom_apply
    (τ : w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K) :
    restrictToBaseHom k w τ = restrictToBase k w τ := rfl

variable (k) in
/-- **The completion of a cyclic extension of number fields is a cyclic extension of the completion
below.**  Restriction embeds its Galois group into the Galois group of the extension. -/
theorem isCyclic_algEquiv_adicCompletion [IsCyclic Gal(K/k)] :
    IsCyclic (w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k]
      w.adicCompletion K) :=
  isCyclic_of_injective (restrictToBaseHom k w) (restrictToBase_injective k w)

end CompletionCyclic

end InverseGalois.CFT

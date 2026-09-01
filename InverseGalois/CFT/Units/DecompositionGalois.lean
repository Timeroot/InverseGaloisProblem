/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.AdicHerbrand
import InverseGalois.CFT.Units.CompletionGalois

/-!
# The decomposition group is the Galois group of the completions

Let `K / k` be a Galois extension of number fields and let `w` be a prime of `K` lying over the
prime `v` of `k`.  The decomposition group at `w`, the stabilizer of `w` in the Galois group, acts
on the completion of `K` at `w` by automorphisms fixing the completion of `k` at `v`, and this
identifies it with the whole Galois group of the local extension.

Injectivity is faithfulness of the action, which holds because an automorphism of the completion is
determined by its restriction to the dense subfield.  Surjectivity is the statement that every
automorphism of the completion over the completion of the base restricts to an automorphism of the
extension fixing the prime, which holds because an automorphism of a finite extension is continuous
and therefore preserves the open unit ball.

## Main definitions

* `InverseGalois.CFT.decompositionAlgEquiv`: the automorphism of the completion attached to an
  element of the decomposition group.
* `InverseGalois.CFT.decompositionEquiv`: **the decomposition group at a prime is the Galois group
  of the completion over the completion of the prime below.**

## Main results

* `InverseGalois.CFT.card_stabilizer_eq_finrank_adicCompletion`: **the order of the decomposition
  group is the local degree.**

## Tags

number field, completion, decomposition group, Galois group, local degree
-/

namespace InverseGalois.CFT

open IsDedekindDomain Module MulAction NumberField

section Decomposition

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  (w : HeightOneSpectrum (𝓞 K))

variable (k) in
/-- **The automorphism of the completion attached to an element of the decomposition group**, as an
automorphism over the completion of the prime below. -/
noncomputable def decompositionAlgEquiv (σ : ↥(stabilizer Gal(K/k) w)) :
    w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K :=
  AlgEquiv.ofRingEquiv (f := adicCompletionAut w σ.1 (mem_stabilizer_iff.mp σ.2))
    (stabilizer_smul_algebraMap k w σ)

variable (k) in
@[simp]
theorem decompositionAlgEquiv_apply (σ : ↥(stabilizer Gal(K/k) w)) (z : w.adicCompletion K) :
    decompositionAlgEquiv k w σ z = σ • z := rfl

variable (k) in
/-- The decomposition group at a prime maps to the Galois group of the completion over the
completion of the prime below. -/
noncomputable def decompositionHom : ↥(stabilizer Gal(K/k) w) →*
    (w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K) where
  toFun := decompositionAlgEquiv k w
  map_one' := AlgEquiv.ext fun z => (one_smul (↥(stabilizer Gal(K/k) w)) z)
  map_mul' σ τ := AlgEquiv.ext fun z => mul_smul σ τ z

variable (k) in
@[simp]
theorem decompositionHom_apply (σ : ↥(stabilizer Gal(K/k) w)) (z : w.adicCompletion K) :
    decompositionHom k w σ z = σ • z := rfl

variable (k) in
/-- An element of the decomposition group is determined by its action on the completion, the
extension being dense in it. -/
theorem decompositionHom_injective : Function.Injective (decompositionHom k w) := by
  intro σ τ h
  have hz : ∀ z : w.adicCompletion K, σ • z = τ • z := fun z => by
    simpa using DFunLike.congr_fun h z
  exact eq_of_smul_eq_smul hz

variable (k) [IsGalois k K] in
/-- **Every automorphism of the completion over the completion of the prime below comes from the
decomposition group.** -/
theorem decompositionHom_surjective : Function.Surjective (decompositionHom k w) := fun τ =>
  ⟨⟨restrictToBase k w τ, restrictToBase_mem_stabilizer k w τ⟩,
    AlgEquiv.ext (adicCompletionAut_restrictToBase k w τ)⟩

variable (k) [IsGalois k K] in
/-- **The decomposition group at a prime is the Galois group of the completion over the completion
of the prime below.** -/
noncomputable def decompositionEquiv : ↥(stabilizer Gal(K/k) w) ≃*
    (w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K) :=
  MulEquiv.ofBijective (decompositionHom k w)
    ⟨decompositionHom_injective k w, decompositionHom_surjective k w⟩

variable (k) [IsGalois k K] in
@[simp]
theorem decompositionEquiv_apply (σ : ↥(stabilizer Gal(K/k) w)) (z : w.adicCompletion K) :
    decompositionEquiv k w σ z = σ • z := rfl

variable (k) [IsGalois k K] in
/-- **The order of the decomposition group at a prime is the local degree.** -/
theorem card_stabilizer_eq_finrank_adicCompletion :
    Nat.card ↥(stabilizer Gal(K/k) w)
      = finrank ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K) := by
  haveI := isGalois_adicCompletion k w
  rw [Nat.card_congr (decompositionEquiv k w).toEquiv, IsGalois.card_aut_eq_finrank]

end Decomposition

end InverseGalois.CFT

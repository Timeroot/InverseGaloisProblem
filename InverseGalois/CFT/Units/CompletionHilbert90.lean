/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.CompletionGalois

/-!
# Hilbert's theorem 90 for the decomposition group at a finite place

The completion of a Galois extension of number fields at a prime is a finite extension of the
completion of the base at the prime below, and every automorphism of it over the completion of the
base is induced by an element of the decomposition group at that prime.  The decomposition group is
therefore the automorphism group of the completion, and Hilbert's theorem 90 for a finite extension
of fields reads as a statement about the decomposition group: a one-cocycle with values in the
units of the completion is the coboundary of a single unit.

The same holds for an arbitrary subgroup of the decomposition group, which is the automorphism
group of the completion over the subfield it fixes, again a finite extension.

## Main definitions

* `InverseGalois.CFT.stabilizerToAlgEquiv`: the automorphism of the completion attached to an
  element of the decomposition group.
* `InverseGalois.CFT.stabilizerAlgEquiv`: **the decomposition group at a prime is the automorphism
  group of the completion there.**

## Main results

* `InverseGalois.CFT.isMulCoboundary₁_of_isMulCocycle₁_stabilizer`: **Hilbert's theorem 90 for a
  subgroup of the decomposition group at a finite place.**

## Tags

number field, completion, decomposition group, Hilbert's theorem 90, Galois cohomology
-/

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1000000

open IsDedekindDomain MulAction NumberField groupCohomology

namespace InverseGalois.CFT

/-! ### The decomposition group as an automorphism group -/

section Stabilizer

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (w : HeightOneSpectrum (𝓞 K))

variable (k) in
/-- **The automorphism of the completion attached to an element of the decomposition group.** -/
noncomputable def stabilizerToAlgEquiv (σ : ↥(stabilizer Gal(K/k) w)) :
    w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K :=
  AlgEquiv.ofRingEquiv (f := adicCompletionAut w σ.1 (mem_stabilizer_iff.mp σ.2))
    (stabilizer_smul_algebraMap k w σ)

variable (k) in
omit [IsGalois k K] in
@[simp]
theorem stabilizerToAlgEquiv_apply (σ : ↥(stabilizer Gal(K/k) w)) (z : w.adicCompletion K) :
    stabilizerToAlgEquiv k w σ z = σ • z := rfl

variable (k) in
/-- **The decomposition group at a prime is the automorphism group of the completion there.**
Every element of the decomposition group extends to the completion, and every automorphism of the
completion over the completion of the base preserves the field, hence restricts to an automorphism
of it fixing the prime. -/
noncomputable def stabilizerAlgEquiv : ↥(stabilizer Gal(K/k) w) ≃*
    (w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K) where
  toFun := stabilizerToAlgEquiv k w
  invFun τ := ⟨restrictToBase k w τ, restrictToBase_mem_stabilizer k w τ⟩
  left_inv σ := by
    refine Subtype.ext (AlgEquiv.ext fun x => ?_)
    refine (toAdicCompletion w).injective ?_
    rw [toAdicCompletion_restrictToBase k w (stabilizerToAlgEquiv k w σ) x,
      stabilizerToAlgEquiv_apply, stabilizer_smul_adicCompletion_def, toAdicCompletion_apply,
      adicCompletionAut_coe]
    rfl
  right_inv τ := AlgEquiv.ext fun z => adicCompletionAut_restrictToBase k w τ z
  map_mul' σ τ := AlgEquiv.ext fun z => mul_smul σ τ z

variable (k) in
@[simp]
theorem stabilizerAlgEquiv_apply (σ : ↥(stabilizer Gal(K/k) w)) (z : w.adicCompletion K) :
    stabilizerAlgEquiv k w σ z = σ • z := rfl

end Stabilizer

/-! ### Hilbert's theorem 90 -/

section Hilbert90

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (w : HeightOneSpectrum (𝓞 K))

/-- **The decomposition group at a prime acts on the units of the completion there.** -/
noncomputable instance instMulDistribMulActionStabilizerUnits :
    MulDistribMulAction ↥(stabilizer Gal(K/k) w) (w.adicCompletion K)ˣ :=
  Units.mulDistribMulActionRight

variable (k) in
omit [NumberField k] [IsGalois k K] in
@[simp]
theorem val_stabilizer_smul_units (σ : ↥(stabilizer Gal(K/k) w)) (u : (w.adicCompletion K)ˣ) :
    ((σ • u : (w.adicCompletion K)ˣ) : w.adicCompletion K) = σ • (u : w.adicCompletion K) := rfl

variable (k) in
/-- **Hilbert's theorem 90 for a subgroup of the decomposition group at a finite place.**  The
subgroup is the automorphism group of the completion over the subfield it fixes, and the completion
is a finite extension of that subfield. -/
theorem isMulCoboundary₁_of_isMulCocycle₁_stabilizer (S : Subgroup ↥(stabilizer Gal(K/k) w))
    (e : ↥S → (w.adicCompletion K)ˣ) (he : IsMulCocycle₁ e) : IsMulCoboundary₁ e := by
  set Φ := stabilizerAlgEquiv k w with hΦ
  set S' : Subgroup (w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k]
    w.adicCompletion K) := S.map Φ.toMonoidHom with hS'
  set F := IntermediateField.fixedField S' with hF
  haveI : FiniteDimensional ↥F (w.adicCompletion K) :=
    FiniteDimensional.right ((primeUnder (𝓞 k) w).adicCompletion k) ↥F (w.adicCompletion K)
  set Ψ : ↥S ≃* Gal(w.adicCompletion K/↥F) :=
    (S.equivMapOfInjective Φ.toMonoidHom Φ.injective).trans
      (IntermediateField.subgroupEquivAlgEquiv S') with hΨdef
  have hΨ : ∀ (σ : ↥S) (z : w.adicCompletion K),
      Ψ σ z = ((σ : ↥(stabilizer Gal(K/k) w))) • z := fun _ _ => rfl
  have hsmul : ∀ (σ : ↥S) (u : (w.adicCompletion K)ˣ), Ψ σ • u = σ • u := by
    intro σ u
    exact Units.ext (hΨ σ (u : w.adicCompletion K))
  have hsymm : ∀ (g : Gal(w.adicCompletion K/↥F)) (u : (w.adicCompletion K)ˣ),
      (Ψ.symm g) • u = g • u := by
    intro g u
    conv_rhs => rw [← Ψ.apply_symm_apply g]
    exact (hsmul (Ψ.symm g) u).symm
  have hcoc : IsMulCocycle₁ (fun g : Gal(w.adicCompletion K/↥F) => e (Ψ.symm g)) := by
    intro g h
    show e (Ψ.symm (g * h)) = g • e (Ψ.symm h) * e (Ψ.symm g)
    rw [map_mul, he, hsymm]
  obtain ⟨α, hα⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units _ hcoc
  refine ⟨α, fun σ => ?_⟩
  have h : Ψ σ • α / α = e (Ψ.symm (Ψ σ)) := hα (Ψ σ)
  rwa [Ψ.symm_apply_apply, hsmul] at h

end Hilbert90

end InverseGalois.CFT

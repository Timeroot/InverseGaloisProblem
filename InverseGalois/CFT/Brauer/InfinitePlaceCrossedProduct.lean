/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.CrossedProductCompositum
import InverseGalois.CFT.Brauer.CrossedProductRestrict
import InverseGalois.CFT.Brauer.Kernel
import InverseGalois.CFT.Units.InfiniteDecompositionField
import InverseGalois.CFT.Units.InfiniteTowerDescent

/-!
# Localising a crossed product at an infinite place

Let `K / k` be a Galois extension of number fields, let `f` be a multiplicative `2`-cocycle of
`Gal(K/k)` with values in `Kˣ`, and let `w` be an infinite place of `K` lying over the place `u` of
`k`.  Extending scalars from `k` to the completion at `u` turns the crossed product of `f` into the
crossed product of the cocycle obtained from `f` by restricting to the decomposition group and
reading the result on the automorphism group of the completions.

The passage is in two steps, through the decomposition field, exactly as at a finite place:
restricting `f` to the automorphisms fixing the decomposition field computes base change to that
field, and the decomposition field is the subfield over which the decomposition group becomes the
whole Galois group, so base change from it to the completion at `u` is transport of the cocycle
along the identification of the two groups.

Consequently the completion at `u` splits the class of the crossed product exactly when the local
cocycle is a coboundary in the units of the completion at `w`, which is the form in which the
archimedean hypotheses of the Albert-Brauer-Hasse-Noether theorem are stated.

## Main definitions

* `InverseGalois.CFT.localInfiniteCocycle`: **the cocycle of the local extension at an infinite
  place attached to a cocycle of the global one.**

## Main results

* `InverseGalois.CFT.baseChangeHom_mk_csa_infiniteCompletion`: **extending scalars to the
  completion at an infinite place sends the class of a crossed product to the class of the local
  crossed product.**
* `InverseGalois.CFT.mem_relative_mk_csa_infiniteCompletion_iff_exists`: **the completion at an
  infinite place splits the class of a crossed product exactly when the cocycle restricted to the
  decomposition group is a coboundary in the units of the completion.**

## Tags

crossed product, Brauer group, infinite place, completion, decomposition field,
Albert-Brauer-Hasse-Noether, class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open groupCohomology

namespace InverseGalois.CFT

open MulAction NumberField

section LocalInfiniteCocycle

attribute [local instance] isGalois_infiniteCompletion

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (w : InfinitePlace K)

variable (k) in
/-- **The cocycle of the local extension at an infinite place attached to a cocycle of the global
one**: restrict the cocycle to the decomposition group and read the result on the automorphism
group of the completions. -/
noncomputable def localInfiniteCocycle (f : Gal(K/k) × Gal(K/k) → Kˣ) :
    (w.Completion ≃ₐ[(w.comap (algebraMap k K)).Completion] w.Completion) ×
        (w.Completion ≃ₐ[(w.comap (algebraMap k K)).Completion] w.Completion) →
      w.Completionˣ :=
  CrossedProduct.compositumCocycle (localInfiniteDecompositionEquiv k w)
    (CrossedProduct.restrictCocycle ↥(infiniteDecompositionField k w) f)

variable (k) in
/-- The local cocycle of a multiplicative `2`-cocycle is a multiplicative `2`-cocycle. -/
theorem isMulCocycle₂_localInfiniteCocycle {f : Gal(K/k) × Gal(K/k) → Kˣ} (hf : IsMulCocycle₂ f) :
    IsMulCocycle₂ (localInfiniteCocycle k w f) :=
  CrossedProduct.isMulCocycle₂_compositumCocycle (algebraMap_localInfiniteDecompositionEquiv k w)
    (CrossedProduct.isMulCocycle₂_restrictCocycle _ hf)

variable (k) in
/-- **Extending scalars to the completion at an infinite place sends the class of a crossed product
to the class of the local crossed product.** -/
theorem baseChangeHom_mk_csa_infiniteCompletion {f : Gal(K/k) × Gal(K/k) → Kˣ}
    (hf : IsMulCocycle₂ f) :
    BrauerGroup.baseChangeHom (w.comap (algebraMap k K)).Completion
        (⟦CrossedProduct.csa hf⟧ : BrauerGroup k)
      = (⟦CrossedProduct.csa (isMulCocycle₂_localInfiniteCocycle k w hf)⟧ :
          BrauerGroup (w.comap (algebraMap k K)).Completion) := by
  rw [← BrauerGroup.baseChangeHom_comp k ↥(infiniteDecompositionField k w)
      (w.comap (algebraMap k K)).Completion, MonoidHom.coe_comp, Function.comp_apply,
    CrossedProduct.baseChangeHom_mk_csa ↥(infiniteDecompositionField k w) hf
      (CrossedProduct.isMulCocycle₂_restrictCocycle _ hf)]
  exact CrossedProduct.baseChangeHom_mk_csa_compositum _ _
    (algebraMap_localInfiniteDecompositionEquiv k w)

variable (k) in
/-- **The completion at an infinite place splits the class of a crossed product exactly when the
local cocycle is a coboundary.** -/
theorem mem_relative_mk_csa_infiniteCompletion_iff {f : Gal(K/k) × Gal(K/k) → Kˣ}
    (hf : IsMulCocycle₂ f) :
    (⟦CrossedProduct.csa hf⟧ : BrauerGroup k)
        ∈ BrauerGroup.relative k (w.comap (algebraMap k K)).Completion
      ↔ IsMulCoboundary₂ (localInfiniteCocycle k w f) := by
  rw [BrauerGroup.relative, MonoidHom.mem_ker, baseChangeHom_mk_csa_infiniteCompletion k w hf,
    CrossedProduct.mk_csa_eq_one_iff]

/-! ### The coboundary condition, read on the decomposition group -/

variable (k) in
omit [IsGalois k K] in
/-- An automorphism of the extension over the decomposition field induces on the base field the
automorphism of the decomposition group it came from. -/
theorem restrictScalars_infiniteDecompositionFieldEquiv (s : ↥(stabilizer Gal(K/k) w)) :
    (infiniteDecompositionFieldEquiv k w s).restrictScalars k = (s : Gal(K/k)) :=
  AlgEquiv.ext fun _ => rfl

variable (k) in
/-- The two identifications of the decomposition group, with the automorphism group of the
completions and with the Galois group over the decomposition field, agree. -/
theorem localInfiniteDecompositionEquiv_stabilizerAlgEquivInfinite
    (s : ↥(stabilizer Gal(K/k) w)) :
    localInfiniteDecompositionEquiv k w (stabilizerAlgEquivInfinite k w s)
      = infiniteDecompositionFieldEquiv k w s := by
  rw [localInfiniteDecompositionEquiv, MulEquiv.coe_trans, Function.comp_apply,
    MulEquiv.symm_apply_apply]

variable (k) in
/-- The local cocycle is the original cocycle, read on the automorphisms of the extension over the
decomposition field and pushed into the units of the completion. -/
theorem localInfiniteCocycle_apply (f : Gal(K/k) × Gal(K/k) → Kˣ)
    (σ τ : w.Completion ≃ₐ[(w.comap (algebraMap k K)).Completion] w.Completion) :
    localInfiniteCocycle k w f (σ, τ)
      = infiniteUnitHom w (f ((localInfiniteDecompositionEquiv k w σ).restrictScalars k,
          (localInfiniteDecompositionEquiv k w τ).restrictScalars k)) := rfl

variable (k) in
/-- **The local cocycle, read on the decomposition group, is the original cocycle pushed into the
units of the completion.** -/
theorem localInfiniteCocycle_stabilizerAlgEquivInfinite (f : Gal(K/k) × Gal(K/k) → Kˣ)
    (s t : ↥(stabilizer Gal(K/k) w)) :
    localInfiniteCocycle k w f
        (stabilizerAlgEquivInfinite k w s, stabilizerAlgEquivInfinite k w t)
      = infiniteUnitHom w (f (s.1, t.1)) := by
  rw [localInfiniteCocycle_apply, localInfiniteDecompositionEquiv_stabilizerAlgEquivInfinite,
    localInfiniteDecompositionEquiv_stabilizerAlgEquivInfinite,
    restrictScalars_infiniteDecompositionFieldEquiv,
    restrictScalars_infiniteDecompositionFieldEquiv]

variable (k) in
/-- The action of the automorphism group of the completion on its units is the action of the
decomposition group. -/
theorem smul_units_stabilizerAlgEquivInfinite (s : ↥(stabilizer Gal(K/k) w))
    (u : w.Completionˣ) : stabilizerAlgEquivInfinite k w s • u = s • u :=
  Units.ext (stabilizerAlgEquivInfinite_apply k w s (u : w.Completion))

variable (k) in
/-- **The local cocycle at an infinite place is a coboundary exactly when the cocycle restricted to
the decomposition group is a coboundary in the units of the completion.** -/
theorem isMulCoboundary₂_localInfiniteCocycle_iff (f : Gal(K/k) × Gal(K/k) → Kˣ) :
    IsMulCoboundary₂ (localInfiniteCocycle k w f) ↔
      ∃ c : ↥(stabilizer Gal(K/k) w) → Additive w.Completionˣ,
        ∀ s t : ↥(stabilizer Gal(K/k) w),
          Additive.ofMul (infiniteUnitHom w (f (s.1, t.1)))
            = smulUnitsAut s (c t) - c (s * t) + c s := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun s => Additive.ofMul (x (stabilizerAlgEquivInfinite k w s)), fun s t => ?_⟩
    have h := hx (stabilizerAlgEquivInfinite k w s) (stabilizerAlgEquivInfinite k w t)
    rw [localInfiniteCocycle_stabilizerAlgEquivInfinite,
      ← map_mul (stabilizerAlgEquivInfinite k w) s t] at h
    refine Additive.toMul.injective ?_
    rw [toMul_ofMul, toMul_add, toMul_sub, toMul_smulUnitsAut_stabilizerInfinite, toMul_ofMul,
      toMul_ofMul, toMul_ofMul, ← smul_units_stabilizerAlgEquivInfinite]
    exact h.symm
  · rintro ⟨c, hc⟩
    refine ⟨fun σ => Additive.toMul (c ((stabilizerAlgEquivInfinite k w).symm σ)), fun σ τ => ?_⟩
    obtain ⟨s, rfl⟩ := (stabilizerAlgEquivInfinite k w).surjective σ
    obtain ⟨t, rfl⟩ := (stabilizerAlgEquivInfinite k w).surjective τ
    rw [localInfiniteCocycle_stabilizerAlgEquivInfinite,
      ← map_mul (stabilizerAlgEquivInfinite k w) s t]
    simp only [MulEquiv.symm_apply_apply]
    have h := congrArg Additive.toMul (hc s t)
    rw [toMul_ofMul, toMul_add, toMul_sub, toMul_smulUnitsAut_stabilizerInfinite] at h
    rw [smul_units_stabilizerAlgEquivInfinite]
    exact h.symm

variable (k) in
/-- **The completion at an infinite place splits the class of a crossed product exactly when the
cocycle restricted to the decomposition group is a coboundary in the units of the completion**,
which is the form taken by the archimedean hypotheses of the Albert-Brauer-Hasse-Noether
theorem. -/
theorem mem_relative_mk_csa_infiniteCompletion_iff_exists {f : Gal(K/k) × Gal(K/k) → Kˣ}
    (hf : IsMulCocycle₂ f) :
    (⟦CrossedProduct.csa hf⟧ : BrauerGroup k)
        ∈ BrauerGroup.relative k (w.comap (algebraMap k K)).Completion
      ↔ ∃ c : ↥(stabilizer Gal(K/k) w) → Additive w.Completionˣ,
        ∀ s t : ↥(stabilizer Gal(K/k) w),
          Additive.ofMul (infiniteUnitHom w (f (s.1, t.1)))
            = smulUnitsAut s (c t) - c (s * t) + c s :=
  (mem_relative_mk_csa_infiniteCompletion_iff k w hf).trans
    (isMulCoboundary₂_localInfiniteCocycle_iff k w f)

end LocalInfiniteCocycle

end InverseGalois.CFT

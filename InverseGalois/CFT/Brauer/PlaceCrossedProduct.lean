/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.CrossedProductCompositum
import InverseGalois.CFT.Brauer.CrossedProductRestrict
import InverseGalois.CFT.Brauer.Kernel
import InverseGalois.CFT.Brauer.PlaceInvariant
import InverseGalois.CFT.Units.DecompositionField

/-!
# Localising a crossed product at a finite place

Let `K / k` be a Galois extension of number fields, let `f` be a multiplicative `2`-cocycle of
`Gal(K/k)` with values in `Kˣ`, and let `w` be a prime of `K` lying over the prime `v` of `k`.
Extending scalars from `k` to the completion at `v` turns the crossed product of `f` into the
crossed product of the cocycle obtained from `f` by restricting to the decomposition group and
reading the result on the Galois group of the completions.

The passage is in two steps, through the decomposition field `F`.  Restricting `f` to `Gal(K/F)`
computes base change from `k` to `F`, because the crossed product of the restriction is the
centralizer of the copy of `F`.  And `F` is exactly the subfield over which the decomposition
group becomes the whole Galois group, so the completion at `v` and the extension `K` are linearly
disjoint over `F` and generate the completion at `w`; base change from `F` to the completion at
`v` is then transport of the cocycle along the identification of `Gal(K_w/k_v)` with `Gal(K/F)`.

Consequently the invariant at `v` of the class of the crossed product vanishes exactly when the
local cocycle is a coboundary in the units of the completion at `w`, which is the form in which
the local hypotheses of the Albert-Brauer-Hasse-Noether theorem are stated.

## Main definitions

* `InverseGalois.CFT.localCocycle`: **the cocycle of the local extension attached to a cocycle of
  the global one.**

## Main results

* `InverseGalois.CFT.baseChangeHom_mk_csa_adicCompletion`: **extending scalars to the completion
  sends the class of a crossed product to the class of the local crossed product.**
* `InverseGalois.CFT.placeInvariant_mk_csa_eq_one_iff`: **the invariant at a finite place of the
  class of a crossed product vanishes exactly when the local cocycle is a coboundary.**

## Tags

crossed product, Brauer group, completion, decomposition field, invariant, class field theory
-/

set_option synthInstance.maxHeartbeats 1000000

open groupCohomology

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

section LocalCocycle

attribute [local instance] isGalois_adicCompletion

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (w : HeightOneSpectrum (𝓞 K))

variable (k) in
/-- **The cocycle of the local extension attached to a cocycle of the global one**: restrict the
cocycle to the decomposition group and read the result on the Galois group of the completions. -/
noncomputable def localCocycle (f : Gal(K/k) × Gal(K/k) → Kˣ) :
    (w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K) ×
        (w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K) →
      (w.adicCompletion K)ˣ :=
  CrossedProduct.compositumCocycle (localDecompositionEquiv k w)
    (CrossedProduct.restrictCocycle ↥(decompositionField k w) f)

variable (k) in
/-- The local cocycle of a multiplicative `2`-cocycle is a multiplicative `2`-cocycle. -/
theorem isMulCocycle₂_localCocycle {f : Gal(K/k) × Gal(K/k) → Kˣ} (hf : IsMulCocycle₂ f) :
    IsMulCocycle₂ (localCocycle k w f) :=
  CrossedProduct.isMulCocycle₂_compositumCocycle (algebraMap_localDecompositionEquiv k w)
    (CrossedProduct.isMulCocycle₂_restrictCocycle _ hf)

variable (k) in
/-- **Extending scalars to the completion at a finite place sends the class of a crossed product
to the class of the local crossed product.** -/
theorem baseChangeHom_mk_csa_adicCompletion {f : Gal(K/k) × Gal(K/k) → Kˣ}
    (hf : IsMulCocycle₂ f) :
    BrauerGroup.baseChangeHom ((primeUnder (𝓞 k) w).adicCompletion k)
        (⟦CrossedProduct.csa hf⟧ : BrauerGroup k)
      = (⟦CrossedProduct.csa (isMulCocycle₂_localCocycle k w hf)⟧ :
          BrauerGroup ((primeUnder (𝓞 k) w).adicCompletion k)) := by
  rw [← BrauerGroup.baseChangeHom_comp k ↥(decompositionField k w)
      ((primeUnder (𝓞 k) w).adicCompletion k), MonoidHom.coe_comp, Function.comp_apply,
    CrossedProduct.baseChangeHom_mk_csa ↥(decompositionField k w) hf
      (CrossedProduct.isMulCocycle₂_restrictCocycle _ hf)]
  exact CrossedProduct.baseChangeHom_mk_csa_compositum _ _
    (algebraMap_localDecompositionEquiv k w)

variable (k) in
/-- **The invariant at a finite place of the class of a crossed product vanishes exactly when the
local cocycle is a coboundary.** -/
theorem placeInvariant_mk_csa_eq_one_iff {f : Gal(K/k) × Gal(K/k) → Kˣ} (hf : IsMulCocycle₂ f) :
    placeInvariant k (primeUnder (𝓞 k) w) (⟦CrossedProduct.csa hf⟧ : BrauerGroup k) = 1
      ↔ IsMulCoboundary₂ (localCocycle k w f) := by
  rw [placeInvariant_eq_one_iff, BrauerGroup.relative, MonoidHom.mem_ker,
    baseChangeHom_mk_csa_adicCompletion k w hf, CrossedProduct.mk_csa_eq_one_iff]

end LocalCocycle

end InverseGalois.CFT

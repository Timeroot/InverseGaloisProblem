/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.PlaceCrossedProduct
import InverseGalois.CFT.Units.TowerDescent

/-!
# The local coboundary condition at a finite place, read on the decomposition group

The cocycle of the completions attached to a cocycle of a Galois extension of number fields is a
coboundary exactly when the original cocycle, restricted to the decomposition group and pushed into
the units of the completion, is a coboundary there.  The two statements differ only in the way they
are written: one indexes by the Galois group of the completions, the other by the decomposition
group, and the identification of the two is the isomorphism of the decomposition group with the
Galois group of the completions.

Combining this with the description of the invariant at a finite place of the class of a crossed
product gives that invariant in the exact shape in which the local hypotheses of the
Albert-Brauer-Hasse-Noether theorem are stated.

## Main results

* `InverseGalois.CFT.isMulCoboundary₂_localCocycle_iff`: **the local cocycle is a coboundary
  exactly when the cocycle restricted to the decomposition group is a coboundary in the units of
  the completion.**
* `InverseGalois.CFT.placeInvariant_mk_csa_eq_one_iff_exists`: **the invariant at a finite place of
  the class of a crossed product vanishes exactly when the cocycle restricted to the decomposition
  group is a coboundary in the units of the completion.**
* `InverseGalois.CFT.mem_relative_mk_csa_adicCompletion_iff_exists`: the same criterion, phrased as
  the completion at the place splitting the class.

## Tags

crossed product, Brauer group, completion, decomposition group, coboundary, invariant,
Albert-Brauer-Hasse-Noether, class field theory
-/

set_option synthInstance.maxHeartbeats 1000000

open groupCohomology

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

section PlaceCoboundary

attribute [local instance] isGalois_adicCompletion

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (w : HeightOneSpectrum (𝓞 K))

variable (k) in
omit [IsGalois k K] in
/-- An automorphism of the extension over the decomposition field induces on the base field the
automorphism of the decomposition group it came from. -/
theorem restrictScalars_decompositionFieldEquiv (s : ↥(stabilizer Gal(K/k) w)) :
    (decompositionFieldEquiv k w s).restrictScalars k = (s : Gal(K/k)) :=
  AlgEquiv.ext fun _ => rfl

variable (k) in
/-- The two identifications of the decomposition group, with the Galois group of the completions
and with the Galois group over the decomposition field, agree. -/
theorem localDecompositionEquiv_decompositionEquiv (s : ↥(stabilizer Gal(K/k) w)) :
    localDecompositionEquiv k w (decompositionEquiv k w s) = decompositionFieldEquiv k w s := by
  rw [localDecompositionEquiv, MulEquiv.coe_trans, Function.comp_apply,
    MulEquiv.symm_apply_apply]

variable (k) in
/-- The local cocycle is the original cocycle, read on the automorphisms of the extension over the
decomposition field and pushed into the units of the completion. -/
theorem localCocycle_apply (f : Gal(K/k) × Gal(K/k) → Kˣ)
    (σ τ : w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K) :
    localCocycle k w f (σ, τ)
      = adicUnitHom w (f ((localDecompositionEquiv k w σ).restrictScalars k,
          (localDecompositionEquiv k w τ).restrictScalars k)) := rfl

variable (k) in
/-- **The local cocycle, read on the decomposition group, is the original cocycle pushed into the
units of the completion.** -/
theorem localCocycle_decompositionEquiv (f : Gal(K/k) × Gal(K/k) → Kˣ)
    (s t : ↥(stabilizer Gal(K/k) w)) :
    localCocycle k w f (decompositionEquiv k w s, decompositionEquiv k w t)
      = adicUnitHom w (f (s.1, t.1)) := by
  rw [localCocycle_apply, localDecompositionEquiv_decompositionEquiv,
    localDecompositionEquiv_decompositionEquiv, restrictScalars_decompositionFieldEquiv,
    restrictScalars_decompositionFieldEquiv]

variable (k) in
/-- The action of the Galois group of the completions on the units of the completion is the action
of the decomposition group. -/
theorem smul_units_decompositionEquiv (s : ↥(stabilizer Gal(K/k) w))
    (u : (w.adicCompletion K)ˣ) : decompositionEquiv k w s • u = s • u :=
  Units.ext (decompositionEquiv_apply k w s (u : w.adicCompletion K))

variable (k) in
/-- **The local cocycle is a coboundary exactly when the cocycle restricted to the decomposition
group is a coboundary in the units of the completion.** -/
theorem isMulCoboundary₂_localCocycle_iff (f : Gal(K/k) × Gal(K/k) → Kˣ) :
    IsMulCoboundary₂ (localCocycle k w f) ↔
      ∃ c : ↥(stabilizer Gal(K/k) w) → Additive (w.adicCompletion K)ˣ,
        ∀ s t : ↥(stabilizer Gal(K/k) w),
          Additive.ofMul (adicUnitHom w (f (s.1, t.1)))
            = smulUnitsAut s (c t) - c (s * t) + c s := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun s => Additive.ofMul (x (decompositionEquiv k w s)), fun s t => ?_⟩
    have h := hx (decompositionEquiv k w s) (decompositionEquiv k w t)
    rw [localCocycle_decompositionEquiv, ← map_mul (decompositionEquiv k w) s t] at h
    refine Additive.toMul.injective ?_
    rw [toMul_ofMul, toMul_add, toMul_sub, toMul_smulUnitsAut_stabilizer, toMul_ofMul, toMul_ofMul,
      toMul_ofMul, ← smul_units_decompositionEquiv]
    exact h.symm
  · rintro ⟨c, hc⟩
    refine ⟨fun σ => Additive.toMul (c ((decompositionEquiv k w).symm σ)), fun σ τ => ?_⟩
    obtain ⟨s, rfl⟩ := (decompositionEquiv k w).surjective σ
    obtain ⟨t, rfl⟩ := (decompositionEquiv k w).surjective τ
    rw [localCocycle_decompositionEquiv, ← map_mul (decompositionEquiv k w) s t]
    simp only [MulEquiv.symm_apply_apply]
    have h := congrArg Additive.toMul (hc s t)
    rw [toMul_ofMul, toMul_add, toMul_sub, toMul_smulUnitsAut_stabilizer] at h
    rw [smul_units_decompositionEquiv]
    exact h.symm

variable (k) in
/-- **The invariant at a finite place of the class of a crossed product vanishes exactly when the
cocycle restricted to the decomposition group is a coboundary in the units of the completion**,
which is the form taken by the local hypotheses of the Albert-Brauer-Hasse-Noether theorem. -/
theorem placeInvariant_mk_csa_eq_one_iff_exists {f : Gal(K/k) × Gal(K/k) → Kˣ}
    (hf : IsMulCocycle₂ f) :
    placeInvariant k (primeUnder (𝓞 k) w) (⟦CrossedProduct.csa hf⟧ : BrauerGroup k) = 1
      ↔ ∃ c : ↥(stabilizer Gal(K/k) w) → Additive (w.adicCompletion K)ˣ,
        ∀ s t : ↥(stabilizer Gal(K/k) w),
          Additive.ofMul (adicUnitHom w (f (s.1, t.1)))
            = smulUnitsAut s (c t) - c (s * t) + c s :=
  (placeInvariant_mk_csa_eq_one_iff k w hf).trans (isMulCoboundary₂_localCocycle_iff k w f)

variable (k) in
/-- **The completion at a finite place splits the class of a crossed product exactly when the
cocycle restricted to the decomposition group is a coboundary in the units of the completion**,
which is the form taken by the local hypotheses of the Albert-Brauer-Hasse-Noether theorem. -/
theorem mem_relative_mk_csa_adicCompletion_iff_exists {f : Gal(K/k) × Gal(K/k) → Kˣ}
    (hf : IsMulCocycle₂ f) :
    (⟦CrossedProduct.csa hf⟧ : BrauerGroup k)
        ∈ BrauerGroup.relative k ((primeUnder (𝓞 k) w).adicCompletion k)
      ↔ ∃ c : ↥(stabilizer Gal(K/k) w) → Additive (w.adicCompletion K)ˣ,
        ∀ s t : ↥(stabilizer Gal(K/k) w),
          Additive.ofMul (adicUnitHom w (f (s.1, t.1)))
            = smulUnitsAut s (c t) - c (s * t) + c s := by
  rw [BrauerGroup.relative, MonoidHom.mem_ker, baseChangeHom_mk_csa_adicCompletion k w hf,
    CrossedProduct.mk_csa_eq_one_iff]
  exact isMulCoboundary₂_localCocycle_iff k w f

end PlaceCoboundary

end InverseGalois.CFT

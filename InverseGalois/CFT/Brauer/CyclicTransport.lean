/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.CyclicTower

/-!
# Transporting a cyclic algebra along an isomorphism of splitting fields

A cyclic algebra is built from a cyclic Galois extension of the base, a chosen generator of its
Galois group and a scalar.  An isomorphism of two such extensions over the base which carries one
chosen generator to the other carries one cyclic algebra to the other, so the two have the same
Brauer class.

The proof is the recognition criterion for cyclic algebras: the cyclic algebra of the first
extension contains a copy of the second extension, obtained by composing the tautological copy of
the first with the inverse of the isomorphism, and the unit which conjugates the first copy by its
generator conjugates the second copy by its generator, because the isomorphism intertwines the two.
The dimension count is unchanged because isomorphic extensions have the same degree.

## Main results

* `InverseGalois.CFT.cyclicBrauerHom_congr`: **the Brauer class of a cyclic algebra is unchanged by
  an isomorphism of splitting fields carrying one chosen generator to the other.**

## Tags

Brauer group, cyclic algebra, crossed product, splitting field, transport
-/

namespace InverseGalois.CFT

open Module

/-! ### Transport along an isomorphism -/

section Transport

variable {K L L' : Type u} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']
  [FiniteDimensional K L] [FiniteDimensional K L'] [IsGalois K L] [IsGalois K L']

/-- **The Brauer class of a cyclic algebra is unchanged by an isomorphism of splitting fields
carrying one chosen generator to the other.**  The cyclic algebra of the first extension already
contains a copy of the second, and the unit implementing the first generator implements the second
one through the isomorphism. -/
theorem cyclicBrauerHom_congr {σ₀ : Gal(L/K)} {σ₀' : Gal(L'/K)}
    (hσ₀ : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers σ₀)
    (hσ₀' : ∀ x : Gal(L'/K), x ∈ Subgroup.zpowers σ₀') (φ : L ≃ₐ[K] L')
    (hφ : ∀ x : L, φ (σ₀ x) = σ₀' (φ x)) (a : Kˣ) :
    cyclicBrauerHom hσ₀' a = cyclicBrauerHom hσ₀ a := by
  have hrank : finrank K L = finrank K L' := φ.toLinearEquiv.finrank_eq
  rcases Nat.lt_or_ge (finrank K L) 2 with h1 | h2
  · have he : finrank K L = 1 := by
      have := Module.finrank_pos (R := K) (M := L)
      omega
    have hA : cyclicBrauerHom hσ₀ a = 1 := by
      have h := cyclicBrauerHom_pow_finrank hσ₀ a
      rwa [he, pow_one] at h
    have hB : cyclicBrauerHom hσ₀' a = 1 := by
      have h := cyclicBrauerHom_pow_finrank hσ₀' a
      rwa [← hrank, he, pow_one] at h
    rw [hA, hB]
  · obtain ⟨u, hu, hun⟩ := exists_unit_cyclicAlgebra hσ₀ a h2
    have hcomm : ∀ x : L',
        ((CrossedProduct.inclAlgHom (isMulCocycle₂_cyclicUnitCocycle hσ₀ a)).comp
            (φ.symm : L' →ₐ[K] L)) (σ₀' x) * (u : cyclicAlgebra hσ₀ a)
          = (u : cyclicAlgebra hσ₀ a)
            * ((CrossedProduct.inclAlgHom (isMulCocycle₂_cyclicUnitCocycle hσ₀ a)).comp
                (φ.symm : L' →ₐ[K] L)) x := by
      intro x
      have h0 : φ (σ₀ (φ.symm x)) = σ₀' x := by
        rw [hφ (φ.symm x), φ.apply_symm_apply]
      have hkey : (φ.symm : L' →ₐ[K] L) (σ₀' x) = σ₀ ((φ.symm : L' →ₐ[K] L) x) := by
        show φ.symm (σ₀' x) = σ₀ (φ.symm x)
        rw [← h0, φ.symm_apply_apply]
      simp only [AlgHom.comp_apply, hkey]
      exact hu (φ.symm x)
    have hpow : (u : cyclicAlgebra hσ₀ a) ^ finrank K L'
        = algebraMap K (cyclicAlgebra hσ₀ a) (a : K) := by
      rw [← hrank]
      exact hun
    have hdim : finrank K (cyclicAlgebra hσ₀ a) = finrank K L' * finrank K L' := by
      rw [CrossedProduct.finrank_eq, IsGalois.card_aut_eq_finrank K L, sq, hrank]
    obtain ⟨e⟩ := nonempty_algEquiv_cyclicAlgebra (A := cyclicAlgebra hσ₀ a) hσ₀' a
      ((CrossedProduct.inclAlgHom (isMulCocycle₂_cyclicUnitCocycle hσ₀ a)).comp
        (φ.symm : L' →ₐ[K] L)) u hcomm hpow hdim
    rw [cyclicBrauerHom_apply, cyclicBrauerHom_apply]
    exact Quotient.sound (IsBrauerEquivalent.of_algEquiv e)

end Transport

end InverseGalois.CFT

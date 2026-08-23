/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Herbrand

/-!
# Tate cohomology of a multiplicatively written module

The Tate groups are built for an additively written commutative group carrying an automorphism.
The modules that arithmetic supplies — the unit group of a field, the ideles, the idele classes —
are written multiplicatively, so this file records the dictionary.

An automorphism `σ` of a commutative group `M` becomes an automorphism of `Additive M`, the
operator `x ↦ σ x - x` becomes `x ↦ σ x / x`, and the norm `x ↦ ∑ i < n, σ ^ i x` becomes the
product of the conjugates `x ↦ ∏ i < n, σ ^ i x`.  With that translation in place, the two Tate
groups of `Additive M` are the multiplicative subquotients

`Ĥ⁰ = {x | σ x = x} / {∏ i < n, σ ^ i y}` and `Ĥ⁻¹ = {x | ∏ i < n, σ ^ i x = 1} / {σ y / y}`,

and this file gives the criteria that recognise them in that form.

## Main definitions

* `InverseGalois.CFT.addAut`: the automorphism of `Additive M` attached to an automorphism of `M`.

## Main results

* `InverseGalois.CFT.normHom_ofMul`: the norm operator is the product of the conjugates.
* `InverseGalois.CFT.tateHm1_eq_zero`: `Ĥ⁻¹` is trivial as soon as every element whose conjugates
  multiply to one is of the form `σ y / y`.
* `InverseGalois.CFT.tateH0_mk_eq_zero_iff`: a fixed point is trivial in `Ĥ⁰` exactly when it is a
  product of conjugates.

## Tags

Tate cohomology, multiplicative module, norm
-/

namespace InverseGalois.CFT

variable {M : Type*} [CommGroup M]

/-- Applying a successor power of a multiplicative automorphism means applying it last. -/
theorem mulPow_succ_apply (σ : M ≃* M) (i : ℕ) (x : M) : (σ ^ (i + 1)) x = σ ((σ ^ i) x) := by
  rw [pow_succ']
  rfl

/-- **The automorphism of `Additive M` attached to an automorphism of `M`.** -/
abbrev addAut (σ : M ≃* M) : Additive M ≃+ Additive M := MulEquiv.toAdditive σ

@[simp]
theorem addAut_apply (σ : M ≃* M) (x : M) :
    addAut σ (Additive.ofMul x) = Additive.ofMul (σ x) := rfl

/-- Powers of the transported automorphism are the transports of the powers. -/
theorem addAut_pow_apply (σ : M ≃* M) (i : ℕ) (x : M) :
    ((addAut σ) ^ i) (Additive.ofMul x) = Additive.ofMul ((σ ^ i) x) := by
  induction i with
  | zero => rfl
  | succ k ih => rw [pow_succ_apply, ih, addAut_apply, mulPow_succ_apply]

/-- The transported automorphism has the same order. -/
theorem addAut_pow_eq_one (σ : M ≃* M) {n : ℕ} (hσ : σ ^ n = 1) : (addAut σ) ^ n = 1 := by
  refine AddEquiv.ext fun u => ?_
  have h := addAut_pow_apply σ n (Additive.toMul u)
  rw [hσ] at h
  exact h

/-- The operator `x ↦ σ x - x` is the operator `x ↦ σ x / x`. -/
theorem sigmaSubOne_ofMul (σ : M ≃* M) (x : M) :
    sigmaSubOne (addAut σ) (Additive.ofMul x) = Additive.ofMul (σ x / x) := rfl

/-- **The norm operator is the product of the conjugates.** -/
theorem normHom_ofMul (σ : M ≃* M) (n : ℕ) (x : M) :
    normHom (addAut σ) n (Additive.ofMul x)
      = Additive.ofMul (∏ i ∈ Finset.range n, (σ ^ i) x) := by
  rw [normHom_apply]
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, Finset.prod_range_succ, ih, addAut_pow_apply]; rfl

/-- A fixed point of `σ` is a fixed point of the transported automorphism. -/
theorem addAut_apply_eq_self (σ : M ≃* M) {x : M} (hx : σ x = x) :
    addAut σ (Additive.ofMul x) = Additive.ofMul x := by rw [addAut_apply, hx]

/-- An element whose conjugates multiply to one has norm zero. -/
theorem normHom_ofMul_eq_zero (σ : M ≃* M) (n : ℕ) {x : M}
    (hx : (∏ i ∈ Finset.range n, (σ ^ i) x) = 1) :
    normHom (addAut σ) n (Additive.ofMul x) = 0 := by
  rw [normHom_ofMul, hx]
  rfl

/-- **`Ĥ⁻¹` is trivial when Hilbert's theorem 90 holds.**  If every element whose conjugates
multiply to one is a quotient `σ y / y`, then every class of `Ĥ⁻¹` vanishes. -/
theorem tateHm1_eq_zero (σ : M ≃* M) (n : ℕ)
    (h : ∀ x : M, (∏ i ∈ Finset.range n, (σ ^ i) x) = 1 → ∃ y : M, σ y / y = x)
    (c : tateHm1 (addAut σ) n) : c = 0 := by
  obtain ⟨u, hu, rfl⟩ := tateHm1.mk_surjective c
  obtain ⟨x, rfl⟩ : ∃ x : M, Additive.ofMul x = u := ⟨Additive.toMul u, rfl⟩
  rw [normHom_ofMul] at hu
  obtain ⟨y, hy⟩ := h x (ofMul_eq_zero.mp hu)
  refine (tateHm1.mk_eq_zero_iff _ _).mpr ⟨Additive.ofMul y, ?_⟩
  rw [← sigmaSubOne_apply, sigmaSubOne_ofMul, hy]

/-- **A fixed point is trivial in `Ĥ⁰` exactly when it is a product of conjugates.** -/
theorem tateH0_mk_eq_zero_iff (σ : M ≃* M) (n : ℕ) (x : M)
    (hx : addAut σ (Additive.ofMul x) = Additive.ofMul x) :
    tateH0.mk (addAut σ) n (Additive.ofMul x) hx = 0
      ↔ ∃ y : M, (∏ i ∈ Finset.range n, (σ ^ i) y) = x := by
  rw [tateH0.mk_eq_zero_iff]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨Additive.toMul u, Additive.ofMul.injective ?_⟩
    rw [← normHom_ofMul]
    exact hu
  · rintro ⟨y, hy⟩
    exact ⟨Additive.ofMul y, by rw [normHom_ofMul, hy]⟩

end InverseGalois.CFT

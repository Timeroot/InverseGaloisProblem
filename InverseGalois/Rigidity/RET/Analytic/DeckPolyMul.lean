/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.DeckPoly

/-!
# The group law of a simple extension, written in polynomials

An automorphism of `L = K(α)` is determined by where it sends `α`, and that image is `q(α)` for a
polynomial `q` of degree less than the degree of the minimal polynomial `P`.  The whole group
structure is then visible in `K[X]` modulo `P`: composing two automorphisms composes their
polynomials, the identity has polynomial `X`, and two different automorphisms have polynomials
whose difference is coprime to `P`.

Composition reverses the order, because substituting the polynomial of `σ` into that of `τ`
evaluates the outer automorphism at the inner one's image.

Every statement here is a divisibility or a Bézout identity in `K[X]`, so all of it survives
evaluation in any `K`-algebra — which is what turns an abstract Galois group into a group of
formulas acting on the roots of a family of equations.

## Main definitions

* `Rigidity.RET.autPoly` — the polynomial of an automorphism.

## Main results

* `Rigidity.RET.dvd_comp_autPoly` — the polynomial of an automorphism carries roots of `P` to roots
  of `P`.
* `Rigidity.RET.dvd_autPoly_mul` — the composition law, modulo `P`.
* `Rigidity.RET.dvd_autPoly_one` — the identity has polynomial `X`, modulo `P`.
* `Rigidity.RET.isCoprime_autPoly_sub` — distinct automorphisms are separated along the roots
  of `P`.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {P : Polynomial K} {α : L}
  (hgen : ∀ β : L, ∃ g : Polynomial K, aeval α g = β)

/-- **Two polynomials agreeing at the generator differ by a multiple of the minimal polynomial.**
This is the single mechanism behind every identity in this file. -/
theorem dvd_sub_of_aeval_eq (hP : P.Monic) (hPirr : Irreducible P) (hPα : aeval α P = 0)
    {f g : Polynomial K} (h : aeval α f = aeval α g) : P ∣ f - g := by
  have hmin : minpoly K α = P := (minpoly.eq_of_irreducible_of_monic hPirr hPα hP).symm
  have hdvd : minpoly K α ∣ f - g := by
    refine minpoly.dvd K α ?_
    rw [map_sub, h, sub_self]
  rwa [hmin] at hdvd

/-! ### The polynomial of an automorphism -/

/-- **The polynomial describing an automorphism of a simple extension.** -/
def autPoly (P : Polynomial K) {α : L}
    (hgen : ∀ β : L, ∃ g : Polynomial K, aeval α g = β) (σ : L ≃ₐ[K] L) : Polynomial K :=
  deckPoly P hgen (σ α)

theorem aeval_autPoly (hP : P.Monic) (hPα : aeval α P = 0) (σ : L ≃ₐ[K] L) :
    aeval α (autPoly P hgen σ) = σ α :=
  aeval_deckPoly hgen hP hPα _

theorem degree_autPoly_lt (hP : P.Monic) (σ : L ≃ₐ[K] L) :
    (autPoly P hgen σ).degree < P.degree :=
  degree_deckPoly_lt hgen hP _

include hgen in
/-- **An automorphism is determined by its effect on the generator.** -/
theorem eq_of_apply_gen_eq {σ τ : L ≃ₐ[K] L} (h : σ α = τ α) : σ = τ := by
  refine AlgEquiv.ext fun β => ?_
  obtain ⟨g, rfl⟩ := hgen β
  rw [← aeval_algHom_apply σ α g, ← aeval_algHom_apply τ α g, h]

/-! ### The three identities -/

/-- **The polynomial of an automorphism carries roots of `P` to roots of `P`.** -/
theorem dvd_comp_autPoly (hP : P.Monic) (hPirr : Irreducible P) (hPα : aeval α P = 0)
    (σ : L ≃ₐ[K] L) : P ∣ P.comp (autPoly P hgen σ) := by
  refine dvd_comp_deckPoly hgen hP hPirr hPα ?_
  rw [aeval_algHom_apply σ α P, hPα, map_zero]

/-- **The composition law**: substituting the polynomial of `σ` into that of `τ` gives the
polynomial of `τ * σ`, modulo `P`. -/
theorem dvd_autPoly_mul (hP : P.Monic) (hPirr : Irreducible P) (hPα : aeval α P = 0)
    (σ τ : L ≃ₐ[K] L) :
    P ∣ (autPoly P hgen σ).comp (autPoly P hgen τ) - autPoly P hgen (τ * σ) := by
  refine dvd_sub_of_aeval_eq hP hPirr hPα ?_
  rw [aeval_comp, aeval_autPoly hgen hP hPα, aeval_algHom_apply τ α (autPoly P hgen σ),
    aeval_autPoly hgen hP hPα, aeval_autPoly hgen hP hPα, AlgEquiv.mul_apply]

/-- **The identity automorphism has polynomial `X`**, modulo `P`. -/
theorem dvd_autPoly_one (hP : P.Monic) (hPirr : Irreducible P) (hPα : aeval α P = 0) :
    P ∣ autPoly P hgen (1 : L ≃ₐ[K] L) - X := by
  refine dvd_sub_of_aeval_eq hP hPirr hPα ?_
  rw [aeval_autPoly hgen hP hPα, aeval_X]
  exact AlgEquiv.one_apply α

/-- **Distinct automorphisms are separated along the roots of `P`.** -/
theorem isCoprime_autPoly_sub (hP : P.Monic) (hPirr : Irreducible P) (hPα : aeval α P = 0)
    {σ τ : L ≃ₐ[K] L} (h : σ ≠ τ) :
    IsCoprime P (autPoly P hgen σ - autPoly P hgen τ) :=
  isCoprime_deckPoly_sub hgen hP hPirr hPα fun hEq => h (eq_of_apply_gen_eq hgen (α := α) hEq)

/-- The Bézout identity behind `Rigidity.RET.isCoprime_autPoly_sub`. -/
theorem exists_bezout_autPoly_sub (hP : P.Monic) (hPirr : Irreducible P) (hPα : aeval α P = 0)
    {σ τ : L ≃ₐ[K] L} (h : σ ≠ τ) :
    ∃ A B : Polynomial K, A * P + B * (autPoly P hgen σ - autPoly P hgen τ) = 1 :=
  isCoprime_autPoly_sub hgen hP hPirr hPα h

end Rigidity.RET

end

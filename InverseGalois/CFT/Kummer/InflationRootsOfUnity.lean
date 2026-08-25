/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Making a cochain take values in the roots of unity after adjoining a radical

A two-cocycle of a Galois group whose values are `n`-th roots of unity may still only be a
coboundary through a one-cochain `b` with much larger values.  The `n`-th powers of such a `b`
form a one-cocycle, so Hilbert's theorem 90 produces a single element `β` of the base with
`g • β / β = b g ^ n`.  Adjoining an `n`-th root `α` of `β` to a larger Galois extension and
correcting `b` by `g • α / α` produces a one-cochain whose values are `n`-th roots of unity and
which cobounds the inflated cocycle.

This is the finite-level form of the standard argument that a class of the Galois group with
values in the roots of unity which dies in the units already dies in the roots of unity over a
larger extension.

## Main results

* `InverseGalois.CFT.exists_pow_eq_of_isMulCoboundary₂`: **the `n`-th powers of a one-cochain
  cobounding a cocycle of `n`-th roots of unity are the coboundary of a single element.**
* `InverseGalois.CFT.exists_cochain_pow_eq_one`: **over an extension containing an `n`-th root of
  that element, the inflated cocycle is cobounded by a one-cochain of `n`-th roots of unity.**

## Tags

Kummer theory, Hilbert 90, group cohomology, two-cocycle, coboundary, root of unity, inflation
-/

open groupCohomology

namespace InverseGalois.CFT

section Base

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K]

/-- **The `n`-th powers of a one-cochain cobounding a cocycle whose values are `n`-th roots of
unity are the coboundary of a single element.**  Raising the coboundary relation to the `n`-th
power kills the cocycle, so `g ↦ b g ^ n` is a one-cocycle and Hilbert's theorem 90 applies. -/
theorem exists_pow_eq_of_isMulCoboundary₂ {n : ℕ}
    {a : Gal(K/k) × Gal(K/k) → Kˣ} (hpow : ∀ p, a p ^ n = 1)
    {b : Gal(K/k) → Kˣ} (hb : ∀ g h : Gal(K/k), g • b h / b (g * h) * b g = a (g, h)) :
    ∃ β : Kˣ, ∀ g : Gal(K/k), g • β / β = b g ^ n := by
  refine isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units (fun g => b g ^ n) ?_
  intro g h
  have h1 : (g • b h / b (g * h) * b g) ^ n = 1 := by rw [hb g h]; exact hpow (g, h)
  rw [mul_pow, div_pow, ← smul_pow', div_mul_eq_mul_div, div_eq_one] at h1
  show b (g * h) ^ n = g • b h ^ n * b g ^ n
  exact h1.symm

end Base

section Tower

variable {k K M : Type*} [Field k] [Field K] [Field M] [Algebra k K] [Algebra k M] [Algebra K M]
  [IsScalarTower k K M] [Normal k K]

/-- **Over an extension containing an `n`-th root of the element produced by Hilbert's theorem 90,
the inflated cocycle is cobounded by a one-cochain whose values are `n`-th roots of unity.**
Correcting the given one-cochain by `g • α / α` leaves the coboundary unchanged, because that
correction is itself a coboundary, and kills the `n`-th power. -/
theorem exists_cochain_pow_eq_one {n : ℕ}
    {a : Gal(K/k) × Gal(K/k) → Kˣ}
    {b : Gal(K/k) → Kˣ} (hb : ∀ g h : Gal(K/k), g • b h / b (g * h) * b g = a (g, h))
    {β : Kˣ} (hβ : ∀ g : Gal(K/k), g • β / β = b g ^ n)
    (α : Mˣ) (hα : α ^ n = Units.map (algebraMap K M : K →* M) β) :
    ∃ b' : Gal(M/k) → Mˣ, (∀ g : Gal(M/k), b' g ^ n = 1) ∧
      ∀ g h : Gal(M/k), g • b' h / b' (g * h) * b' g =
        Units.map (algebraMap K M : K →* M)
          (a (AlgEquiv.restrictNormalHom K g, AlgEquiv.restrictNormalHom K h)) := by
  classical
  set ι : Kˣ →* Mˣ := Units.map (algebraMap K M : K →* M) with hι
  have hcomm : ∀ (g : Gal(M/k)) (u : Kˣ),
      g • ι u = ι (AlgEquiv.restrictNormalHom K g • u) := by
    intro g u
    refine Units.ext ?_
    show g (algebraMap K M (u : K))
      = algebraMap K M ((AlgEquiv.restrictNormalHom K g : Gal(K/k)) u)
    exact (AlgEquiv.restrictNormal_commutes g K (u : K)).symm
  refine ⟨fun g => ι (b (AlgEquiv.restrictNormalHom K g)) * (g • α / α)⁻¹, ?_, ?_⟩
  · intro g
    rw [mul_pow, ← map_pow, inv_pow, div_pow, ← smul_pow', hα, hcomm, ← map_div, hβ, map_pow,
      mul_inv_cancel]
  · intro g h
    rw [← hb (AlgEquiv.restrictNormalHom K g) (AlgEquiv.restrictNormalHom K h)]
    simp only [map_mul, map_div, ← hcomm, smul_div', smul_mul', smul_inv', ← mul_smul]
    refine Additive.ofMul.injective ?_
    simp only [ofMul_mul, ofMul_div, ofMul_inv]
    abel

end Tower

end InverseGalois.CFT

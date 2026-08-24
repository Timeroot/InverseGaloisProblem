/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Basic

/-!
# Multiples of a fixed point that are norms

The zeroth Tate group is the fixed points modulo the norms, so its order annihilates every class:
a fixed point multiplied by that order is a norm, and so is a fixed point multiplied by any
multiple of that order.

This is the mechanism behind the local half of the second inequality.  At a place where the norm
index is the local degree, and for an extension whose degree is a prime, the local degree divides
that prime, so every prime multiple of a local unit fixed by the decomposition group is a local
norm.

## Main results

* `InverseGalois.CFT.exists_normHom_eq_card_nsmul`: **a fixed point multiplied by the order of the
  zeroth Tate group is a norm.**
* `InverseGalois.CFT.exists_normHom_eq_nsmul`: **more generally a fixed point multiplied by any
  multiple of that order is a norm.**

## Tags

Tate cohomology, norm, fixed point, annihilator
-/

namespace InverseGalois.CFT

variable {A : Type*} [AddCommGroup A] {σ : A ≃+ A} {n : ℕ}

/-- The class of a multiple of a fixed point is that multiple of the class. -/
theorem tateH0.nsmul_mk (d : ℕ) (x : A) (hx : σ x = x) :
    d • tateH0.mk σ n x hx = tateH0.mk σ n (d • x) (by rw [map_nsmul, hx]) := rfl

/-- **A fixed point multiplied by the order of the zeroth Tate group is a norm**, because that
order annihilates the group, so the class of the multiple vanishes. -/
theorem exists_normHom_eq_card_nsmul (x : A) (hx : σ x = x) :
    ∃ y, normHom σ n y = Nat.card (tateH0 σ n) • x := by
  have hfix : σ (Nat.card (tateH0 σ n) • x) = Nat.card (tateH0 σ n) • x := by rw [map_nsmul, hx]
  refine (tateH0.mk_eq_zero_iff (σ := σ) (n := n) _ hfix).mp ?_
  rw [← tateH0.nsmul_mk _ x hx]
  exact card_nsmul_eq_zero'

/-- **A fixed point multiplied by any multiple of the order of the zeroth Tate group is a norm**,
the norms forming a subgroup. -/
theorem exists_normHom_eq_nsmul (x : A) (hx : σ x = x) {m : ℕ}
    (hm : Nat.card (tateH0 σ n) ∣ m) : ∃ y, normHom σ n y = m • x := by
  obtain ⟨c, rfl⟩ := hm
  obtain ⟨y, hy⟩ := exists_normHom_eq_card_nsmul x hx
  exact ⟨c • y, by rw [map_nsmul, hy, smul_smul, mul_comm]⟩

end InverseGalois.CFT

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Genus.OrdBound

/-!
# A derivation creates poles of bounded order

A derivation of the function field of a cover need not preserve the functions regular at a prime,
but it cannot do arbitrary damage there.  If the functions of the cover are spanned, over the
functions of the base, by finitely many of them, and the derivation preserves the functions of the
base, then Leibniz's rule expresses the derivative of any function of the cover in terms of the
derivatives of those finitely many: the pole it creates is no worse than the worst pole among them.

Passing from the functions of the cover to the functions merely regular at one prime costs
nothing: such a function is a fraction whose denominator is invertible at that prime, and
differentiating the equation relating the two sides moves the bound across unchanged.

## Main results

* `Rigidity.RET.exists_ordAtLeast_deriv` — a derivation preserving a base over which the domain is
  module-finite creates, at any prime, a pole of order bounded independently of the function.
-/

open IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section


namespace Rigidity.RET

section Crude

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable {v : HeightOneSpectrum R}
variable {k : Type*} [Field k] [Algebra k K]
variable {A : Type*} [CommRing A] [Algebra A R] [Algebra A K] [IsScalarTower A R K]

/-- **On the functions of the cover the pole created by the derivation is bounded.** -/
theorem exists_ordAtLeast_deriv_algebraMap [Module.Finite A R] (δ : Derivation k K K)
    (hA : ∀ a : A, OrdAtLeast K v 0 (δ (algebraMap A K a))) :
    ∃ N : ℕ, ∀ y : R, OrdAtLeast K v (-(N : ℤ)) (δ (algebraMap R K y)) := by
  classical
  obtain ⟨s, hs⟩ : (⊤ : Submodule A R).FG := Module.Finite.fg_top
  refine ⟨s.sup fun b => (-(ord K v (δ (algebraMap R K b)))).toNat, fun y => ?_⟩
  set N : ℕ := s.sup fun b => (-(ord K v (δ (algebraMap R K b)))).toNat with hN
  have hy : y ∈ Submodule.span A (s : Set R) := by rw [hs]; exact Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem b hb =>
    have hle : (-(ord K v (δ (algebraMap R K b)))).toNat ≤ N :=
      Finset.le_sup (f := fun b => (-(ord K v (δ (algebraMap R K b)))).toNat) hb
    exact ordAtLeast_of_ord_le (by omega)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add]; exact hx.add hy
  | smul a x _ hx =>
    have hAa : OrdAtLeast K v 0 (algebraMap A K a) := by
      rw [IsScalarTower.algebraMap_apply A R K]
      exact ordAtLeast_algebraMap _
    have hmul : algebraMap R K (a • x) = algebraMap A K a * algebraMap R K x := by
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
    rw [hmul, δ.leibniz, smul_eq_mul, smul_eq_mul]
    refine OrdAtLeast.add ?_ ?_
    · simpa using hAa.mul hx
    · have h := (ordAtLeast_algebraMap (K := K) (v := v) x).mul (hA a)
      exact h.mono (by omega)

/-- **The pole created by the derivation is bounded on every function regular at the prime.**

Such a function is a fraction with denominator invertible at the prime; differentiating the
relation between numerator and denominator carries the bound over. -/
theorem exists_ordAtLeast_deriv [Module.Finite A R] (δ : Derivation k K K)
    (hA : ∀ a : A, OrdAtLeast K v 0 (δ (algebraMap A K a))) :
    ∃ N : ℕ, ∀ z : K, OrdAtLeast K v 0 z → OrdAtLeast K v (-(N : ℤ)) (δ z) := by
  obtain ⟨N, hNy⟩ := exists_ordAtLeast_deriv_algebraMap (v := v) (A := A) δ hA
  refine ⟨N, fun z hz => ?_⟩
  obtain ⟨a, s, hsv, hsz⟩ := exists_den_notMem_of_ord_nonneg K v (ordAtLeast_zero_iff.1 hz)
  have hs0 : algebraMap R K s ≠ 0 := by
    intro h
    exact hsv (by simp [IsFractionRing.to_map_eq_zero_iff.mp h])
  have hords : ord K v (algebraMap R K s) = 0 := by
    have h1 : 0 ≤ ord K v (algebraMap R K s) := ord_nonneg v s
    have h2 : ¬ 0 < ord K v (algebraMap R K s) := by
      intro h
      exact hsv ((mem_iff_ord_pos (K := K) v (fun hs => hs0 (by rw [hs, map_zero]))).2 h)
    omega
  have hinv : OrdAtLeast K v 0 (algebraMap R K s)⁻¹ := by
    refine ordAtLeast_of_ord_le ?_
    rw [ord_inv, hords, neg_zero]
  -- differentiate `s · z = a`
  have hδ : δ (algebraMap R K s) * z + algebraMap R K s * δ z = δ (algebraMap R K a) := by
    have h := congrArg δ hsz
    rw [δ.leibniz, smul_eq_mul, smul_eq_mul] at h
    linear_combination h
  have hbound : OrdAtLeast K v (-(N : ℤ)) (algebraMap R K s * δ z) := by
    have heq : algebraMap R K s * δ z
        = δ (algebraMap R K a) - δ (algebraMap R K s) * z := by linear_combination hδ
    rw [heq]
    refine (hNy a).sub ?_
    simpa using (hNy s).mul hz
  have hzeq : δ z = (algebraMap R K s * δ z) * (algebraMap R K s)⁻¹ := by field_simp
  rw [hzeq]
  simpa using hbound.mul hinv

end Crude

end Rigidity.RET

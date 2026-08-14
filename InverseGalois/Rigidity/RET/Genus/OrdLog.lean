/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Genus.OrdCrude
import InverseGalois.Rigidity.RET.Genus.OrdResidue

/-!
# A derivation logarithmic along a coordinate of the base preserves the local ring

Let a derivation of the function field of a cover be given, and let a function of the base vanish
at a prime of the cover to some order.  Differentiating that function can only lose one order
against it — that is what it means for the derivation to be logarithmic along the base coordinate,
and it is what happens at a branch point in characteristic zero, where the ramification index is
invertible.

Under that condition the derivation preserves the functions regular at the prime.  Factoring the
base coordinate as a power of the coordinate at the prime times a unit, and differentiating the
factorization, expresses the derivative of the coordinate at the prime in terms of the derivative
of the base coordinate and of the unit; the ramification index appears as a factor, and dividing by
it — possible exactly in the tame case — shows that the pole of the derivative of the coordinate at
the prime is one order better than the worst pole the derivation creates.  That is the descent
step, and iterating it removes the pole.

## Main results

* `Rigidity.RET.exists_ord_eq_one` — every prime has a coordinate.
* `Rigidity.RET.ordAtLeast_deriv_uniformizer` — differentiating the coordinate at a prime gains an
  order against the worst pole the derivation creates.
* `Rigidity.RET.ordAtLeast_zero_deriv_of_logarithmic` — a derivation logarithmic along a base
  coordinate, with tame ramification index, preserves the functions regular at the prime.
-/

open IsDedekindDomain WithZero
open scoped nonZeroDivisors

noncomputable section


namespace Rigidity.RET

section Log

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable {v : HeightOneSpectrum R}
variable {k : Type*} [Field k] [Algebra k R] [Algebra k K] [IsScalarTower k R K]

/-! ## Coordinates and constants -/

/-- **Every prime has a coordinate**: a function vanishing there to order exactly one. -/
theorem exists_ord_eq_one : ∃ t : K, ord K v t = 1 := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact exp_ne_zero hπ.symm
  refine ⟨π, ?_⟩
  rw [valuation_eq_exp_neg_ord K v hπ0] at hπ
  have := exp_injective hπ
  omega

/-- **A nonzero constant neither vanishes nor has a pole.** -/
theorem ord_algebraMap_const {c : k} (hc : c ≠ 0) : ord K v (algebraMap k K c) = 0 := by
  have hmem : ∀ d : k, 0 ≤ ord K v (algebraMap k K d) := by
    intro d
    rw [IsScalarTower.algebraMap_apply k R K]
    exact ord_nonneg v _
  have h1 := hmem c
  have h2 := hmem c⁻¹
  have hne : algebraMap k K c ≠ 0 := by
    simpa using (map_ne_zero_iff (algebraMap k K) (algebraMap k K).injective).2 hc
  have hsum : ord K v (algebraMap k K c) + ord K v (algebraMap k K c⁻¹) = 0 := by
    rw [← ord_mul v hne (by simpa using (map_ne_zero_iff (algebraMap k K)
      (algebraMap k K).injective).2 (inv_ne_zero hc)), ← map_mul, mul_inv_cancel₀ hc, map_one,
      ord_one]
  omega

/-! ## Differentiating the coordinate at the prime -/

/-- **Differentiating the coordinate at a prime gains an order.**

The base coordinate `g` vanishes at the prime to order `e`, which is invertible in the constants,
and differentiating it loses at most one order against it.  If the derivation creates a pole of
order at most `N ≥ 1` out of every function regular at the prime, then the derivative of the
coordinate at the prime has a pole of order at most `N - 1`. -/
theorem ordAtLeast_deriv_uniformizer (δ : Derivation k K K) {t g : K} {e N : ℕ}
    (ht : ord K v t = 1) (hg : g ≠ 0) (hge : ord K v g = e) (he : (e : k) ≠ 0)
    (hδg : OrdAtLeast K v ((e : ℤ) - 1) (δ g)) (hN1 : 1 ≤ N)
    (hN : ∀ z : K, OrdAtLeast K v 0 z → OrdAtLeast K v (-(N : ℤ)) (δ z)) :
    OrdAtLeast K v (1 - (N : ℤ)) (δ t) := by
  have ht0 : t ≠ 0 := ne_zero_of_ord_eq_one ht
  have he1 : 1 ≤ e := by
    by_contra h
    have : e = 0 := by omega
    exact he (by rw [this]; simp)
  -- the unit left after taking out the coordinate
  set w : K := g * (t ^ e)⁻¹ with hwdef
  have htpow : (t : K) ^ e ≠ 0 := pow_ne_zero _ ht0
  have hw0 : w ≠ 0 := by
    rw [hwdef]
    exact mul_ne_zero hg (inv_ne_zero htpow)
  have hordw : ord K v w = 0 := by
    rw [hwdef, ord_mul v hg (inv_ne_zero htpow), ord_inv, ord_pow v ht0, ht, hge]
    omega
  have hwreg : OrdAtLeast K v 0 w := ordAtLeast_of_ord_le (le_of_eq hordw.symm)
  have hgeq : g = t ^ e * w := by
    rw [hwdef]
    field_simp
  -- the constant `e` is invertible
  have hek : algebraMap k K (e : k) = (e : K) := by rw [map_natCast]
  have heK : (e : K) ≠ 0 := by
    rw [← hek]
    simpa using (map_ne_zero_iff (algebraMap k K) (algebraMap k K).injective).2 he
  have horde : ord K v ((e : K)) = 0 := by rw [← hek]; exact ord_algebraMap_const he
  -- differentiate the factorization
  have hδg2 : δ g = t ^ e * δ w + w * ((e : K) * (t ^ (e - 1) * δ t)) := by
    conv_lhs => rw [hgeq]
    rw [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      nsmul_eq_mul]
  have hkey : (e : K) * w * t ^ (e - 1) * δ t = δ g - t ^ e * δ w := by
    rw [hδg2]; ring
  -- the left side has a bounded pole
  have hδw : OrdAtLeast K v (-(N : ℤ)) (δ w) := hN w hwreg
  have hright : OrdAtLeast K v ((e : ℤ) - N) (δ g - t ^ e * δ w) := by
    refine OrdAtLeast.sub (hδg.mono (by omega)) ?_
    have htpowb : OrdAtLeast K v (e : ℤ) (t ^ e) := by
      refine ordAtLeast_of_ord_le ?_
      rw [ord_pow v ht0, ht]
      omega
    exact (htpowb.mul hδw).mono (by omega)
  -- divide by the unit factor
  have hfac0 : (e : K) * w * t ^ (e - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero heK hw0) (pow_ne_zero _ ht0)
  have hordfac : ord K v (((e : K) * w * t ^ (e - 1))⁻¹) = 1 - (e : ℤ) := by
    rw [ord_inv, ord_mul v (mul_ne_zero heK hw0) (pow_ne_zero _ ht0),
      ord_mul v heK hw0, horde, hordw, ord_pow v ht0, ht]
    omega
  have hinvb : OrdAtLeast K v (1 - (e : ℤ)) (((e : K) * w * t ^ (e - 1))⁻¹) :=
    ordAtLeast_of_ord_le (le_of_eq hordfac.symm)
  have hδteq : δ t = (δ g - t ^ e * δ w) * ((e : K) * w * t ^ (e - 1))⁻¹ := by
    rw [← hkey]
    field_simp
  rw [hδteq]
  exact (hright.mul hinvb).mono (by omega)

/-! ## The local ring is preserved -/

variable {A : Type*} [CommRing A] [Algebra A R] [Algebra A K] [IsScalarTower A R K]

/-- **A derivation logarithmic along a base coordinate preserves the functions regular at a
prime.** -/
theorem ordAtLeast_zero_deriv_of_logarithmic [Module.Finite A R] (δ : Derivation k K K)
    (hA : ∀ a : A, OrdAtLeast K v 0 (δ (algebraMap A K a)))
    (hk : ∀ b : R, ∃ c : k, b - algebraMap k R c ∈ v.asIdeal)
    {g : K} {e : ℕ} (hg : g ≠ 0) (hge : ord K v g = e) (he : (e : k) ≠ 0)
    (hδg : OrdAtLeast K v ((e : ℤ) - 1) (δ g)) :
    ∀ z : K, OrdAtLeast K v 0 z → OrdAtLeast K v 0 (δ z) := by
  obtain ⟨t, ht⟩ := exists_ord_eq_one (v := v) (K := K)
  obtain ⟨N, hN⟩ := exists_ordAtLeast_deriv (v := v) (A := A) δ hA
  refine ordAtLeast_deriv_of_descent δ ht
    (fun z hz => exists_const_ordAtLeast_one_sub hk hz) (fun M hM1 hMbd => ?_) N hN
  exact ordAtLeast_deriv_uniformizer δ ht hg hge he hδg hM1 hMbd

end Log

end Rigidity.RET

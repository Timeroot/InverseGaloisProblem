/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.MultiKummerInertia
import InverseGalois.Rigidity.RET.Infinity

/-!
# The multi-point Kummer cover is ramified at infinity unless the exponents sum correctly

`RET/MultiKummerInertia.lean` shows that the cover `wⁿ = ∏ᵢ (T - tᵢ)^{aᵢ}` is unramified at the
point at infinity when `n` divides `∑ᵢ aᵢ`.  The converse holds too, and this module proves it.

In the coordinate `S = T⁻¹` at infinity the datum becomes `∏ᵢ (1 - tᵢS)^{aᵢ} · S^{c}`, where `c`
is chosen so that `∑ᵢ aᵢ + c` is a multiple `n·s` of `n`; the first factor is a unit at `S = 0`,
so the multiplicity of the origin in the twisted datum is exactly `c`.  If `n` does not divide
`∑ᵢ aᵢ` then `c` can be taken with `0 < c < n`, and the local ramification bound of
`RET/LocalKummer.lean` gives inertia of order at least `n / gcd(n, c) ≥ 2` at the origin of the
twist — that is, ramification at infinity.

## Main results

* `Rigidity.RET.twistRootS_pow_gen` — the equation satisfied at infinity by the Kummer root
  divided by `T^s`, for an arbitrary `s`.
* `Rigidity.RET.dvd_sum_of_isUnramifiedAtInfinity` — a multi-point Kummer cover unramified at
  infinity has `n ∣ ∑ᵢ aᵢ`.
-/

open Polynomial IntermediateField

noncomputable section


namespace Rigidity.RET

open GeomAKLB Module

/-! ### The equation at infinity, with a leftover power of the parameter -/

section Gen

variable {r : ℕ} {N : Type} [Field N] [Algebra (RatFunc k) N]

/-- **The Kummer root read in the coordinate at infinity, for an arbitrary shift.**  Dividing the
root by `T^s` leaves the equation of the datum `revMultiA` times the power `S^c` of the
coordinate at infinity, where `c` is the defect `n·s - ∑ᵢ aᵢ`. -/
theorem twistRootS_pow_gen {n s c : ℕ} (t : Fin r → k) (a : Fin r → ℕ)
    (hsum : (∑ i, a i) + c = n * s) (w : N)
    (hw : w ^ n =
      algebraMap (RatFunc k) N (algebraMap (Polynomial k) (RatFunc k) (multiA t a))) :
    (twistRootS s w) ^ n =
      algebraMap (RatFunc k) (Twist invSubst N)
        (algebraMap (Polynomial k) (RatFunc k) (revMultiA t a * X ^ c)) := by
  have hX0 : algebraMap (RatFunc k) N (RatFunc.X : RatFunc k) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap (RatFunc k) N).injective).mpr (RatFunc.X_ne_zero (K := k))
  set Xn : N := algebraMap (RatFunc k) N (RatFunc.X : RatFunc k) with hXn
  set A : N := algebraMap (RatFunc k) N
    (invSubst (algebraMap (Polynomial k) (RatFunc k) (revMultiA t a))) with hAdef
  have key : A * Xn ^ (∑ i, a i)
      = algebraMap (RatFunc k) N (algebraMap (Polynomial k) (RatFunc k) (multiA t a)) := by
    have h := congrArg (algebraMap (RatFunc k) N) (invSubst_revMultiA t a)
    rwa [map_mul, map_pow] at h
  have hXinv : invSubst (algebraMap (Polynomial k) (RatFunc k) (X : Polynomial k))
      = (RatFunc.X : RatFunc k)⁻¹ := by rw [RatFunc.algebraMap_X, invSubst_X]
  have hrhs : invSubst (algebraMap (Polynomial k) (RatFunc k) (revMultiA t a * X ^ c))
      = invSubst (algebraMap (Polynomial k) (RatFunc k) (revMultiA t a))
        * ((RatFunc.X : RatFunc k)⁻¹) ^ c := by
    rw [map_mul, map_mul, map_pow, map_pow, hXinv]
  show (w * algebraMap (RatFunc k) N ((RatFunc.X : RatFunc k)⁻¹ ^ s)) ^ n
      = algebraMap (RatFunc k) N
        (invSubst (algebraMap (Polynomial k) (RatFunc k) (revMultiA t a * X ^ c)))
  rw [hrhs, map_mul, ← hAdef, map_pow, map_inv₀, ← hXn, map_pow, map_inv₀, ← hXn, mul_pow,
    ← pow_mul, hw, ← key, mul_assoc]
  congr 1
  have hsn : s * n = (∑ i, a i) + c := by rw [mul_comm]; exact hsum.symm
  rw [hsn, pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hX0, one_pow, one_mul]

end Gen

/-! ### Ramification at infinity when the exponents do not sum to a multiple of `n` -/

section Converse

attribute [local instance] Ideal.Quotient.field GeomAKLB.instMSA GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instIntegral GeomAKLB.instFaithful
  GeomAKLB.instDedekindB

variable {r : ℕ}

/-- **A multi-point Kummer cover unramified at infinity has `n ∣ ∑ᵢ aᵢ`.**  Otherwise the datum
read at infinity vanishes at the origin of the twist to an order `c` with `0 < c < n`, and the
cover is ramified there. -/
theorem dvd_sum_of_isUnramifiedAtInfinity {n : ℕ} [NeZero n] {t : Fin r → k} {a : Fin r → ℕ}
    (L : LineCover) [IsSplittingField (RatFunc k) L.M
      ((X : (RatFunc k)[X]) ^ n - C (algebraMap (Polynomial k) (RatFunc k) (multiA t a)))]
    (hinf : L.IsUnramifiedAtInfinity) : n ∣ ∑ i, a i := by
  by_contra hnd
  have hnpos : 0 < n := NeZero.pos n
  -- the defect at infinity
  obtain ⟨s, c, hcpos, hclt, hsum⟩ : ∃ s c, 0 < c ∧ c < n ∧ (∑ i, a i) + c = n * s := by
    have hmlt : (∑ i, a i) % n < n := Nat.mod_lt _ hnpos
    have hm0 : (∑ i, a i) % n ≠ 0 := fun h => hnd (Nat.dvd_of_mod_eq_zero h)
    have hq := Nat.div_add_mod (∑ i, a i) n
    refine ⟨(∑ i, a i) / n + 1, n - (∑ i, a i) % n, by omega, by omega, ?_⟩
    rw [Nat.mul_add, mul_one]
    omega
  -- the Kummer root, read at infinity
  set w : L.M := kummerRoot n (algebraMap (Polynomial k) (RatFunc k) (multiA t a)) L.M with hwdef
  have hwpow : w ^ n = algebraMap (RatFunc k) L.M
      (algebraMap (Polynomial k) (RatFunc k) (multiA t a)) := kummerRoot_pow _
  have hvpow := twistRootS_pow_gen t a hsum w hwpow
  have htower : ∀ b : Polynomial k,
      algebraMap (Polynomial k) (Twist (invSubst : RatFunc k ≃+* RatFunc k) L.M) b
        = algebraMap (RatFunc k) (Twist (invSubst : RatFunc k ≃+* RatFunc k) L.M)
            (algebraMap (Polynomial k) (RatFunc k) b) := fun b =>
    IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) _ b
  have hint : IsIntegral (Polynomial k) (twistRootS s w) :=
    IsIntegral.of_pow hnpos (by rw [hvpow, ← htower]; exact isIntegral_algebraMap)
  set v : Bring (Twist (invSubst : RatFunc k ≃+* RatFunc k) L.M) := ⟨twistRootS s w, hint⟩
    with hvdef
  have hvB : v ^ n = algebraMap (Polynomial k)
      (Bring (Twist (invSubst : RatFunc k ≃+* RatFunc k) L.M)) (revMultiA t a * X ^ c) := by
    apply Subtype.ext
    rw [Subalgebra.coe_pow, Subalgebra.coe_algebraMap]
    show (twistRootS s w) ^ n
      = algebraMap (Polynomial k) (Twist (invSubst : RatFunc k ≃+* RatFunc k) L.M)
        (revMultiA t a * X ^ c)
    rw [htower, hvpow]
  -- the local ramification bound at the origin of the twist
  obtain ⟨Q, hQmax, hQover⟩ :=
    exists_Q_over_placeP (Twist (invSubst : RatFunc k ≃+* RatFunc k) L.M) (0 : k)
  haveI := hQmax
  haveI := hQover
  have hA : revMultiA t a * X ^ c = (X - C (0 : k)) ^ c * revMultiA t a := by
    rw [C_0, sub_zero, mul_comm]
  have hU : (revMultiA t a).eval 0 ≠ 0 := by rw [revMultiA_eval_zero]; exact one_ne_zero
  have hle := le_card_geomInertia_of_pow_dvd (0 : k) Q (local_pow_dvd_map_placeP hA hU v hvB Q)
  -- the inertia group at the origin of the twist is non-trivial
  have h2 : 2 ≤ n / Nat.gcd n c := by
    have hg0 : 0 < Nat.gcd n c := Nat.gcd_pos_of_pos_left _ hnpos
    have hgc : Nat.gcd n c ≤ c := Nat.le_of_dvd hcpos (Nat.gcd_dvd_right n c)
    have hmul : Nat.gcd n c * (n / Nat.gcd n c) = n := Nat.mul_div_cancel' (Nat.gcd_dvd_left n c)
    by_contra hlt
    have hn : n ≤ Nat.gcd n c := by
      calc n = Nat.gcd n c * (n / Nat.gcd n c) := hmul.symm
        _ ≤ Nat.gcd n c * 1 := Nat.mul_le_mul_left _ (by omega)
        _ = Nat.gcd n c := mul_one _
    omega
  have hne : geomInertia (Twist (invSubst : RatFunc k ≃+* RatFunc k) L.M) Q ≠ ⊥ :=
    (Subgroup.one_lt_card_iff_ne_bot _).mp (by omega)
  obtain ⟨σ, hσ⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hone : σ.1 = 1 := hinf σ.1 ⟨Q, hQmax, hQover, σ.2⟩
  exact hσ (Subtype.ext hone)

end Converse

end Rigidity.RET

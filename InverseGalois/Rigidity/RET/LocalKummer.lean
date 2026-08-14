/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.MultiKummer

/-!
# Local ramification of a Kummer cover at a point

A Kummer cover `wⁿ = A` of the line is ramified at a point `p` to the order dictated by the
multiplicity of `p` in `A`: if `A = (T - p)^c · U` with `U(p) ≠ 0`, then the place above `p`
occurs to the power `n / gcd(n, c)` in the extended place.

The mechanism is the one used for the multi-point covers of `RET/MultiKummerInertia.lean`, but
nothing here refers to the shape of `A` away from `p`.  Write `d = gcd(n, c)`, `m = n/d` and
`C = c/d`; then `Y = w^m / (T - p)^C` is integral with `Y^d = U`, hence a unit at every place
above `p`, and Bézout `C·x = m·q + 1` turns `z = w^x / (T - p)^q` into an element with
`z^m = Y^x · (T - p)`, which forces the place above `p` to occur to the power `m`.

## Main results

* `Rigidity.RET.exists_localKummerY` — the auxiliary root `Y` at `p`.
* `Rigidity.RET.localKummerY_notMem` — `Y` is a unit at every place above `p`.
* `Rigidity.RET.local_pow_dvd_map_placeP` — the place above `p` occurs to the power
  `n / gcd(n, c)`.
-/

open Polynomial IntermediateField

noncomputable section


namespace Rigidity.RET

open GeomAKLB

section LocalKummer

attribute [local instance] Ideal.Quotient.field GeomAKLB.instMSA GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instIntegral GeomAKLB.instFaithful
  GeomAKLB.instDedekindB

variable {Ω : Type} [Field Ω] [Algebra (RatFunc k) Ω] [FiniteDimensional (RatFunc k) Ω]
  [IsGalois (RatFunc k) Ω]
  [Algebra (Polynomial k) Ω] [IsScalarTower (Polynomial k) (RatFunc k) Ω]

omit [FiniteDimensional (RatFunc k) Ω] [IsGalois (RatFunc k) Ω] in
/-- Polynomials embed in the cover. -/
theorem algebraMap_poly_injective : Function.Injective (algebraMap (Polynomial k) Ω) := by
  intro x y hxy
  refine IsFractionRing.injective (Polynomial k) (RatFunc k)
    ((algebraMap (RatFunc k) Ω).injective ?_)
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, hxy]

omit [FiniteDimensional (RatFunc k) Ω] [IsGalois (RatFunc k) Ω] in
/-- **The auxiliary root at a point of the radicand.**  With `A = (T - p)^c · U`, `d = gcd(n, c)`,
`m = n/d` and `C = c/d`, the element `Y = w^m / (T - p)^C` is integral and satisfies `Y^d = U`. -/
theorem exists_localKummerY {n : ℕ} [NeZero n] {p : k} {c : ℕ} {A U : Polynomial k}
    (hA : A = (X - C p) ^ c * U) (w : Bring Ω)
    (hw : w ^ n = algebraMap (Polynomial k) (Bring Ω) A) :
    ∃ Y : Bring Ω, Y ^ (Nat.gcd n c) = algebraMap (Polynomial k) (Bring Ω) U ∧
      Y * (algebraMap (Polynomial k) (Bring Ω) (X - C p)) ^ (c / Nat.gcd n c)
        = w ^ (n / Nat.gcd n c) := by
  set d : ℕ := Nat.gcd n c with hddef
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_left _ (NeZero.pos n)
  set m : ℕ := n / d with hmdef
  set Cc : ℕ := c / d with hCdef
  have hmd : m * d = n := Nat.div_mul_cancel (Nat.gcd_dvd_left n c)
  have hCd : Cc * d = c := Nat.div_mul_cancel (Nat.gcd_dvd_right n c)
  set P : Ω := algebraMap (Polynomial k) Ω (X - C p) with hPdef
  have hP0 : P ≠ 0 := by
    rw [hPdef, Ne, map_eq_zero_iff _ algebraMap_poly_injective]
    exact X_sub_C_ne_zero p
  have hwΩ : (w : Ω) ^ n = algebraMap (Polynomial k) Ω A := by
    have := congrArg (fun x : Bring Ω => (x : Ω)) hw
    simpa using this
  set Ywit : Ω := (w : Ω) ^ m / P ^ Cc with hYwitdef
  have h1 : (w : Ω) ^ (m * d) = P ^ (Cc * d) * algebraMap (Polynomial k) Ω U := by
    rw [hmd, hCd, hwΩ, hA, map_mul, map_pow, hPdef]
  have hYd : Ywit ^ d = algebraMap (Polynomial k) Ω U := by
    rw [hYwitdef, div_pow, ← pow_mul, ← pow_mul, h1,
      mul_div_cancel_left₀ _ (pow_ne_zero _ hP0)]
  have hYint : IsIntegral (Polynomial k) Ywit :=
    IsIntegral.of_pow hd0 (hYd ▸ isIntegral_algebraMap)
  refine ⟨⟨Ywit, hYint⟩, ?_, ?_⟩
  · apply Subtype.ext
    rw [Subalgebra.coe_pow, Subalgebra.coe_algebraMap]
    exact hYd
  · apply Subtype.ext
    rw [Submonoid.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_algebraMap, Subalgebra.coe_pow]
    show Ywit * P ^ Cc = (w : Ω) ^ m
    rw [hYwitdef, div_mul_cancel₀ _ (pow_ne_zero _ hP0)]

omit [Algebra (RatFunc k) Ω] [FiniteDimensional (RatFunc k) Ω] [IsGalois (RatFunc k) Ω]
  [IsScalarTower (Polynomial k) (RatFunc k) Ω] in
/-- The auxiliary root at `p` is a unit at every place above `p`. -/
theorem localKummerY_notMem {p : k} {U : Polynomial k} (hU : U.eval p ≠ 0)
    (Q : Ideal (Bring Ω)) [Q.IsMaximal] [Q.LiesOver (placeP p)]
    {Y : Bring Ω} {d : ℕ} (hd0 : 0 < d)
    (hYd : Y ^ d = algebraMap (Polynomial k) (Bring Ω) U) : Y ∉ Q := by
  intro hmem
  refine notMem_of_eval_ne_zero (Ω := Ω) (t := p) (b := U) hU Q ?_
  rw [← hYd]
  exact Ideal.pow_mem_of_mem Q hmem d hd0

/-- **A Kummer cover is ramified to order `n / gcd(n, c)` at a point of multiplicity `c` in the
radicand.** -/
theorem local_pow_dvd_map_placeP {n : ℕ} [NeZero n] {p : k} {c : ℕ} {A U : Polynomial k}
    (hA : A = (X - C p) ^ c * U) (hU : U.eval p ≠ 0) (w : Bring Ω)
    (hw : w ^ n = algebraMap (Polynomial k) (Bring Ω) A)
    (Q : Ideal (Bring Ω)) [hQm : Q.IsMaximal] [Q.LiesOver (placeP p)] :
    Q ^ (n / Nat.gcd n c) ∣ Ideal.map (algebraMap (Polynomial k) (Bring Ω)) (placeP p) := by
  haveI := hQm.isPrime
  have hQ0 : Q ≠ ⊥ := Q_ne_bot Ω p Q
  have hprime : Prime Q := Ideal.prime_of_isPrime hQ0 hQm.isPrime
  set d : ℕ := Nat.gcd n c with hddef
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_left _ (NeZero.pos n)
  set m : ℕ := n / d with hmdef
  set Cc : ℕ := c / d with hCdef
  have hmd : m * d = n := Nat.div_mul_cancel (Nat.gcd_dvd_left n c)
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => (NeZero.ne n) (by rw [← hmd, h, zero_mul])
  -- the uniformizer at `p` lies in `Q`
  set PB : Bring Ω := algebraMap (Polynomial k) (Bring Ω) (X - C p) with hPBdef
  have hPBQ : PB ∈ Q := by
    have hover : placeP p = Q.comap (algebraMap (Polynomial k) (Bring Ω)) :=
      Ideal.LiesOver.over
    have hmem : (X - C p : Polynomial k) ∈ placeP p := Ideal.mem_span_singleton_self _
    rw [hover] at hmem
    exact hmem
  have hmapeq : Ideal.map (algebraMap (Polynomial k) (Bring Ω)) (placeP p)
      = Ideal.span {PB} := by
    rw [placeP, Ideal.map_span, Set.image_singleton]
  rw [hmapeq]
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · have hm1 : m = 1 := by omega
    rw [hm1, pow_one]
    exact Ideal.dvd_iff_le.mpr (by rwa [Ideal.span_le, Set.singleton_subset_iff])
  -- the auxiliary root, a unit at the place
  obtain ⟨Y, hYd, hYmul⟩ := exists_localKummerY (Ω := Ω) hA w hw
  have hYQ : Y ∉ Q := localKummerY_notMem hU Q hd0 hYd
  set P : Ω := algebraMap (Polynomial k) Ω (X - C p) with hPdef
  have hP0 : P ≠ 0 := by
    rw [hPdef, Ne, map_eq_zero_iff _ algebraMap_poly_injective]
    exact X_sub_C_ne_zero p
  have hYmulΩ : (Y : Ω) * P ^ Cc = (w : Ω) ^ m := by
    have := congrArg (fun x : Bring Ω => (x : Ω)) hYmul
    simpa [hPdef] using this
  -- Bézout: `C x = m q + 1`
  have hcop : Nat.Coprime m Cc := Nat.coprime_div_gcd_div_gcd hd0
  obtain ⟨x, -, hx⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop.symm hm2
  set q : ℕ := Cc * x / m with hqdef
  have hCx : Cc * x = m * q + 1 := by
    conv_lhs => rw [← Nat.div_add_mod (Cc * x) m]
    rw [hx]
  -- the element of valuation one at the place
  set zw : Ω := (w : Ω) ^ x / P ^ q with hzwdef
  have hnum : (w : Ω) ^ (x * m) = (Y : Ω) ^ x * P ^ (m * q + 1) := by
    rw [mul_comm x m, pow_mul, ← hYmulΩ, mul_pow, ← pow_mul, hCx]
  have hzpow : zw ^ m = (Y : Ω) ^ x * P := by
    have hPm : (P : Ω) ^ (q * m) ≠ 0 := pow_ne_zero _ hP0
    rw [hzwdef, div_pow, ← pow_mul, ← pow_mul, hnum, eq_comm, eq_div_iff hPm, pow_add, pow_one,
      mul_comm q m]
    ring
  have hzint : IsIntegral (Polynomial k) zw :=
    IsIntegral.of_pow hm0 (by rw [hzpow]; exact (IsIntegral.pow Y.2 x).mul isIntegral_algebraMap)
  set z : Bring Ω := ⟨zw, hzint⟩ with hzdef
  have hzB : z ^ m = Y ^ x * PB := by
    apply Subtype.ext
    rw [Subalgebra.coe_pow, Submonoid.coe_mul, Subalgebra.coe_pow, hPBdef,
      Subalgebra.coe_algebraMap]
    exact hzpow
  have hzQ : z ∈ Q := by
    refine (‹Q.IsPrime›).mem_of_pow_mem m ?_
    rw [hzB]
    exact Ideal.mul_mem_left _ _ hPBQ
  have h1 : Q ∣ Ideal.span {z} :=
    Ideal.dvd_iff_le.mpr (by rwa [Ideal.span_le, Set.singleton_subset_iff])
  have h2 : Q ^ m ∣ Ideal.span {Y ^ x} * Ideal.span {PB} := by
    have hp := pow_dvd_pow_of_dvd h1 m
    rwa [Ideal.span_singleton_pow, hzB, ← Ideal.span_singleton_mul_span_singleton] at hp
  have hnotY : ¬ Q ∣ Ideal.span {Y ^ x} := by
    intro hdvd
    have hmem : Y ^ x ∈ Q := Ideal.dvd_iff_le.mp hdvd (Ideal.mem_span_singleton_self _)
    exact hYQ ((‹Q.IsPrime›).mem_of_pow_mem x hmem)
  exact hprime.pow_dvd_of_dvd_mul_left m hnotY h2

end LocalKummer

end Rigidity.RET

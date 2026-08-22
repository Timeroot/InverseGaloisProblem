import Mathlib

/-!
# Every rational number is a square in a cyclotomic field

This file gives the concrete, embedding-free form of the Kronecker–Weber theorem for quadratic
fields: for every `d : ℚ` there is a nonzero `m : ℕ` such that `d` becomes a square in the
cyclotomic field `CyclotomicField m ℚ`.

The proof is the classical one, assembled from three sources of square roots inside a field `K`
of characteristic zero equipped with a primitive `m`-th root of unity `ζ`:

* a primitive fourth root of unity squares to `-1`, so `-1` is a square as soon as `4 ∣ m`;
* if `η` is a primitive eighth root of unity then `(η + η⁻¹) ^ 2 = 2`, so `2` is a square as
  soon as `8 ∣ m`;
* for an odd prime `p` dividing `m`, the quadratic Gauss sum attached to the quadratic character
  of `ZMod p` and the additive character `a ↦ ζ ^ a` squares to `±p`; combined with the square
  root of `-1` this makes `p` itself a square.

Multiplicativity then produces a square root of every integer whose prime divisors divide `m`,
and writing `d = (d.num * d.den) / d.den ^ 2` reduces the rational case to the integer one.
Taking `m = 8 * (d.num.natAbs * d.den)` satisfies all the divisibility requirements.

## Main results

* `InverseGalois.CFT.isSquare_two_of_isPrimitiveRoot_eight`: `2` is a square in any field
  containing a primitive eighth root of unity.
* `InverseGalois.CFT.isSquare_natCast_odd_prime_of_isPrimitiveRoot`: an odd prime `p` is a square
  in a characteristic-zero field containing a primitive `p`-th root of unity and a square root
  of `-1`.
* `InverseGalois.CFT.isSquare_intCast_of_isPrimitiveRoot`: an integer all of whose prime divisors
  divide `m` is a square in a characteristic-zero field with a primitive `m`-th root of unity,
  provided `8 ∣ m`.
* `InverseGalois.CFT.exists_sq_eq_ratCast_of_isPrimitiveRoot`: the same statement for a rational
  number, in terms of its numerator and denominator.
* `InverseGalois.CFT.exists_sq_eq_cyclotomicField_num_den`: an explicit conductor, namely
  `8 * (d.num.natAbs * d.den)`, works for a nonzero rational `d`.
* `InverseGalois.CFT.exists_sq_eq_cyclotomicField`: every rational number is a square in some
  cyclotomic field over `ℚ`.
* `InverseGalois.CFT.exists_algHom_cyclotomicField_of_finrank_two`: every quadratic number field
  admits a `ℚ`-algebra map into some cyclotomic field over `ℚ`.

-/

namespace InverseGalois.CFT

open AddChar MulChar

variable {K : Type*} [Field K]

/-- A primitive fourth root of unity squares to `-1`: its square is a primitive second root of
unity, and `-1` is the only one. -/
theorem sq_eq_neg_one_of_isPrimitiveRoot_four {i : K} (hi : IsPrimitiveRoot i 4) : i ^ 2 = -1 :=
  (hi.pow (by norm_num) (show (4 : ℕ) = 2 * 2 by norm_num)).eq_neg_one_of_two_right

/-- `-1` is a square in any field containing a primitive fourth root of unity. -/
theorem isSquare_neg_one_of_isPrimitiveRoot_four {i : K} (hi : IsPrimitiveRoot i 4) :
    IsSquare (-1 : K) :=
  ⟨i, by rw [← sq, sq_eq_neg_one_of_isPrimitiveRoot_four hi]⟩

/-- `2` is a square in any field containing a primitive eighth root of unity `η`: an explicit
square root is `η + η ^ 7 = η + η⁻¹`. -/
theorem isSquare_two_of_isPrimitiveRoot_eight {η : K} (hη : IsPrimitiveRoot η 8) :
    IsSquare (2 : K) := by
  have h4 : η ^ 4 = -1 :=
    (hη.pow (by norm_num) (show (8 : ℕ) = 4 * 2 by norm_num)).eq_neg_one_of_two_right
  refine ⟨η + η ^ 7, ?_⟩
  linear_combination (-(η ^ 2 * (η ^ 8 - η ^ 4 + 1) + 2 * (η ^ 4 - 1))) * h4

/-- A primitive `m`-th root of unity yields a primitive `k`-th root of unity for every divisor
`k` of `m`. -/
theorem isPrimitiveRoot_pow_div {m k : ℕ} (hm : m ≠ 0) {ζ : K} (hζ : IsPrimitiveRoot ζ m)
    (hk : k ∣ m) : IsPrimitiveRoot (ζ ^ (m / k)) k :=
  hζ.pow (Nat.pos_of_ne_zero hm) (Nat.div_mul_cancel hk).symm

variable [CharZero K]

/-- An odd prime `p` is a square in a field of characteristic zero that contains a primitive
`p`-th root of unity and a square root of `-1`. The square root is built from the quadratic
Gauss sum, whose square is `±p`. -/
theorem isSquare_natCast_odd_prime_of_isPrimitiveRoot {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hneg : IsSquare (-1 : K)) : IsSquare ((p : K)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hinj : Function.Injective (algebraMap ℤ K) := by
    intro a b h
    simpa [eq_intCast] using h
  set ψ : AddChar (ZMod p) K := zmodChar p hζ.pow_eq_one
  have hψ : ψ.IsPrimitive := zmodChar_primitive_of_primitive_root p hζ
  set χ : MulChar (ZMod p) K := (quadraticChar (ZMod p)).ringHomComp (algebraMap ℤ K)
  have hχ1 : χ ≠ 1 := (MulChar.ringHomComp_ne_one_iff hinj).mpr
    (quadraticChar_ne_one (by rw [ZMod.ringChar_zmod_n]; exact hp2))
  have hχ2 : χ.IsQuadratic := (quadraticChar_isQuadratic (ZMod p)).comp _
  have hsq := gaussSum_sq hχ1 hχ2 hψ
  rw [ZMod.card] at hsq
  have hc : χ (-1) * χ (-1) = 1 := by rw [← map_mul, neg_mul_neg, one_mul, MulChar.map_one]
  rcases mul_self_eq_one_iff.mp hc with h | h
  · rw [h, one_mul] at hsq
    exact ⟨gaussSum χ ψ, by rw [← hsq]; ring⟩
  · rw [h] at hsq
    have hp' : (p : K) = -1 * gaussSum χ ψ ^ 2 := by linear_combination hsq
    rw [hp']
    exact hneg.mul ⟨gaussSum χ ψ, by ring⟩

/-- Every prime divisor of `m` is a square in a field of characteristic zero containing a
primitive `m`-th root of unity, provided `8 ∣ m`. -/
theorem isSquare_natCast_prime_of_isPrimitiveRoot {m : ℕ} (hm : m ≠ 0) {ζ : K}
    (hζ : IsPrimitiveRoot ζ m) (h8 : 8 ∣ m) {q : ℕ} (hq : q.Prime) (hqm : q ∣ m) :
    IsSquare ((q : K)) := by
  have hneg : IsSquare (-1 : K) := isSquare_neg_one_of_isPrimitiveRoot_four
    (isPrimitiveRoot_pow_div hm hζ (dvd_trans (by norm_num) h8))
  rcases eq_or_ne q 2 with rfl | hq2
  · simpa using isSquare_two_of_isPrimitiveRoot_eight (isPrimitiveRoot_pow_div hm hζ h8)
  · exact isSquare_natCast_odd_prime_of_isPrimitiveRoot hq hq2
      (isPrimitiveRoot_pow_div hm hζ hqm) hneg

/-- A natural number all of whose prime divisors divide `m` is a square in a field of
characteristic zero containing a primitive `m`-th root of unity, provided `8 ∣ m`. -/
theorem isSquare_natCast_of_isPrimitiveRoot {m : ℕ} (hm : m ≠ 0) {ζ : K}
    (hζ : IsPrimitiveRoot ζ m) (h8 : 8 ∣ m) (n : ℕ)
    (hn : ∀ q : ℕ, q.Prime → q ∣ n → q ∣ m) : IsSquare ((n : K)) := by
  revert hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases eq_or_ne n 0 with rfl | hn0
    · exact ⟨0, by simp⟩
    rcases eq_or_ne n 1 with rfl | hn1
    · exact ⟨1, by simp⟩
    have hq : n.minFac.Prime := Nat.minFac_prime hn1
    have hk : n.minFac * (n / n.minFac) = n := Nat.mul_div_cancel' (Nat.minFac_dvd n)
    have hklt : n / n.minFac < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn0) hq.one_lt
    have h1 : IsSquare ((n / n.minFac : ℕ) : K) :=
      ih _ hklt fun r hr hrd => hn r hr (hrd.trans (Nat.div_dvd_of_dvd (Nat.minFac_dvd n)))
    have h2 : IsSquare ((n.minFac : ℕ) : K) :=
      isSquare_natCast_prime_of_isPrimitiveRoot hm hζ h8 hq (hn _ hq (Nat.minFac_dvd n))
    have h3 := h2.mul h1
    rwa [← Nat.cast_mul, hk] at h3

/-- An integer all of whose prime divisors divide `m` is a square in a field of characteristic
zero containing a primitive `m`-th root of unity, provided `8 ∣ m`. -/
theorem isSquare_intCast_of_isPrimitiveRoot {m : ℕ} (hm : m ≠ 0) {ζ : K}
    (hζ : IsPrimitiveRoot ζ m) (h8 : 8 ∣ m) (n : ℤ)
    (hn : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ n → q ∣ m) : IsSquare ((n : K)) := by
  have hneg : IsSquare (-1 : K) := isSquare_neg_one_of_isPrimitiveRoot_four
    (isPrimitiveRoot_pow_div hm hζ (dvd_trans (by norm_num) h8))
  have h := isSquare_natCast_of_isPrimitiveRoot hm hζ h8 n.natAbs fun q hq hqd =>
    hn q hq (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hqd))
  rcases Int.natAbs_eq n with hnn | hnn
  · rw [hnn, Int.cast_natCast]
    exact h
  · rw [hnn, Int.cast_neg, Int.cast_natCast]
    have h' := hneg.mul h
    rwa [neg_one_mul] at h'

/-- A rational number whose numerator and denominator only involve primes dividing `m` is a
square in a field of characteristic zero containing a primitive `m`-th root of unity, provided
`8 ∣ m`. -/
theorem exists_sq_eq_ratCast_of_isPrimitiveRoot {m : ℕ} (hm : m ≠ 0) {ζ : K}
    (hζ : IsPrimitiveRoot ζ m) (h8 : 8 ∣ m) (d : ℚ)
    (hd : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ d.num * d.den → q ∣ m) : ∃ x : K, x ^ 2 = (d : K) := by
  obtain ⟨y, hy⟩ := isSquare_intCast_of_isPrimitiveRoot hm hζ h8 (d.num * d.den) hd
  have hden : ((d.den : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr d.den_nz
  refine ⟨y / (d.den : K), ?_⟩
  have h2 : y ^ 2 = ((d.num * (d.den : ℤ) : ℤ) : K) := by rw [hy]; ring
  rw [div_pow, h2, Rat.cast_def]
  push_cast
  field_simp

/-- A nonzero rational number `d` is a square in the cyclotomic field of conductor
`8 * (d.num.natAbs * d.den)`. -/
theorem exists_sq_eq_cyclotomicField_num_den {d : ℚ} (hd : d ≠ 0) :
    ∃ x : CyclotomicField (8 * (d.num.natAbs * d.den)) ℚ,
      x ^ 2 = algebraMap ℚ (CyclotomicField (8 * (d.num.natAbs * d.den)) ℚ) d := by
  have hm : 8 * (d.num.natAbs * d.den) ≠ 0 := Nat.mul_ne_zero (by norm_num)
    (Nat.mul_ne_zero (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hd)) d.den_nz)
  haveI : NeZero (8 * (d.num.natAbs * d.den)) := ⟨hm⟩
  haveI : NeZero ((8 * (d.num.natAbs * d.den) : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hm⟩
  have hz := IsCyclotomicExtension.zeta_spec (8 * (d.num.natAbs * d.den)) ℚ
    (CyclotomicField (8 * (d.num.natAbs * d.den)) ℚ)
  have h8 : 8 ∣ 8 * (d.num.natAbs * d.den) := Dvd.intro _ rfl
  have hd' : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ d.num * d.den → q ∣ 8 * (d.num.natAbs * d.den) := by
    intro q _ hqd
    have h1 : q ∣ d.num.natAbs * d.den := by
      simpa [Int.natAbs_mul] using Int.natAbs_dvd_natAbs.mpr hqd
    exact h1.mul_left 8
  obtain ⟨x, hx⟩ := exists_sq_eq_ratCast_of_isPrimitiveRoot hm hz h8 d hd'
  exact ⟨x, by rw [hx, eq_ratCast]⟩

/-- Every rational number is a square in some cyclotomic field over `ℚ`. -/
theorem exists_sq_eq_cyclotomicField (d : ℚ) :
    ∃ m : ℕ, m ≠ 0 ∧ ∃ x : CyclotomicField m ℚ,
      x ^ 2 = algebraMap ℚ (CyclotomicField m ℚ) d := by
  rcases eq_or_ne d 0 with rfl | hd
  · exact ⟨1, one_ne_zero, 0, by simp⟩
  refine ⟨8 * (d.num.natAbs * d.den), Nat.mul_ne_zero (by norm_num)
    (Nat.mul_ne_zero (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hd)) d.den_nz), ?_⟩
  exact exists_sq_eq_cyclotomicField_num_den hd

open Polynomial in
/-- Every quadratic number field embeds into a cyclotomic field over `ℚ`. A primitive element
`γ` has a monic quadratic minimal polynomial `X ^ 2 + b * X + c`; completing the square, a
square root of `b ^ 2 / 4 - c` in a cyclotomic field produces a root of that polynomial there,
hence a `ℚ`-algebra map. -/
theorem exists_algHom_cyclotomicField_of_finrank_two (L : Type*) [Field L] [NumberField L]
    (h : Module.finrank ℚ L = 2) :
    ∃ m : ℕ, m ≠ 0 ∧ Nonempty (L →ₐ[ℚ] CyclotomicField m ℚ) := by
  obtain ⟨γ, hS⟩ := Field.exists_primitive_element ℚ L
  have hγi : IsIntegral ℚ γ := IsIntegral.of_finite ℚ γ
  set p := minpoly ℚ γ with hpdef
  have hdeg : p.natDegree = 2 := by
    have h1 := IntermediateField.adjoin.finrank hγi
    rw [hS, IntermediateField.finrank_top'] at h1
    exact h1 ▸ h
  have hc2 : p.coeff 2 = 1 := by
    have h2 := (minpoly.monic hγi).coeff_natDegree
    rwa [← hpdef, hdeg] at h2
  obtain ⟨b, c, hpe⟩ : ∃ b c : ℚ, p = C c + C b * X + X ^ 2 := by
    refine ⟨p.coeff 1, p.coeff 0, ?_⟩
    have h3 := p.as_sum_range_C_mul_X_pow' (n := 3) (by omega)
    simp [Finset.sum_range_succ, hc2] at h3
    linear_combination (norm := ring_nf) h3
  obtain ⟨m, hm, x, hx⟩ := exists_sq_eq_cyclotomicField (b ^ 2 / 4 - c)
  refine ⟨m, hm, ?_⟩
  simp only [eq_ratCast] at hx
  have hroot : aeval (x - (b / 2 : ℚ) : CyclotomicField m ℚ) p = 0 := by
    rw [hpe]
    simp only [map_add, map_mul, map_pow, aeval_C, aeval_X, eq_ratCast]
    push_cast at hx ⊢
    linear_combination hx
  have e : L ≃ₐ[ℚ] AdjoinRoot p :=
    (((IntermediateField.equivOfEq hS).trans IntermediateField.topEquiv).symm).trans
      (IntermediateField.adjoinRootEquivAdjoin ℚ hγi).symm
  exact ⟨(AdjoinRoot.liftAlgHom p (Algebra.ofId ℚ (CyclotomicField m ℚ)) _ hroot).comp e.toAlgHom⟩

end InverseGalois.CFT

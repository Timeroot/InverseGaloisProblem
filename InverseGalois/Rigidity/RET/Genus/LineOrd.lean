/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Genus.Ord

/-!
# Orders of rational functions at the points of the affine line

The height-one primes of `F[X]` at which a rational function is measured are, for `F`
algebraically closed, exactly the points of `F`: the prime at `t` is `(X - t)`.  The order of a
polynomial there is its multiplicity as a root, and summing that multiplicity over all points of
the line recovers the degree, because over an algebraically closed field a polynomial is the
product of its linear factors.

For a rational function the same sum is the difference of the degrees of numerator and
denominator, that is, `RatFunc.intDegree`.  This is the affine half of the statement that the
divisor of a rational function has degree zero; the missing half lives at infinity.

## Main definitions

* `Rigidity.RET.pointPlace` — the height-one prime `(X - t)` of `F[X]`.

## Main results

* `Rigidity.RET.ord_polynomial` — the order of a polynomial at `t` is its root multiplicity.
* `Rigidity.RET.finsum_ord_polynomial` — the orders of a polynomial sum to its degree.
* `Rigidity.RET.finsum_ord_ratFunc` — the orders of a rational function sum to its `intDegree`.
-/

open IsDedekindDomain Polynomial

noncomputable section


namespace Rigidity.RET

variable {F : Type*} [Field F]

/-- **The point `t` of the affine line, as a height-one prime of `F[X]`.** -/
def pointPlace (t : F) : HeightOneSpectrum (Polynomial F) where
  asIdeal := Ideal.span {X - C t}
  isPrime := (Ideal.span_singleton_prime (X_sub_C_ne_zero t)).mpr (prime_X_sub_C t)
  ne_bot := by
    simpa [Ideal.span_singleton_eq_bot] using X_sub_C_ne_zero t

@[simp]
theorem pointPlace_asIdeal (t : F) : (pointPlace t).asIdeal = Ideal.span {X - C t} := rfl

/-- Distinct points of the line are distinct places. -/
theorem pointPlace_injective : Function.Injective (pointPlace (F := F)) := by
  intro s t hst
  have h : (X - C s : Polynomial F) ∈ Ideal.span {(X - C t : Polynomial F)} := by
    rw [← pointPlace_asIdeal, ← hst, pointPlace_asIdeal]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp h
  have := congrArg (Polynomial.eval t) hc
  simpa [sub_eq_zero, eq_comm] using this

/-- A nonzero polynomial is nonzero in the field of rational functions. -/
theorem algebraMap_ne_zero {p : Polynomial F} (hp : p ≠ 0) :
    algebraMap (Polynomial F) (RatFunc F) p ≠ 0 :=
  fun h => hp (IsFractionRing.to_map_eq_zero_iff.mp h)

/-- The uniformizer at `t` has order one there. -/
@[simp]
theorem ord_X_sub_C_self (t : F) :
    ord (RatFunc F) (pointPlace t) (algebraMap (Polynomial F) (RatFunc F) (X - C t)) = 1 := by
  rw [ord_algebraMap]
  have : (Ideal.span {(X - C t : Polynomial F)}) = (pointPlace t).asIdeal := rfl
  rw [this]
  exact FractionalIdeal.count_self (K := RatFunc F) (v := pointPlace t)

/-- A polynomial not divisible by the uniformizer at `t` has order zero there. -/
theorem ord_eq_zero_of_not_dvd {t : F} {q : Polynomial F} (hq : q ≠ 0)
    (hdvd : ¬ (X - C t : Polynomial F) ∣ q) :
    ord (RatFunc F) (pointPlace t) (algebraMap (Polynomial F) (RatFunc F) q) = 0 := by
  refine le_antisymm ?_ (ord_nonneg _ _)
  by_contra hlt
  push_neg at hlt
  exact hdvd (Ideal.mem_span_singleton.mp
    ((mem_iff_ord_pos (K := RatFunc F) (pointPlace t) hq).mpr hlt))

/-- **The order of a polynomial at a point of the line is its multiplicity as a root there.** -/
theorem ord_polynomial (t : F) {p : Polynomial F} (hp : p ≠ 0) :
    ord (RatFunc F) (pointPlace t) (algebraMap (Polynomial F) (RatFunc F) p)
      = p.rootMultiplicity t := by
  obtain ⟨q, hq, hqdvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp t
  have hqne : q ≠ 0 := by rintro rfl; simp at hq; exact hp hq
  have hxne : (X - C t : Polynomial F) ≠ 0 := X_sub_C_ne_zero t
  conv_lhs => rw [hq]
  rw [map_mul, map_pow,
    ord_mul _ (pow_ne_zero _ (algebraMap_ne_zero hxne)) (algebraMap_ne_zero hqne),
    ord_pow _ (algebraMap_ne_zero hxne), ord_X_sub_C_self, ord_eq_zero_of_not_dvd hqne hqdvd]
  simp

/-- **The orders of a polynomial at the points of the line sum to its degree.** -/
theorem finsum_ord_polynomial [IsAlgClosed F] {p : Polynomial F} (hp : p ≠ 0) :
    ∑ᶠ t : F, ord (RatFunc F) (pointPlace t) (algebraMap (Polynomial F) (RatFunc F) p)
      = p.natDegree := by
  classical
  have hsupp : (Function.support fun t : F =>
      ord (RatFunc F) (pointPlace t) (algebraMap (Polynomial F) (RatFunc F) p))
      ⊆ (p.roots.toFinset : Set F) := by
    intro t ht
    simp only [Function.mem_support, ord_polynomial t hp, ne_eq, Int.natCast_eq_zero] at ht
    have hpos : 0 < p.roots.count t := by
      rw [Polynomial.count_roots]; exact Nat.pos_of_ne_zero ht
    exact Finset.mem_coe.mpr (Multiset.mem_toFinset.mpr (Multiset.count_pos.mp hpos))
  rw [finsum_eq_finset_sum_of_support_subset _ hsupp]
  have hcard : p.roots.card = p.natDegree :=
    (Polynomial.splits_iff_card_roots (f := p)).mp (IsAlgClosed.splits p)
  calc ∑ t ∈ p.roots.toFinset,
        ord (RatFunc F) (pointPlace t) (algebraMap (Polynomial F) (RatFunc F) p)
      = ∑ t ∈ p.roots.toFinset, (p.roots.count t : ℤ) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [ord_polynomial t hp, Polynomial.count_roots]
    _ = ((∑ t ∈ p.roots.toFinset, p.roots.count t : ℕ) : ℤ) := by push_cast; ring
    _ = (p.natDegree : ℤ) := by rw [Multiset.toFinset_sum_count_eq, hcard]

/-- **The orders of a rational function at the points of the line sum to its degree**, the
difference of the degrees of its numerator and denominator. -/
theorem finsum_ord_ratFunc [IsAlgClosed F] {g : RatFunc F} (hg : g ≠ 0) :
    ∑ᶠ t : F, ord (RatFunc F) (pointPlace t) g = g.intDegree := by
  classical
  have hnum : g.num ≠ 0 := RatFunc.num_ne_zero hg
  have hden : g.denom ≠ 0 := RatFunc.denom_ne_zero g
  have hgeq : g = algebraMap (Polynomial F) (RatFunc F) g.num /
      algebraMap (Polynomial F) (RatFunc F) g.denom := by
    simp [RatFunc.num_div_denom g]
  have hord : ∀ t : F, ord (RatFunc F) (pointPlace t) g
      = ord (RatFunc F) (pointPlace t) (algebraMap (Polynomial F) (RatFunc F) g.num)
        - ord (RatFunc F) (pointPlace t) (algebraMap (Polynomial F) (RatFunc F) g.denom) := by
    intro t
    conv_lhs => rw [hgeq]
    rw [ord_div _ (algebraMap_ne_zero hnum) (algebraMap_ne_zero hden)]
  have hfinnum : (Function.support fun t : F =>
      ord (RatFunc F) (pointPlace t) (algebraMap (Polynomial F) (RatFunc F) g.num)).Finite := by
    refine Set.Finite.subset g.num.roots.toFinset.finite_toSet fun t ht => ?_
    simp only [Function.mem_support, ord_polynomial t hnum, ne_eq, Int.natCast_eq_zero] at ht
    have hpos : 0 < g.num.roots.count t := by
      rw [Polynomial.count_roots]; exact Nat.pos_of_ne_zero ht
    exact Finset.mem_coe.mpr (Multiset.mem_toFinset.mpr (Multiset.count_pos.mp hpos))
  have hfinden : (Function.support fun t : F =>
      ord (RatFunc F) (pointPlace t) (algebraMap (Polynomial F) (RatFunc F) g.denom)).Finite := by
    refine Set.Finite.subset g.denom.roots.toFinset.finite_toSet fun t ht => ?_
    simp only [Function.mem_support, ord_polynomial t hden, ne_eq, Int.natCast_eq_zero] at ht
    have hpos : 0 < g.denom.roots.count t := by
      rw [Polynomial.count_roots]; exact Nat.pos_of_ne_zero ht
    exact Finset.mem_coe.mpr (Multiset.mem_toFinset.mpr (Multiset.count_pos.mp hpos))
  rw [finsum_congr hord, finsum_sub_distrib hfinnum hfinden, finsum_ord_polynomial hnum,
    finsum_ord_polynomial hden, RatFunc.intDegree]

end Rigidity.RET

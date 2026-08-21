import Mathlib

/-!
# Generators of the square classes of the rationals

A function on nonzero rationals that is multiplicative and insensitive to square factors is
determined by its values on `-1` and on the rational primes.  This file supplies the two
elementary ingredients of that reduction: every nonzero rational is an integer times a square,
and every nonzero integer is built from `1`, `-1` and the primes by multiplication.

Both statements are used to reduce an identity between multiplicative symbols — the product
formula for the Hilbert symbol, say — to the finitely many cases in which both arguments are
`-1` or a prime.

## Main results

* `InverseGalois.CFT.exists_intCast_mul_sq`: a nonzero rational is a nonzero integer times the
  square of a nonzero rational.
* `InverseGalois.CFT.Int.induction_on_prime_mul`: an induction principle for nonzero integers,
  with base cases `1` and `-1` and one step for multiplication by a prime.
* `InverseGalois.CFT.Rat.induction_on_prime_mul_sq`: the two combined, for a predicate on nonzero
  rationals that ignores square factors.
-/

namespace InverseGalois.CFT

/-- A nonzero rational is a nonzero integer times the square of a nonzero rational: clearing the
denominator costs one square. -/
theorem exists_intCast_mul_sq {q : ℚ} (hq : q ≠ 0) :
    ∃ (m : ℤ) (c : ℚ), m ≠ 0 ∧ c ≠ 0 ∧ q = (m : ℚ) * c ^ 2 := by
  have hd : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.2 q.den_nz
  refine ⟨q.num * (q.den : ℤ), (q.den : ℚ)⁻¹, ?_, ?_, ?_⟩
  · exact mul_ne_zero (Rat.num_ne_zero.2 hq) (Int.natCast_ne_zero.2 q.den_nz)
  · exact inv_ne_zero hd
  · have hnum := Rat.num_div_den q
    rw [div_eq_iff hd] at hnum
    push_cast
    rw [hnum]
    field_simp

/-- **Multiplicative induction on the nonzero integers.**  A predicate holding at `1` and `-1`
and stable under multiplication by a prime holds at every nonzero integer. -/
theorem Int.induction_on_prime_mul {motive : ℤ → Prop} (one : motive 1) (neg_one : motive (-1))
    (prime_mul : ∀ (p : ℕ) (a : ℤ), p.Prime → a ≠ 0 → motive a → motive ((p : ℤ) * a))
    {n : ℤ} (hn : n ≠ 0) : motive n := by
  have key : ∀ k : ℕ, k ≠ 0 → motive (k : ℤ) ∧ motive (-(k : ℤ)) := by
    intro k
    induction k using induction_on_primes with
    | zero => intro h; exact absurd rfl h
    | one => intro _; exact ⟨by simpa using one, by simpa using neg_one⟩
    | prime_mul p a hp ih =>
      intro hpa
      have ha : a ≠ 0 := by
        rintro rfl
        simp at hpa
      obtain ⟨h1, h2⟩ := ih ha
      have ha' : (a : ℤ) ≠ 0 := Int.natCast_ne_zero.2 ha
      refine ⟨?_, ?_⟩
      · have := prime_mul p (a : ℤ) hp ha' h1
        push_cast
        exact this
      · have := prime_mul p (-(a : ℤ)) hp (neg_ne_zero.2 ha') h2
        push_cast at this ⊢
        simpa using this
  rcases lt_or_gt_of_ne hn with h | h
  · have hk : n.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hn
    have : -((n.natAbs : ℤ)) = n := by omega
    rw [← this]
    exact (key n.natAbs hk).2
  · have hk : n.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hn
    have : ((n.natAbs : ℤ)) = n := by omega
    rw [← this]
    exact (key n.natAbs hk).1

/-- **Multiplicative induction on the nonzero rationals, up to squares.**  A predicate that holds
at `1` and `-1`, is stable under multiplication by a prime, and is insensitive to multiplication
by a nonzero square, holds at every nonzero rational. -/
theorem Rat.induction_on_prime_mul_sq {motive : ℚ → Prop} (one : motive 1) (neg_one : motive (-1))
    (prime_mul : ∀ (p : ℕ) (a : ℚ), p.Prime → a ≠ 0 → motive a → motive ((p : ℚ) * a))
    (sq : ∀ (a c : ℚ), a ≠ 0 → c ≠ 0 → motive a → motive (a * c ^ 2))
    {q : ℚ} (hq : q ≠ 0) : motive q := by
  obtain ⟨m, c, hm, hc, rfl⟩ := exists_intCast_mul_sq hq
  have hmq : ((m : ℚ)) ≠ 0 := Int.cast_ne_zero.2 hm
  refine sq _ _ hmq hc ?_
  refine Int.induction_on_prime_mul (motive := fun n : ℤ => motive (n : ℚ)) ?_ ?_ ?_ hm
  · simpa using one
  · simpa using neg_one
  · intro p a hp ha h
    rw [show (((p : ℤ) * a : ℤ) : ℚ) = (p : ℚ) * (a : ℚ) by push_cast; ring]
    exact prime_mul p (a : ℚ) hp (Int.cast_ne_zero.2 ha) h

end InverseGalois.CFT

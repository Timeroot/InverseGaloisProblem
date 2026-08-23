import Mathlib
import InverseGalois.CFT.Local.LegendreHilbert
import InverseGalois.CFT.SquareClasses

/-!
# The Hilbert symbol of a rational pair at every finite place

A pair of nonzero rationals has a Hilbert symbol at each completion of the rationals.  This file
sets up the family of symbols at the finite places and proves that only finitely many of them are
nontrivial, which is what makes the product over all places meaningful.

The finiteness is elementary.  Modulo squares a nonzero rational is an integer, and at an odd
prime dividing neither of the two integers both arguments are units of the ring of `p`-adic
integers, so the conic has a point already modulo `p`.

## Main results

* `InverseGalois.CFT.hilbertSymbolAt`: the Hilbert symbol of a pair of rationals at a finite
  place.
* `InverseGalois.CFT.hilbertSymbolAt_intCast_eq_one`: it is trivial at an odd prime dividing
  neither integer argument.
* `InverseGalois.CFT.finite_mulSupport_hilbertSymbolAt`: for a fixed pair of nonzero rationals
  the symbol is trivial at all but finitely many finite places.
-/

namespace InverseGalois.CFT

open Local

/-- A prime, viewed as an element of the subtype of primes, is prime. -/
instance Nat.Primes.fact_prime (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- **The Hilbert symbol of a pair of rationals at a finite place.**  Both arguments are sent to
the field of `p`-adic numbers and the local symbol is taken there. -/
noncomputable def hilbertSymbolAt (p : Nat.Primes) (a b : ℚ) : ℤ :=
  hilbertSymbol ((a : ℚ_[(p : ℕ)])) ((b : ℚ_[(p : ℕ)]))

/-- The symbol at a finite place is a sign. -/
theorem hilbertSymbolAt_eq_one_or (p : Nat.Primes) (a b : ℚ) :
    hilbertSymbolAt p a b = 1 ∨ hilbertSymbolAt p a b = -1 :=
  hilbertSymbol_eq_one_or _ _

/-- The symbol at a finite place is symmetric. -/
theorem hilbertSymbolAt_comm (p : Nat.Primes) (a b : ℚ) :
    hilbertSymbolAt p a b = hilbertSymbolAt p b a :=
  hilbertSymbol_comm _ _

/-- The symbol at a finite place is unchanged when its first argument is multiplied by a nonzero
square. -/
theorem hilbertSymbolAt_mul_sq_left (p : Nat.Primes) (a b c : ℚ) (hc : c ≠ 0) :
    hilbertSymbolAt p (a * c ^ 2) b = hilbertSymbolAt p a b := by
  have hc' : ((c : ℚ_[(p : ℕ)])) ≠ 0 := by
    simpa using hc
  unfold hilbertSymbolAt
  push_cast
  exact hilbertSymbol_mul_sq_left _ _ _ hc'

/-- The symbol at a finite place is unchanged when its second argument is multiplied by a nonzero
square. -/
theorem hilbertSymbolAt_mul_sq_right (p : Nat.Primes) (a b c : ℚ) (hc : c ≠ 0) :
    hilbertSymbolAt p a (b * c ^ 2) = hilbertSymbolAt p a b := by
  have hc' : ((c : ℚ_[(p : ℕ)])) ≠ 0 := by
    simpa using hc
  unfold hilbertSymbolAt
  push_cast
  exact hilbertSymbol_mul_sq_right _ _ _ hc'

/-- **At an odd prime dividing neither argument the symbol of two integers is trivial**: two units
of the ring of `p`-adic integers are always isotropic. -/
theorem hilbertSymbolAt_intCast_eq_one {p : Nat.Primes} (hp : (p : ℕ) ≠ 2) {m n : ℤ}
    (hm : ¬ ((p : ℕ) : ℤ) ∣ m) (hn : ¬ ((p : ℕ) : ℤ) ∣ n) :
    hilbertSymbolAt p (m : ℚ) (n : ℚ) = 1 := by
  unfold hilbertSymbolAt
  push_cast
  exact hilbertSymbol_intCast_intCast hp hm hn

/-- The primes dividing a fixed nonzero integer form a finite set. -/
theorem finite_setOf_prime_dvd {m : ℤ} (hm : m ≠ 0) :
    {p : Nat.Primes | ((p : ℕ) : ℤ) ∣ m}.Finite := by
  have hsub : {p : Nat.Primes | ((p : ℕ) : ℤ) ∣ m} ⊆
      ((↑) : Nat.Primes → ℕ) ⁻¹' (m.natAbs.divisors : Set ℕ) := by
    intro p hp
    have hdvd : (p : ℕ) ∣ m.natAbs := by
      have := Int.natAbs_dvd_natAbs.2 hp
      simpa using this
    simp only [Set.mem_preimage, Finset.mem_coe, Nat.mem_divisors]
    exact ⟨hdvd, Int.natAbs_ne_zero.2 hm⟩
  refine Set.Finite.subset ?_ hsub
  exact Set.Finite.preimage (Nat.Primes.coe_nat_injective.injOn) (Finset.finite_toSet _)

/-- **The symbol of a pair of nonzero integers is trivial at all but finitely many finite
places.** -/
theorem finite_mulSupport_hilbertSymbolAt_intCast {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0) :
    (Function.mulSupport fun p : Nat.Primes => hilbertSymbolAt p (m : ℚ) (n : ℚ)).Finite := by
  have hsub : (Function.mulSupport fun p : Nat.Primes => hilbertSymbolAt p (m : ℚ) (n : ℚ)) ⊆
      {p : Nat.Primes | (p : ℕ) = 2} ∪
        ({p : Nat.Primes | ((p : ℕ) : ℤ) ∣ m} ∪ {p : Nat.Primes | ((p : ℕ) : ℤ) ∣ n}) := by
    intro p hp
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hcon
    exact hp (hilbertSymbolAt_intCast_eq_one hcon.1 hcon.2.1 hcon.2.2)
  refine Set.Finite.subset ?_ hsub
  refine Set.Finite.union ?_ (Set.Finite.union (finite_setOf_prime_dvd hm)
    (finite_setOf_prime_dvd hn))
  refine Set.Finite.subset (Set.finite_singleton (⟨2, Nat.prime_two⟩ : Nat.Primes)) ?_
  intro p hp
  exact Nat.Primes.coe_nat_inj p ⟨2, Nat.prime_two⟩ |>.1 hp

/-- **The symbol of a pair of nonzero rationals is trivial at all but finitely many finite
places**: modulo squares the arguments are integers. -/
theorem finite_mulSupport_hilbertSymbolAt {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (Function.mulSupport fun p : Nat.Primes => hilbertSymbolAt p a b).Finite := by
  obtain ⟨m, c, hm, hc, rfl⟩ := exists_intCast_mul_sq ha
  obtain ⟨n, d, hn, hd, rfl⟩ := exists_intCast_mul_sq hb
  have hcongr : ∀ p : Nat.Primes,
      hilbertSymbolAt p ((m : ℚ) * c ^ 2) ((n : ℚ) * d ^ 2)
        = hilbertSymbolAt p (m : ℚ) (n : ℚ) := by
    intro p
    rw [hilbertSymbolAt_mul_sq_left _ _ _ _ hc, hilbertSymbolAt_mul_sq_right _ _ _ _ hd]
  refine Set.Finite.subset (finite_mulSupport_hilbertSymbolAt_intCast hm hn) ?_
  intro p hp
  simpa [Function.mem_mulSupport, hcongr p] using hp

end InverseGalois.CFT

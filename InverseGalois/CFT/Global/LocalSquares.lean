import Mathlib
import InverseGalois.CFT.Global.HilbertPlaces
import InverseGalois.CFT.Global.JacobiNonresidue
import InverseGalois.CFT.Global.SquarefreeCRT
import InverseGalois.CFT.Local.LegendreHilbert
import InverseGalois.CFT.Local.PadicSquares

/-!
# The Hasse principle for squares

A rational number that is a square in every field of `p`-adic numbers is already a square.
Equivalently, the map from the square classes of the rational field to the product of the square
classes of its finite completions is injective; the real place is not needed.

Modulo squares a nonzero rational is a squarefree integer, so the statement to prove is that a
squarefree integer other than `1` fails to be a square in some `ℚ_p`.  A prime `q` at which the
Jacobi symbol of the integer is `-1` does the job: the symbol being nonzero, `q` divides neither
the integer nor, being odd, the discriminant of the situation, so the integer is a unit of the ring
of `q`-adic integers, and such a unit is a square exactly when its residue is.  Dirichlet's theorem
supplies the prime.

## Main results

* `InverseGalois.CFT.exists_prime_not_isSquare_padic`: a squarefree integer other than `1` is not
  a square in some field of `p`-adic numbers.
* `InverseGalois.CFT.isSquare_of_forall_isSquare_padic`: a rational that is a square in every
  field of `p`-adic numbers is a square.
* `InverseGalois.CFT.isSquare_rat_iff_forall_isSquare_padic`: being a square is a purely local
  condition on a rational number.
* `InverseGalois.CFT.nonneg_of_forall_isSquare_padic`: such a rational is in particular
  nonnegative, so the finite places already see the sign.
-/

namespace InverseGalois.CFT

open Local

/-- **Cancelling a square factor from a square.**  If `x c ^ 2` is a square and `c` is nonzero,
then so is `x`. -/
theorem isSquare_of_isSquare_mul_sq {K : Type*} [Field K] {x c : K} (hc : c ≠ 0)
    (h : IsSquare (x * c ^ 2)) : IsSquare x := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d / c, ?_⟩
  field_simp
  linear_combination hd

/-- **A squarefree integer other than `1` is not a square in some field of `p`-adic numbers.**
The prime is one at which the Jacobi symbol of the integer is `-1`. -/
theorem exists_prime_not_isSquare_padic {m : ℤ} (hm : Squarefree m) (hm1 : m ≠ 1) :
    ∃ q : Nat.Primes, ¬ IsSquare ((m : ℚ_[(q : ℕ)])) := by
  obtain ⟨q, hq, hqN, hjac⟩ := exists_prime_jacobiSym_eq_neg_one hm hm1 2
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hns : ¬ IsSquare ((m : ZMod q)) := ZMod.nonsquare_of_jacobiSym_eq_neg_one hjac
  have hnd : ¬ ((q : ℤ) ∣ m) := by
    rintro ⟨k, rfl⟩
    refine hns ?_
    have hz : (((q : ℤ) * k : ℤ) : ZMod q) = 0 := by push_cast; simp
    rw [hz]
    exact ⟨0, by ring⟩
  refine ⟨⟨q, hq⟩, fun hsq => hns ?_⟩
  have hu : IsUnit ((m : ℤ_[q])) := isUnit_intCast_of_not_dvd hnd
  have hsq' : IsSquare ((m : ℤ_[q])) := by
    refine (isSquare_coe_iff hu).1 ?_
    rwa [PadicInt.coe_intCast]
  rw [← toZMod_intCast]
  exact isSquare_toZMod_of_isSquare hsq'

/-- **The Hasse principle for squares.**  A rational number that is a square in every field of
`p`-adic numbers is a square. -/
theorem isSquare_of_forall_isSquare_padic {a : ℚ}
    (h : ∀ p : Nat.Primes, IsSquare ((a : ℚ_[(p : ℕ)]))) : IsSquare a := by
  rcases eq_or_ne a 0 with rfl | ha
  · exact ⟨0, by ring⟩
  obtain ⟨m, c, hm0, hmsf, hc0, hac⟩ := exists_squarefree_intCast_mul_sq ha
  have hm1 : m = 1 := by
    by_contra hne
    obtain ⟨q, hq⟩ := exists_prime_not_isSquare_padic hmsf hne
    refine hq ?_
    have hcq : ((c : ℚ_[(q : ℕ)])) ≠ 0 := by simpa using hc0
    refine isSquare_of_isSquare_mul_sq hcq ?_
    have hp := h q
    rw [hac] at hp
    rwa [show ((((m : ℚ) * c ^ 2 : ℚ)) : ℚ_[(q : ℕ)])
        = ((m : ℚ_[(q : ℕ)])) * ((c : ℚ_[(q : ℕ)])) ^ 2 by push_cast; ring] at hp
  refine ⟨c, ?_⟩
  rw [hac, hm1]
  push_cast
  ring

/-- **Being a square is a purely local condition on a rational number.** -/
theorem isSquare_rat_iff_forall_isSquare_padic {a : ℚ} :
    IsSquare a ↔ ∀ p : Nat.Primes, IsSquare ((a : ℚ_[(p : ℕ)])) := by
  refine ⟨fun h p => ?_, isSquare_of_forall_isSquare_padic⟩
  obtain ⟨c, hc⟩ := h
  exact ⟨((c : ℚ_[(p : ℕ)])), by rw [hc]; push_cast; ring⟩

/-- **The finite places already see the sign.**  A rational number that is a square in every field
of `p`-adic numbers is nonnegative. -/
theorem nonneg_of_forall_isSquare_padic {a : ℚ}
    (h : ∀ p : Nat.Primes, IsSquare ((a : ℚ_[(p : ℕ)]))) : 0 ≤ a := by
  obtain ⟨c, hc⟩ := isSquare_of_forall_isSquare_padic h
  rw [hc]
  exact mul_self_nonneg c

end InverseGalois.CFT

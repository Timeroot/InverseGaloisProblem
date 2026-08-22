import Mathlib
import InverseGalois.CFT.Global.HasseMinkowski

/-!
# The Hasse norm theorem for a quadratic extension of the rationals

A nonzero rational is a norm from `ℚ(√b)` as soon as it is a norm from `ℚ_p(√b)` for every prime
`p`.  This is the Hasse norm theorem in the quadratic case; equivalently it is the theorem of
Albert, Brauer, Hasse and Noether for quaternion algebras over the rational field, since the
quaternion algebra attached to the pair `(a, b)` is split exactly when `a` is a norm from `ℚ(√b)`.

Two observations turn the Hasse principle for ternary forms into this statement.  The first is
that being a norm is the same as having Hilbert symbol one, without any hypothesis on `b` beyond
being nonzero: when `b` is a square the norm form factors as a product of two linear forms and
represents everything, and otherwise this is the usual description of the values of a binary form.
The second is that the condition at the real place is redundant, being forced by reciprocity.

## Main results

* `InverseGalois.CFT.Local.hilbertSymbol_eq_one_iff_exists_sub_sq'`: the symbol against a nonzero
  element is one exactly when the first argument is a value of its norm form.
* `InverseGalois.CFT.exists_sub_sq_iff_forall_local`: the Hasse norm theorem for the quadratic
  extensions of the rational field.
* `InverseGalois.CFT.mem_normSubgroup_sqrtExt_of_forall_local`: the same statement for the norm
  subgroup of the group of units.
-/

open Polynomial

namespace InverseGalois.CFT.Local

variable {K : Type} [Field K] [CharZero K]

/-- **An element is a value of a norm form exactly when the Hilbert symbol is one**, with
no hypothesis on the second argument beyond being nonzero.  If `b` is the square of `c` then the
form `u ^ 2 - b v ^ 2` factors as `(u - c v) (u + c v)` and represents every element. -/
theorem hilbertSymbol_eq_one_iff_exists_sub_sq' {a b : K} (hb : b ≠ 0) :
    hilbertSymbol a b = 1 ↔ ∃ u v : K, a = u ^ 2 - b * v ^ 2 := by
  by_cases hsq : IsSquare b
  · obtain ⟨c, hc⟩ := hsq
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [hc, mul_zero] at hb
      exact hb rfl
    have h2 : (2 : K) ≠ 0 := two_ne_zero
    constructor
    · intro _
      refine ⟨(a + 1) / 2, (a - 1) / (2 * c), ?_⟩
      rw [hc]
      field_simp
      ring
    · intro _
      exact hilbertSymbol_of_isSquare_right _ _ ⟨c, hc⟩
  · exact hilbertSymbol_eq_one_iff_exists_sub_sq hsq

end InverseGalois.CFT.Local

namespace InverseGalois.CFT

open Local

/-- **At a finite place the symbol is one exactly when the first argument is a local norm.** -/
theorem hilbertSymbolAt_eq_one_iff_exists_sub_sq {p : Nat.Primes} {a b : ℚ} (hb : b ≠ 0) :
    hilbertSymbolAt p a b = 1 ↔
      ∃ u v : ℚ_[(p : ℕ)], ((a : ℚ_[(p : ℕ)])) = u ^ 2 - ((b : ℚ_[(p : ℕ)])) * v ^ 2 := by
  have hb' : ((b : ℚ_[(p : ℕ)])) ≠ 0 := by simpa using hb
  exact hilbertSymbol_eq_one_iff_exists_sub_sq' hb'

/-- **The Hasse norm theorem for a quadratic extension of the rational field.**  A nonzero rational
that is a norm from `ℚ_p(√b)` at every prime is already a norm from `ℚ(√b)`; nothing is required at
the real place, reciprocity supplying it. -/
theorem exists_sub_sq_of_forall_local {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hloc : ∀ p : Nat.Primes, ∃ u v : ℚ_[(p : ℕ)],
      ((a : ℚ_[(p : ℕ)])) = u ^ 2 - ((b : ℚ_[(p : ℕ)])) * v ^ 2) :
    ∃ u v : ℚ, a = u ^ 2 - b * v ^ 2 := by
  refine (hilbertSymbol_eq_one_iff_exists_sub_sq' hb).1 ?_
  refine hilbertSymbol_rat_of_forall_finite ha hb fun p => ?_
  exact (hilbertSymbolAt_eq_one_iff_exists_sub_sq hb).2 (hloc p)

/-- **The Hasse norm theorem, as an equivalence.**  Being a norm from a quadratic extension of the
rational field is a purely local condition. -/
theorem exists_sub_sq_iff_forall_local {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (∃ u v : ℚ, a = u ^ 2 - b * v ^ 2) ↔
      ∀ p : Nat.Primes, ∃ u v : ℚ_[(p : ℕ)],
        ((a : ℚ_[(p : ℕ)])) = u ^ 2 - ((b : ℚ_[(p : ℕ)])) * v ^ 2 := by
  refine ⟨fun h p => ?_, exists_sub_sq_of_forall_local ha hb⟩
  obtain ⟨u, v, huv⟩ := h
  refine ⟨((u : ℚ_[(p : ℕ)])), ((v : ℚ_[(p : ℕ)])), ?_⟩
  rw [huv]
  push_cast
  ring

/-- **The Hasse norm theorem for the norm subgroup of the units.** -/
theorem mem_normSubgroup_sqrtExt_of_forall_local {b : ℚ} [Fact (Irreducible (X ^ 2 - C b))]
    (hb : ¬ IsSquare b) (a : ℚˣ)
    (hloc : ∀ p : Nat.Primes, ∃ u v : ℚ_[(p : ℕ)],
      (((a : ℚ) : ℚ_[(p : ℕ)])) = u ^ 2 - ((b : ℚ_[(p : ℕ)])) * v ^ 2) :
    a ∈ normSubgroup ℚ (sqrtExt ℚ b) := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hb ⟨0, by ring⟩
  rw [mem_normSubgroup_sqrtExt_iff_hilbertSymbol hb]
  exact hilbertSymbol_rat_of_forall_finite a.ne_zero hb0 fun p =>
    (hilbertSymbolAt_eq_one_iff_exists_sub_sq hb0).2 (hloc p)

end InverseGalois.CFT

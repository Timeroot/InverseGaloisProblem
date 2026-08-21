/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Wreath.Independence
import InverseGalois.Rigidity.RET.Wreath.RadicandOrd

/-!
# A family of radicands is independent

Pulling a cyclic cover of the line back along a function `θ` of a second cover replaces the
radicand `∏ᵢ (X - tᵢ)^{eᵢ}` by its value at `θ + c`.  Doing this along every conjugate of `θ`
produces one radicand per conjugate, and the whole point of the construction is that these
radicands are *independent* modulo `n`-th powers: no product of them, with exponents not all
divisible by `n`, is an `n`-th power.

Nothing here needs the conjugates to be conjugate.  All that is used is a family `Θ` of elements of
a field over the constants, so the statements are made for an arbitrary such family; the caller
supplies the family of images of a primitive element under the deck transformations.

Independence is certified place by place.  Suppose that for each member `j` of the family and each
branch point `tᵢ` we can find a valuation which sees the `j`-th radicand with value exactly `eᵢ` and
every *other* radicand with value `0`.  Then a relation `yⁿ = ∏ (radicand j)^{m j}` is seen by that
valuation as `n ∣ m j · eᵢ`; ranging over `i` and using that the `eᵢ` have no common factor with `n`
gives `n ∣ m j`.  This is the statement proved here, with the supply of valuations left abstract:
only additivity on nonzero elements is assumed, so any valuation API can feed it.

## Main results

* `Rigidity.RET.Wreath.conjRadicand` — the radicand attached to a member of the family.
* `Rigidity.RET.Wreath.conjRadicand_ne_zero` — a radicand is nonzero.
* `Rigidity.RET.Wreath.isCoprime_gcd_of_gcd_eq_one` — the exponents, cast to the integers, still
  have greatest common divisor coprime to the degree.
* `Rigidity.RET.Wreath.indep_of_private_valuations` — the independence of the radicands.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET.Wreath

open GeomAKLB

variable {F : Type*} [Field F] [Algebra k F]
variable {ι : Type*} {r : ℕ} (Θ : ι → F) (t : Fin r → k) (e : Fin r → ℕ) (c : k)

/-- **The radicand attached to a member of the family**: the multi-point Kummer radicand
`∏ᵢ (X - tᵢ)^{eᵢ}` evaluated at the translate `Θ j + c`. -/
def conjRadicand (j : ι) : F :=
  eval₂ (algebraMap k F) (Θ j + algebraMap k F c) (multiA t e)

theorem conjRadicand_eq (j : ι) :
    conjRadicand Θ t e c j = ∏ i, (Θ j + algebraMap k F c - algebraMap k F (t i)) ^ e i :=
  eval₂_multiA _ _ _ _

theorem conjRadicand_ne_zero {j : ι}
    (hne : ∀ i, Θ j + algebraMap k F c - algebraMap k F (t i) ≠ 0) :
    conjRadicand Θ t e c j ≠ 0 := by
  rw [conjRadicand_eq]
  exact Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hne i)

/-- **Exponents with no common factor with the degree stay coprime to it over the integers.**  A
common divisor of the degree and of the integer greatest common divisor of the exponents divides
each exponent, hence divides their greatest common divisor as natural numbers. -/
theorem isCoprime_gcd_of_gcd_eq_one {n : ℕ} {e : Fin r → ℕ}
    (h : Nat.gcd n (Finset.univ.gcd e) = 1) :
    IsCoprime (n : ℤ) (Finset.univ.gcd fun i => (e i : ℤ)) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  set d : ℕ := Int.gcd (n : ℤ) (Finset.univ.gcd fun i => (e i : ℤ)) with hd
  have hdn : d ∣ n := by
    have : (d : ℤ) ∣ (n : ℤ) := Int.gcd_dvd_left _ _
    exact_mod_cast this
  have hde : ∀ i, d ∣ e i := by
    intro i
    have h1 : (Finset.univ.gcd fun i => (e i : ℤ)) ∣ (e i : ℤ) :=
      Finset.gcd_dvd (Finset.mem_univ i)
    have : (d : ℤ) ∣ (e i : ℤ) := (Int.gcd_dvd_right _ _).trans h1
    exact_mod_cast this
  have : d ∣ Nat.gcd n (Finset.univ.gcd e) :=
    Nat.dvd_gcd hdn (Finset.dvd_gcd fun i _ => hde i)
  rw [h] at this
  exact Nat.dvd_one.mp this

/-- **The radicands are independent modulo `n`-th powers.**  For each member of the family one is
handed a family of valuations, indexed by the branch points, which sees that member's radicand with
the corresponding exponent and every other member's radicand not at all.  A relation exhibiting a
monomial in the radicands as an `n`-th power is then read off by those valuations as a divisibility
`n ∣ m j · eᵢ` for each `i`, and the exponents have no factor in common with `n`. -/
theorem indep_of_private_valuations [Fintype ι] [DecidableEq ι] {n : ℕ}
    (hgcd : Nat.gcd n (Finset.univ.gcd e) = 1)
    (hne : ∀ (j : ι) (i : Fin r), Θ j + algebraMap k F c - algebraMap k F (t i) ≠ 0)
    (V : ι → Fin r → F → ℤ)
    (hVadd : ∀ (j : ι) (i : Fin r) (x y : F), x ≠ 0 → y ≠ 0 →
      V j i (x * y) = V j i x + V j i y)
    (hself : ∀ (j : ι) (i : Fin r), V j i (conjRadicand Θ t e c j) = (e i : ℤ))
    (hother : ∀ (j j' : ι), j' ≠ j → ∀ i : Fin r, V j i (conjRadicand Θ t e c j') = 0)
    (m : ι → ℤ) (y : F) (hy : y ≠ 0)
    (hpow : y ^ n = ∏ j, conjRadicand Θ t e c j ^ m j) (j : ι) :
    (n : ℤ) ∣ m j := by
  refine dvd_of_pow_eq_prod_zpow (fun l => conjRadicand_ne_zero Θ t e c (hne l)) hy hpow j
    Finset.univ (V j) (fun i _ => hVadd j i) (fun i _ l hl => hother j l hl i) ?_
  have : (Finset.univ.gcd fun i => V j i (conjRadicand Θ t e c j))
      = Finset.univ.gcd fun i => (e i : ℤ) :=
    Finset.gcd_congr rfl fun i _ => hself j i
  rw [this]
  exact isCoprime_gcd_of_gcd_eq_one hgcd

end Rigidity.RET.Wreath

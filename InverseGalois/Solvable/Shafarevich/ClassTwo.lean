/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Commutator calculus one layer at a time

Walking up the descending `p`-central series means computing in a group in which the commutators
that arise are central: two elements of one layer commute with each other modulo the next layer,
and their commutator is central there.  In that situation the commutator is bilinear and the `n`-th
power of a product picks up exactly one correction term,

`(x * y) ^ n = x ^ n * y ^ n * ⁅y, x⁆ ^ (n.choose 2)`.

Both facts are recorded in the form they are used: as hypotheses about individual commutators
commuting with individual elements, rather than about the nilpotency class of the whole group, so
that they apply verbatim inside a quotient by a term of the series.

## Main results

* `InverseGalois.Shafarevich.commutatorElement_mul_left_of_commute`,
  `InverseGalois.Shafarevich.commutatorElement_mul_right_of_commute`,
  `InverseGalois.Shafarevich.commutatorElement_inv_left_of_commute`,
  `InverseGalois.Shafarevich.commutatorElement_inv_right_of_commute` — bilinearity of the
  commutator when the relevant commutators are central.
* `InverseGalois.Shafarevich.mul_pow_of_commute_commutator` — **the class two power formula.**

## Tags

commutator, class two, Hall-Petrescu, p-central series
-/

namespace InverseGalois.Shafarevich

variable {G : Type*} [Group G]

/-! ### Bilinearity -/

theorem commutatorElement_mul_left (x y z : G) : ⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆ := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_mul_right (x y z : G) : ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
  simp only [commutatorElement_def]
  group

/-- The commutator is multiplicative in its first argument as soon as the commutator of the second
factor is central enough to be moved past a conjugation. -/
theorem commutatorElement_mul_left_of_commute {x y z : G} (h : Commute x ⁅y, z⁆) :
    ⁅x * y, z⁆ = ⁅y, z⁆ * ⁅x, z⁆ := by
  rw [commutatorElement_mul_left, h.eq]
  group

/-- The commutator is multiplicative in its second argument as soon as the commutator of the second
factor is central enough to be moved past a conjugation. -/
theorem commutatorElement_mul_right_of_commute {x y z : G} (h : Commute y ⁅x, z⁆) :
    ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  rw [commutatorElement_mul_right, h.eq]
  group

/-- Inverting the first argument of a commutator inverts the commutator, as soon as that
commutator is central enough to be moved past a conjugation. -/
theorem commutatorElement_inv_left_of_commute {x z : G} (h : Commute x ⁅x, z⁆) :
    ⁅x⁻¹, z⁆ = ⁅x, z⁆⁻¹ := by
  calc ⁅x⁻¹, z⁆ = x⁻¹ * ⁅x, z⁆⁻¹ * x := by
        simp only [commutatorElement_def]
        group
    _ = ⁅x, z⁆⁻¹ := by rw [mul_assoc, ← h.inv_right.eq, inv_mul_cancel_left]

/-- Inverting the second argument of a commutator inverts the commutator, as soon as that
commutator is central enough to be moved past a conjugation. -/
theorem commutatorElement_inv_right_of_commute {x z : G} (h : Commute z ⁅x, z⁆) :
    ⁅x, z⁻¹⁆ = ⁅x, z⁆⁻¹ := by
  calc ⁅x, z⁻¹⁆ = z⁻¹ * ⁅x, z⁆⁻¹ * z := by
        simp only [commutatorElement_def]
        group
    _ = ⁅x, z⁆⁻¹ := by rw [mul_assoc, ← h.inv_right.eq, inv_mul_cancel_left]

/-! ### The class two power formula -/

/-- Moving a power of `y` past `x` costs one copy of the commutator per unit of the exponent. -/
theorem pow_mul_of_commute_aux {x y c : G} (hy : Commute c y)
    (h : y * x = x * y * c) (n : ℕ) : y ^ n * x = x * y ^ n * c ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc y ^ (n + 1) * x = y * (y ^ n * x) := by rw [pow_succ']; group
      _ = y * (x * y ^ n * c ^ n) := by rw [ih]
      _ = y * x * (y ^ n * c ^ n) := by group
      _ = x * y * c * (y ^ n * c ^ n) := by rw [h]
      _ = x * y * (c * y ^ n) * c ^ n := by group
      _ = x * y * (y ^ n * c) * c ^ n := by rw [(hy.pow_right n).eq]
      _ = x * y ^ (n + 1) * c ^ (n + 1) := by group

/-- The class two power formula, stated for a named commutator. -/
theorem mul_pow_of_commute_aux {x y c : G} (hx : Commute c x) (hy : Commute c y)
    (h : y * x = x * y * c) (n : ℕ) : (x * y) ^ n = x ^ n * y ^ n * c ^ n.choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hchoose : (n + 1).choose 2 = n.choose 2 + n := by
      rw [show (n + 1).choose 2 = n.choose 1 + n.choose 2 from rfl, Nat.choose_one_right,
        Nat.add_comm]
    have hc : Commute (c ^ n.choose 2) (x * y) := (hx.mul_right hy).pow_left _
    calc (x * y) ^ (n + 1) = (x * y) ^ n * (x * y) := pow_succ _ _
      _ = x ^ n * y ^ n * c ^ n.choose 2 * (x * y) := by rw [ih]
      _ = x ^ n * y ^ n * (c ^ n.choose 2 * (x * y)) := by group
      _ = x ^ n * y ^ n * (x * y * c ^ n.choose 2) := by rw [hc.eq]
      _ = x ^ n * (y ^ n * x) * y * c ^ n.choose 2 := by group
      _ = x ^ n * (x * y ^ n * c ^ n) * y * c ^ n.choose 2 := by
          rw [pow_mul_of_commute_aux hy h n]
      _ = x ^ (n + 1) * y ^ n * (c ^ n * y) * c ^ n.choose 2 := by group
      _ = x ^ (n + 1) * y ^ n * (y * c ^ n) * c ^ n.choose 2 := by rw [(hy.pow_left n).eq]
      _ = x ^ (n + 1) * y ^ (n + 1) * c ^ (n.choose 2 + n) := by group
      _ = x ^ (n + 1) * y ^ (n + 1) * c ^ (n + 1).choose 2 := by rw [hchoose]

variable {x y : G}

/-- Moving a power of `y` past `x` costs one commutator per unit of the exponent. -/
theorem pow_mul_of_commute_commutator (hx : Commute ⁅y, x⁆ x) (hy : Commute ⁅y, x⁆ y) (n : ℕ) :
    y ^ n * x = x * y ^ n * ⁅y, x⁆ ^ n := by
  refine pow_mul_of_commute_aux hy ?_ n
  rw [← (hx.mul_right hy).eq]
  simp only [commutatorElement_def]
  group

/-- **The class two power formula.**  If `⁅y, x⁆` commutes with both `x` and `y`, then
`(x * y) ^ n = x ^ n * y ^ n * ⁅y, x⁆ ^ (n.choose 2)`. -/
theorem mul_pow_of_commute_commutator (hx : Commute ⁅y, x⁆ x) (hy : Commute ⁅y, x⁆ y) (n : ℕ) :
    (x * y) ^ n = x ^ n * y ^ n * ⁅y, x⁆ ^ n.choose 2 := by
  refine mul_pow_of_commute_aux hx hy ?_ n
  rw [← (hx.mul_right hy).eq]
  simp only [commutatorElement_def]
  group

end InverseGalois.Shafarevich

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Herbrand

/-!
# The Tate groups of a module with trivial action

When the automorphism is the identity the two operators of the Tate formalism degenerate: the
difference `σ - 1` is zero and the norm is multiplication by `n`.  So the upper Tate group is the
module modulo `n`, the lower one is the `n`-torsion, and the Herbrand quotient is the ratio of
their orders.

The case that matters is the module of integers, where the `n`-torsion is trivial and the quotient
has `n` elements: the Herbrand quotient of `ℤ` with trivial action is `n`.  This is the source of
the factor `[L : K]` in the computation of the Herbrand quotient of the idele classes, entering
through the degree map.

## Main results

* `InverseGalois.CFT.card_tateH0_trivial`: the order of `Ĥ⁰` for a trivial action is the index of
  the multiples of `n`.
* `InverseGalois.CFT.card_tateHm1_trivial`: `Ĥ⁻¹` is trivial when the module has no `n`-torsion.
* `InverseGalois.CFT.herbrand_int`: **the Herbrand quotient of `ℤ` with trivial action is `n`.**

## Tags

Tate cohomology, trivial action, Herbrand quotient
-/

namespace InverseGalois.CFT

variable {A : Type*} [AddCommGroup A]

/-! ### The two operators of a trivial action -/

/-- For a trivial action the difference operator vanishes. -/
theorem sigmaSubOne_one : sigmaSubOne (1 : A ≃+ A) = 0 := by
  ext x
  rw [sigmaSubOne_apply]
  exact sub_self x

/-- For a trivial action the norm is multiplication by `n`. -/
theorem normHom_one_apply (n : ℕ) (x : A) : normHom (1 : A ≃+ A) n x = n • x := by
  rw [normHom_apply]
  have h : ∀ i ∈ Finset.range n, ((1 : A ≃+ A) ^ i) x = x := fun i _ => by rw [one_pow]; rfl
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range]

/-- For a trivial action every element is fixed. -/
theorem ker_sigmaSubOne_one : (sigmaSubOne (1 : A ≃+ A)).ker = ⊤ := by
  ext x
  simp

/-! ### The upper Tate group -/

/-- **The map onto `Ĥ⁰` for a trivial action**, defined on the whole module because every element
is fixed. -/
noncomputable def tateH0Trivial (n : ℕ) : A →+ tateH0 (1 : A ≃+ A) n :=
  (QuotientAddGroup.mk' _).comp
    ((AddMonoidHom.id A).codRestrict (sigmaSubOne (1 : A ≃+ A)).ker
      (fun _ => (mem_ker_sigmaSubOne_iff _ _).mpr rfl))

theorem tateH0Trivial_apply (n : ℕ) (x : A) :
    tateH0Trivial n x = tateH0.mk (1 : A ≃+ A) n x rfl := rfl

theorem tateH0Trivial_surjective (n : ℕ) : Function.Surjective (tateH0Trivial (A := A) n) := by
  intro c
  obtain ⟨x, hx, rfl⟩ := tateH0.mk_surjective c
  exact ⟨x, rfl⟩

theorem ker_tateH0Trivial (n : ℕ) :
    (tateH0Trivial (A := A) n).ker = (normHom (1 : A ≃+ A) n).range := by
  ext x
  rw [AddMonoidHom.mem_ker, tateH0Trivial_apply, tateH0.mk_eq_zero_iff]
  exact Iff.rfl

/-- **The order of `Ĥ⁰` for a trivial action** is the index of the multiples of `n`. -/
theorem card_tateH0_trivial (n : ℕ) :
    Nat.card (tateH0 (1 : A ≃+ A) n) = (normHom (1 : A ≃+ A) n).range.index := by
  rw [AddSubgroup.index_eq_card, ← ker_tateH0Trivial (A := A) n]
  exact (Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective _
    (tateH0Trivial_surjective n)).toEquiv).symm

/-! ### The lower Tate group -/

/-- **`Ĥ⁻¹` is trivial for a trivial action on a module without `n`-torsion.** -/
theorem card_tateHm1_trivial (n : ℕ) (h : ∀ x : A, n • x = 0 → x = 0) :
    Nat.card (tateHm1 (1 : A ≃+ A) n) = 1 := by
  have hsub : Subsingleton (tateHm1 (1 : A ≃+ A) n) := by
    constructor
    intro a b
    obtain ⟨x, hx, rfl⟩ := tateHm1.mk_surjective a
    obtain ⟨y, hy, rfl⟩ := tateHm1.mk_surjective b
    rw [normHom_one_apply] at hx hy
    have hx0 : x = 0 := h x hx
    have hy0 : y = 0 := h y hy
    subst hx0
    subst hy0
    rfl
  exact Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨0⟩⟩

/-! ### The integers -/

/-- The norms of a trivial action on the integers are the multiples of `n`. -/
theorem range_normHom_int (n : ℕ) :
    (normHom (1 : ℤ ≃+ ℤ) n).range = AddSubgroup.zmultiples (n : ℤ) := by
  ext x
  simp only [AddMonoidHom.mem_range, AddSubgroup.mem_zmultiples_iff, normHom_one_apply,
    nsmul_eq_mul, smul_eq_mul]
  exact ⟨fun ⟨y, hy⟩ => ⟨y, by rw [← hy]; ring⟩, fun ⟨k, hk⟩ => ⟨k, by rw [← hk]; ring⟩⟩

/-- `Ĥ⁰` of the integers with trivial action has `n` elements. -/
theorem card_tateH0_int (n : ℕ) : Nat.card (tateH0 (1 : ℤ ≃+ ℤ) n) = n := by
  rw [card_tateH0_trivial, range_normHom_int, Int.index_zmultiples]
  exact Int.natAbs_natCast n

/-- `Ĥ⁻¹` of the integers with trivial action is trivial. -/
theorem card_tateHm1_int (n : ℕ) (hn : n ≠ 0) : Nat.card (tateHm1 (1 : ℤ ≃+ ℤ) n) = 1 := by
  refine card_tateHm1_trivial n fun x hx => ?_
  rw [nsmul_eq_mul, mul_eq_zero] at hx
  rcases hx with h | h
  · exact absurd (Nat.cast_eq_zero.mp h) hn
  · exact h

/-- **The Herbrand quotient of the integers with trivial action is `n`.** -/
theorem herbrand_int (n : ℕ) (hn : n ≠ 0) : herbrand (1 : ℤ ≃+ ℤ) n = n := by
  rw [herbrand, card_tateH0_int, card_tateHm1_int n hn, Nat.cast_one, div_one]

end InverseGalois.CFT

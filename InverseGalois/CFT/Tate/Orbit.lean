/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.PermLattice

/-!
# The lattice of a single orbit

A permutation acting transitively on a finite set turns that set into a single cyclically shifted
block: the powers of the permutation applied to a chosen point run through the whole set, and two
powers give the same point exactly when the exponents agree modulo the period of the point.  The
set is therefore in equivariant bijection with `ZMod` of its own cardinality, and the free lattice
it generates is the module induced from the trivial module over the stabiliser of a point.

The Herbrand quotient follows: for a cyclic group of order `n` acting transitively on a set of `d`
elements, with `n = d * m`, the free lattice on that set has Herbrand quotient `m`.  This is the
shape in which the places of a Galois extension lying over one place of the base field contribute
to the computation of the Herbrand quotient of the ideles.

## Main definitions

* `InverseGalois.CFT.orbitPoint`: the point of an orbit at a given place.
* `InverseGalois.CFT.orbitEquiv`: the cyclic model of a transitive orbit.

## Main results

* `InverseGalois.CFT.pow_apply_congr`: powers agreeing modulo the period act equally on the point.
* `InverseGalois.CFT.apply_orbitEquiv`: the model is equivariant.
* `InverseGalois.CFT.card_eq_period`: a transitive orbit has as many points as the period.
* `InverseGalois.CFT.herbrand_permLatticeAut_of_transitive`: **the Herbrand quotient of the free
  lattice on a transitive orbit is the order of the stabiliser of a point.**

## Tags

Tate cohomology, Herbrand quotient, orbit, permutation module
-/

namespace InverseGalois.CFT

open MulAction

variable {X : Type*} {p : Equiv.Perm X}

/-! ### The period of a point -/

/-- The period of a point under a permutation of a finite set is positive. -/
instance neZero_period [Fintype X] (p : Equiv.Perm X) (x₀ : X) : NeZero (period p x₀) :=
  ⟨(period_pos_of_orderOf_pos (orderOf_pos p) x₀).ne'⟩

variable (p) in
/-- A power of the permutation fixes the point exactly when the period divides the exponent. -/
theorem pow_apply_eq_self_iff (x₀ : X) {k : ℕ} : (p ^ k) x₀ = x₀ ↔ period p x₀ ∣ k :=
  pow_smul_eq_iff_period_dvd (n := k) (m := p) (a := x₀)

variable (p) in
/-- Two powers of the permutation agree on the point exactly when the period divides the difference
of the exponents. -/
theorem pow_apply_eq_pow_apply_iff (x₀ : X) {a b : ℕ} (hab : b ≤ a) :
    (p ^ a) x₀ = (p ^ b) x₀ ↔ period p x₀ ∣ a - b := by
  have hsplit : (p ^ a) x₀ = (p ^ b) ((p ^ (a - b)) x₀) := by
    rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hab]
  rw [hsplit]
  refine ⟨fun h => (pow_apply_eq_self_iff p x₀).mp ((p ^ b).injective h), fun h => ?_⟩
  rw [(pow_apply_eq_self_iff p x₀).mpr h]

variable (p) in
/-- **Powers agreeing modulo the period act equally on the point.** -/
theorem pow_apply_congr (x₀ : X) {a b : ℕ}
    (h : (a : ZMod (period p x₀)) = (b : ZMod (period p x₀))) : (p ^ a) x₀ = (p ^ b) x₀ := by
  rw [ZMod.natCast_eq_natCast_iff] at h
  rcases le_total b a with hab | hab
  · exact (pow_apply_eq_pow_apply_iff p x₀ hab).mpr ((Nat.modEq_iff_dvd' hab).mp h.symm)
  · exact ((pow_apply_eq_pow_apply_iff p x₀ hab).mpr ((Nat.modEq_iff_dvd' hab).mp h)).symm

/-! ### The cyclic model of an orbit -/

variable (p)

/-- **The point of the orbit of `x₀` at the place `j`.** -/
noncomputable def orbitPoint (x₀ : X) (j : ZMod (period p x₀)) : X := (p ^ j.val) x₀

theorem orbitPoint_apply (x₀ : X) (j : ZMod (period p x₀)) :
    orbitPoint p x₀ j = (p ^ j.val) x₀ := rfl

variable [Fintype X]

theorem orbitPoint_injective (x₀ : X) : Function.Injective (orbitPoint p x₀) := by
  intro a b hab
  refine ZMod.val_injective _ ?_
  rcases le_total b.val a.val with h | h
  · have hdvd := (pow_apply_eq_pow_apply_iff p x₀ h).mp hab
    have hlt : a.val - b.val < period p x₀ := lt_of_le_of_lt (Nat.sub_le _ _) (ZMod.val_lt a)
    have hz := Nat.eq_zero_of_dvd_of_lt hdvd
    omega
  · have hdvd := (pow_apply_eq_pow_apply_iff p x₀ h).mp hab.symm
    have hlt : b.val - a.val < period p x₀ := lt_of_le_of_lt (Nat.sub_le _ _) (ZMod.val_lt b)
    have hz := Nat.eq_zero_of_dvd_of_lt hdvd
    omega

theorem orbitPoint_surjective (x₀ : X) (htrans : ∀ y : X, ∃ k : ℕ, (p ^ k) x₀ = y) :
    Function.Surjective (orbitPoint p x₀) := by
  intro y
  obtain ⟨k, hk⟩ := htrans y
  refine ⟨(k : ZMod (period p x₀)), ?_⟩
  rw [orbitPoint_apply, ← hk]
  exact pow_apply_congr p x₀ (ZMod.natCast_rightInverse (k : ZMod (period p x₀)))

/-- **The cyclic model of a transitive orbit.** -/
noncomputable def orbitEquiv (x₀ : X) (htrans : ∀ y : X, ∃ k : ℕ, (p ^ k) x₀ = y) :
    ZMod (period p x₀) ≃ X :=
  Equiv.ofBijective _ ⟨orbitPoint_injective p x₀, orbitPoint_surjective p x₀ htrans⟩

theorem orbitEquiv_apply (x₀ : X) (htrans : ∀ y : X, ∃ k : ℕ, (p ^ k) x₀ = y)
    (j : ZMod (period p x₀)) : orbitEquiv p x₀ htrans j = (p ^ j.val) x₀ := rfl

/-- **The model is equivariant**: the permutation advances the place by one. -/
theorem apply_orbitEquiv (x₀ : X) (htrans : ∀ y : X, ∃ k : ℕ, (p ^ k) x₀ = y)
    (j : ZMod (period p x₀)) :
    p (orbitEquiv p x₀ htrans j) = orbitEquiv p x₀ htrans (j + 1) := by
  have h : ((j.val + 1 : ℕ) : ZMod (period p x₀)) = (((j + 1).val : ℕ) : ZMod (period p x₀)) := by
    rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_rightInverse j,
      ZMod.natCast_rightInverse (j + 1)]
  rw [orbitEquiv_apply, orbitEquiv_apply, ← Equiv.Perm.mul_apply, ← pow_succ']
  exact pow_apply_congr p x₀ h

/-- **A transitive orbit has as many points as the period.** -/
theorem card_eq_period (x₀ : X) (htrans : ∀ y : X, ∃ k : ℕ, (p ^ k) x₀ = y) :
    Fintype.card X = period p x₀ := by
  rw [← Fintype.card_congr (orbitEquiv p x₀ htrans), ZMod.card]

/-! ### The Herbrand quotient -/

/-- The blocks of a single-block presentation. -/
def unitSigmaEquiv (Y : Type*) : (Σ _ : Unit, Y) ≃ Y where
  toFun s := s.2
  invFun y := ⟨(), y⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {p}

/-- **The Herbrand quotient of the free lattice on a transitive orbit is the order of the
stabiliser of a point.**  A cyclic group of order `n = d * m` acting transitively on `d` points has
a stabiliser of order `m`, and the lattice it permutes is induced from the trivial module there. -/
theorem herbrand_permLatticeAut_of_transitive {m n : ℕ} (x₀ : X)
    (htrans : ∀ y : X, ∃ k : ℕ, (p ^ k) x₀ = y) (hnm : period p x₀ * m = n) (hm : m ≠ 0) :
    herbrand (permLatticeAut p) n = (m : ℚ) := by
  have hφ : ∀ (i : Unit) (j : ZMod (period p x₀)),
      p ((unitSigmaEquiv _).trans (orbitEquiv p x₀ htrans) ⟨i, j⟩)
        = (unitSigmaEquiv _).trans (orbitEquiv p x₀ htrans) ⟨i, j + 1⟩ :=
    fun _ j => apply_orbitEquiv p x₀ htrans j
  rw [herbrand_permLatticeAut (ι := Unit) (d := fun _ => period p x₀) (m := fun _ => m)
    (fun _ => hnm) (fun _ => hm) ((unitSigmaEquiv _).trans (orbitEquiv p x₀ htrans)) hφ,
    Finset.prod_const, Finset.card_univ, Fintype.card_unit, pow_one]

end InverseGalois.CFT

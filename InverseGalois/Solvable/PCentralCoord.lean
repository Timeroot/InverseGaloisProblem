/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.PCentralTower

/-!
# The free object of `p`-class one is elementary abelian of the same rank

A group of `p`-class at most one is abelian of exponent dividing `p`, so the free object of rank
`d` in that variety is the free module of rank `d` over the ring with `p` elements.  Reading off
the coordinates of an element is a homomorphism to `(ZMod p) ^ d`, and substituting the standard
basis vectors for the generators inverts it.

This is the bottom rung of the tower of free objects: an extension of `ℚ` whose Galois group is the
free object of `p`-class one and rank `d` is a multiradical extension with `d` independent radicals.

## Main results

* `InverseGalois.FreePClass.instCommGroupOne`: the free object of `p`-class one is abelian.
* `InverseGalois.FreePClass.coord`: the coordinates of an element of the free object of `p`-class
  one.
* `InverseGalois.FreePClass.coordEquiv`: **the free object of rank `d` and `p`-class one is the
  elementary abelian group of rank `d` and exponent `p`.**
* `InverseGalois.FreePClass.card_one`: its order is `p ^ d`.

## Tags

`p`-group, lower central series, free object, elementary abelian
-/

namespace InverseGalois

open Multiplicative

/-! ## Powers along a congruence -/

/-- Two powers of an element killed by an exponent agree when the two exponents are congruent
modulo it. -/
theorem pow_eq_pow_of_modEq {G : Type*} [Group G] {g : G} {n : ℕ} (hg : g ^ n = 1) {a b : ℕ}
    (h : a ≡ b [MOD n]) : g ^ a = g ^ b :=
  pow_eq_pow_iff_modEq.mpr (h.of_dvd (orderOf_dvd_of_pow_eq_one hg))

/-! ## The elementary abelian group -/

/-- The elementary abelian group of rank `d` and exponent `p` has exponent dividing `p`. -/
theorem pow_eq_one_multiplicative (p d : ℕ) (x : Multiplicative (Fin d → ZMod p)) : x ^ p = 1 := by
  refine toAdd.injective ?_
  rw [toAdd_pow, toAdd_one]
  funext i
  simp [nsmul_eq_mul]

/-- The lower `p`-central series of the elementary abelian group of exponent `p` reaches the
trivial subgroup in one step. -/
theorem lowerPCentralSeries_one_multiplicative (p d : ℕ) :
    lowerPCentralSeries p (Multiplicative (Fin d → ZMod p)) 1 = ⊥ := by
  refine le_bot_iff.mp (lowerPCentralSeries_succ_le_of (fun x _ y => ?_) (fun x _ => ?_))
  · rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm x y
  · rw [Subgroup.mem_bot]
    exact pow_eq_one_multiplicative p d x

namespace FreePClass

variable (p d : ℕ)

/-! ## Abelian of exponent `p` -/

/-- The free object of `p`-class one has exponent dividing `p`. -/
theorem pow_eq_one_one (x : FreePClass p d 1) : x ^ p = 1 :=
  pow_eq_one_of_mem_lowerPCentralSeries (lowerPCentralSeries_eq_bot p d 1) (Subgroup.mem_top x)

/-- **The free object of `p`-class one is abelian**, its commutators forming the first term of its
lower `p`-central series. -/
instance instCommGroupOne : CommGroup (FreePClass p d 1) :=
  { instGroup p d 1 with
    mul_comm := fun x y => by
      have hc : ⁅x, y⁆ = 1 := by
        have h := commutator_mem_lowerPCentralSeries_succ (p := p) (n := 0) (y := y)
          (Subgroup.mem_top x)
        rwa [lowerPCentralSeries_eq_bot p d 1, Subgroup.mem_bot] at h
      exact commutatorElement_eq_one_iff_mul_comm.mp hc }

/-! ## The coordinates -/

/-- The coordinates of an element of the free object of rank `d` and `p`-class one. -/
noncomputable def coord : FreePClass p d 1 →* Multiplicative (Fin d → ZMod p) :=
  lift (lowerPCentralSeries_one_multiplicative p d) fun i => ofAdd (Pi.single i 1)

@[simp] theorem coord_gen (i : Fin d) : coord p d (gen p d 1 i) = ofAdd (Pi.single i 1) :=
  lift_gen _ _ i

variable [NeZero p]

/-- The element of the free object of `p`-class one with prescribed coordinates. -/
noncomputable def coordInv : Multiplicative (Fin d → ZMod p) →* FreePClass p d 1 :=
  MonoidHom.mk' (fun x => ∏ i, gen p d 1 i ^ ((toAdd x) i).val) fun x y => by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← pow_add]
    refine pow_eq_pow_of_modEq (pow_eq_one_one p d _) ?_
    rw [Nat.ModEq]
    simp [ZMod.val_add]

theorem coordInv_apply (x : Multiplicative (Fin d → ZMod p)) :
    coordInv p d x = ∏ i, gen p d 1 i ^ ((toAdd x) i).val := rfl

/-- Reading off the coordinates of the element with prescribed coordinates returns them. -/
theorem coord_coordInv (x : Multiplicative (Fin d → ZMod p)) : coord p d (coordInv p d x) = x := by
  rw [coordInv_apply, map_prod]
  simp only [map_pow, coord_gen]
  refine toAdd.injective ?_
  rw [toAdd_prod]
  funext j
  rw [Finset.sum_apply]
  have hterm : ∀ i : Fin d,
      (toAdd (((ofAdd (Pi.single i 1) : Multiplicative (Fin d → ZMod p)))
        ^ ((toAdd x) i).val)) j = if j = i then (((toAdd x) i).val : ZMod p) else 0 := by
    intro i
    rw [toAdd_pow, toAdd_ofAdd, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero,
      nsmul_eq_mul, mul_one]
  simp only [hterm, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp [ZMod.natCast_val, ZMod.cast_id]

/-- The element with the coordinates of a given element is that element. -/
theorem coordInv_coord (g : FreePClass p d 1) : coordInv p d (coord p d g) = g := by
  have hg : g ∈ Subgroup.closure (Set.range (gen p d 1)) := by
    rw [closure_range_gen]
    exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    rw [coord_gen, coordInv_apply, toAdd_ofAdd, Finset.prod_eq_single i]
    · rw [Pi.single_eq_same, ZMod.val_one_eq_one_mod]
      rcases eq_or_ne p 1 with rfl | hp
      · have h1 := pow_eq_one_one 1 d (gen 1 d 1 i)
        rw [pow_one] at h1
        rw [Nat.mod_self, pow_zero, h1]
      · rw [Nat.mod_eq_of_lt (by have := NeZero.ne p; omega), pow_one]
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, ZMod.val_zero, pow_zero]
    · exact fun h => absurd (Finset.mem_univ i) h
  | one => rw [map_one, map_one]
  | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]
  | inv a _ ha => rw [map_inv, map_inv, ha]

/-- **The free object of rank `d` and `p`-class one is the elementary abelian group of rank `d`
and exponent `p`.** -/
noncomputable def coordEquiv : FreePClass p d 1 ≃* Multiplicative (Fin d → ZMod p) :=
  MulEquiv.ofBijective (coord p d)
    ⟨Function.LeftInverse.injective (coordInv_coord p d),
      Function.RightInverse.surjective (coord_coordInv p d)⟩

@[simp] theorem coordEquiv_apply (g : FreePClass p d 1) : coordEquiv p d g = coord p d g := rfl

/-- The free object of rank `d` and `p`-class one has order `p ^ d`. -/
theorem card_one : Nat.card (FreePClass p d 1) = p ^ d := by
  rw [Nat.card_congr (coordEquiv p d).toEquiv]
  simp

end FreePClass

end InverseGalois

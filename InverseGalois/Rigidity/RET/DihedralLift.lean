/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Dihedral groups mapped into a group by generators and relations

A rotation of order dividing `n` and an involution inverting it generate a homomorphic image of
the dihedral group of order `2n`: the assignment `r i ↦ ρ^i`, `sr i ↦ σ·ρ^i` respects the four
cases of the dihedral multiplication, each case being the relation `ρ^i·σ = σ·ρ^{-i}` together
with `σ² = 1` and the fact that powers of `ρ` commute.

The homomorphism is injective as soon as the rotation has order exactly `n` — so that no `r i`
with `i ≠ 0` dies — and the involution is not a power of the rotation — so that no `sr i` dies.

The exponent of a rotation is indexed by `ZMod n`, so the powers are taken along the
representative `ZMod.val`, and the two arithmetic lemmas `pow_val_add` and `pow_val_sub` say that
this is compatible with addition and subtraction in `ZMod n`.

## Main definitions and results

* `Rigidity.RET.dihedralLift` — the homomorphism `DihedralGroup n →* H` determined by a rotation
  and an inverting involution.
* `Rigidity.RET.dihedralLift_injective` — it is injective under the two nondegeneracy
  hypotheses.
* `Rigidity.RET.conj_eq_inv_of_mul_eq_one` — the inverting hypothesis in the form a matrix
  computation delivers it, as the vanishing of the product `σ·ρ·σ·ρ`.
-/

namespace Rigidity.RET

variable {H : Type*} [Group H] {n : ℕ} [NeZero n] {σ ρ : H}

/-! ## Powers along `ZMod n` -/

omit [NeZero n] in
/-- A power of an element killed by `n` only depends on the exponent modulo `n`. -/
theorem pow_val_mod (hρ : ρ ^ n = 1) (m : ℕ) : ρ ^ (m % n) = ρ ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m n]
  rw [pow_add, pow_mul, hρ, one_pow, one_mul]

/-- Powers along `ZMod n` add. -/
theorem pow_val_add (hρ : ρ ^ n = 1) (i j : ZMod n) :
    ρ ^ (i + j).val = ρ ^ i.val * ρ ^ j.val := by
  rw [ZMod.val_add, pow_val_mod hρ, pow_add]

/-- Powers along `ZMod n` subtract. -/
theorem pow_val_sub (hρ : ρ ^ n = 1) (i j : ZMod n) :
    ρ ^ (i - j).val = ρ ^ i.val * (ρ ^ j.val)⁻¹ := by
  have h := pow_val_add (i := i - j) (j := j) hρ
  rw [sub_add_cancel] at h
  exact eq_mul_inv_of_mul_eq h.symm

omit [NeZero n] in
/-- **The dihedral relation from a product.**  An involution `σ` inverts `ρ` exactly when the
fourfold product `σ·ρ·σ·ρ` is trivial, which is how a matrix computation delivers it. -/
theorem conj_eq_inv_of_mul_eq_one (hσ : σ * σ = 1) (h : σ * ρ * σ * ρ = 1) :
    σ * ρ * σ⁻¹ = ρ⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right hσ]
  exact eq_inv_of_mul_eq_one_left h

/-! ## The homomorphism -/

/-- Conjugating a power of the rotation by the involution inverts it. -/
theorem conj_pow (hc : σ * ρ * σ⁻¹ = ρ⁻¹) (m : ℕ) : σ * ρ ^ m * σ⁻¹ = (ρ ^ m)⁻¹ := by
  have h : (MulAut.conj σ) (ρ ^ m) = ((MulAut.conj σ) ρ) ^ m := map_pow _ _ _
  simpa [MulAut.conj_apply, hc, inv_pow] using h

/-- Moving the involution past a power of the rotation inverts the power. -/
theorem pow_mul_swap (hc : σ * ρ * σ⁻¹ = ρ⁻¹) (m : ℕ) : ρ ^ m * σ = σ * (ρ ^ m)⁻¹ := by
  have h : σ * (ρ ^ m)⁻¹ * σ⁻¹ = ρ ^ m := by
    have := congrArg (fun x : H => x⁻¹) (conj_pow hc m)
    simpa [mul_inv_rev, mul_assoc] using this
  calc ρ ^ m * σ = σ * (ρ ^ m)⁻¹ * σ⁻¹ * σ := by rw [h]
    _ = σ * (ρ ^ m)⁻¹ := by group

/-- Powers of the rotation commute with inverse powers of the rotation. -/
theorem pow_inv_comm (i j : ℕ) : (ρ ^ i)⁻¹ * ρ ^ j = ρ ^ j * (ρ ^ i)⁻¹ :=
  (((Commute.refl ρ).pow_pow i j).inv_left).eq

/-- The underlying function of the lift: a rotation goes to a power of `ρ`, a reflection to the
same power preceded by `σ`. -/
def dihedralLiftFun (σ ρ : H) : DihedralGroup n → H
  | .r i => ρ ^ i.val
  | .sr i => σ * ρ ^ i.val

/-- **The homomorphism out of the dihedral group** determined by a rotation of order dividing `n`
and an involution inverting it. -/
def dihedralLift (hρ : ρ ^ n = 1) (hσ : σ * σ = 1) (hc : σ * ρ * σ⁻¹ = ρ⁻¹) :
    DihedralGroup n →* H where
  toFun := dihedralLiftFun σ ρ
  map_one' := by
    show ρ ^ (0 : ZMod n).val = 1
    rw [ZMod.val_zero, pow_zero]
  map_mul' a b := by
    cases a with
    | r i =>
      cases b with
      | r j =>
        show ρ ^ (i + j).val = ρ ^ i.val * ρ ^ j.val
        exact pow_val_add hρ i j
      | sr j =>
        show σ * ρ ^ (j - i).val = ρ ^ i.val * (σ * ρ ^ j.val)
        calc σ * ρ ^ (j - i).val = σ * (ρ ^ j.val * (ρ ^ i.val)⁻¹) := by rw [pow_val_sub hρ]
          _ = σ * ((ρ ^ i.val)⁻¹ * ρ ^ j.val) := by rw [pow_inv_comm]
          _ = σ * (ρ ^ i.val)⁻¹ * ρ ^ j.val := (mul_assoc _ _ _).symm
          _ = ρ ^ i.val * σ * ρ ^ j.val := by rw [pow_mul_swap hc]
          _ = ρ ^ i.val * (σ * ρ ^ j.val) := mul_assoc _ _ _
    | sr i =>
      cases b with
      | r j =>
        show σ * ρ ^ (i + j).val = σ * ρ ^ i.val * ρ ^ j.val
        rw [pow_val_add hρ, mul_assoc]
      | sr j =>
        show ρ ^ (j - i).val = σ * ρ ^ i.val * (σ * ρ ^ j.val)
        calc ρ ^ (j - i).val = ρ ^ j.val * (ρ ^ i.val)⁻¹ := pow_val_sub hρ j i
          _ = (ρ ^ i.val)⁻¹ * ρ ^ j.val := (pow_inv_comm _ _).symm
          _ = σ * σ * ((ρ ^ i.val)⁻¹ * ρ ^ j.val) := by rw [hσ, one_mul]
          _ = σ * (σ * (ρ ^ i.val)⁻¹) * ρ ^ j.val := by group
          _ = σ * (ρ ^ i.val * σ) * ρ ^ j.val := by rw [pow_mul_swap hc]
          _ = σ * ρ ^ i.val * (σ * ρ ^ j.val) := by group

@[simp] theorem dihedralLift_r (hρ : ρ ^ n = 1) (hσ : σ * σ = 1) (hc : σ * ρ * σ⁻¹ = ρ⁻¹)
    (i : ZMod n) : dihedralLift hρ hσ hc (DihedralGroup.r i) = ρ ^ i.val := rfl

@[simp] theorem dihedralLift_sr (hρ : ρ ^ n = 1) (hσ : σ * σ = 1) (hc : σ * ρ * σ⁻¹ = ρ⁻¹)
    (i : ZMod n) : dihedralLift hρ hσ hc (DihedralGroup.sr i) = σ * ρ ^ i.val := rfl

/-- **The lift is injective** when the rotation has order exactly `n` and the involution is not a
power of the rotation. -/
theorem dihedralLift_injective (hρ : ρ ^ n = 1) (hσ : σ * σ = 1) (hc : σ * ρ * σ⁻¹ = ρ⁻¹)
    (hord : orderOf ρ = n) (hnot : ∀ m : ℕ, m < n → σ ≠ ρ ^ m) :
    Function.Injective (dihedralLift hρ hσ hc) := by
  rw [injective_iff_map_eq_one]
  rintro (i | i) h
  · rw [dihedralLift_r] at h
    have hdvd : n ∣ i.val := by
      have hd := orderOf_dvd_of_pow_eq_one h
      rwa [hord] at hd
    have hzero : i.val = 0 := by
      by_contra hne
      exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd) (not_le.mpr (ZMod.val_lt i))
    have hi : i = 0 := by
      have hcast := ZMod.natCast_rightInverse (n := n) i
      rw [hzero] at hcast
      simpa using hcast.symm
    rw [hi]
    rfl
  · exfalso
    have hσval : σ = (ρ ^ i.val)⁻¹ := eq_inv_of_mul_eq_one_left h
    have hle : i.val ≤ n := (ZMod.val_lt i).le
    have hinv : (ρ ^ i.val)⁻¹ = ρ ^ (n - i.val) :=
      inv_eq_of_mul_eq_one_right (by rw [← pow_add, Nat.add_sub_cancel' hle, hρ])
    refine hnot ((n - i.val) % n) (Nat.mod_lt _ (NeZero.pos n)) ?_
    rw [pow_val_mod hρ, hσval, hinv]

end Rigidity.RET

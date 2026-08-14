/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Loops in a topological monoid

A loop based at the unit of a topological monoid can be multiplied with another such loop in two
different ways: pointwise, and by concatenation.  The two agree up to homotopy.  The homotopy is an
explicit reparametrisation: at time `s` the first factor runs through its loop at speed `1 + s`
and then waits, while the second waits and then runs through its loop at speed `1 + s`; at `s = 0`
both run at unit speed, which is the pointwise product, and at `s = 1` the two runs are disjoint,
which is the concatenation.

The consequence used elsewhere is that raising a loop pointwise to the `n`-th power is the `n`-th
power in the fundamental group, so that the `n`-th power map of a topological group multiplies the
fundamental group of the group by `n`.  That is the source of every local degree computation: the
`n`-th power map of the punctured plane multiplies the winding number by `n`.

## Main definitions

* `Rigidity.RET.loopMul` — the pointwise product of two loops at the unit.
* `Rigidity.RET.loopPow` — the pointwise `n`-th power of a loop at the unit.

## Main results

* `Rigidity.RET.homotopic_loopMul` — the pointwise product of two loops is homotopic to their
  concatenation.
* `Rigidity.RET.fromPath_loopPow` — the pointwise `n`-th power of a loop is the `n`-th power of its
  class in the fundamental group.
* `Rigidity.RET.mapOfEq_npowMap` — the `n`-th power map of a topological group acts on the
  fundamental group at the unit as the `n`-th power map.
-/

open unitInterval

noncomputable section

namespace Rigidity.RET

variable {G : Type*} [TopologicalSpace G] [Monoid G] [ContinuousMul G]

/-- The **pointwise product** of two loops based at the unit. -/
def loopMul (α β : Path (1 : G) 1) : Path (1 : G) 1 where
  toFun t := α t * β t
  continuous_toFun := α.continuous.mul β.continuous
  source' := by show α 0 * β 0 = 1; rw [α.source, β.source, mul_one]
  target' := by show α 1 * β 1 = 1; rw [α.target, β.target, mul_one]

@[simp] theorem loopMul_apply (α β : Path (1 : G) 1) (t : I) : loopMul α β t = α t * β t := rfl

/-! ### The reparametrisation -/

/-- The reparametrisation of the first factor: at time `s` the first loop is run at speed `1 + s`
and then waits. -/
def leftParam : C(I × I, I) :=
  ⟨fun p => ⟨min ((1 + (p.1 : ℝ)) * (p.2 : ℝ)) 1,
      ⟨le_min (mul_nonneg (by linarith [p.1.2.1]) p.2.2.1) zero_le_one, min_le_right _ _⟩⟩, by
    refine Continuous.subtype_mk (Continuous.min ?_ continuous_const) _
    exact (continuous_const.add (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_subtype_val.comp continuous_snd)⟩

/-- The reparametrisation of the second factor: at time `s` the second loop waits and is then run
at speed `1 + s`. -/
def rightParam : C(I × I, I) :=
  ⟨fun p => ⟨max ((1 + (p.1 : ℝ)) * (p.2 : ℝ) - (p.1 : ℝ)) 0,
      ⟨le_max_right _ _, max_le (by nlinarith [p.1.2.1, p.1.2.2, p.2.2.1, p.2.2.2]) zero_le_one⟩⟩,
    by
    refine Continuous.subtype_mk (Continuous.max ?_ continuous_const) _
    exact ((continuous_const.add (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_subtype_val.comp continuous_snd)).sub
      (continuous_subtype_val.comp continuous_fst)⟩

theorem leftParam_zero (x : I) : leftParam ((0 : I), x) = x := by
  refine Subtype.ext ?_
  show min ((1 + ((0 : I) : ℝ)) * (x : ℝ)) 1 = (x : ℝ)
  rw [Set.Icc.coe_zero, add_zero, one_mul, min_eq_left x.2.2]

theorem rightParam_zero (x : I) : rightParam ((0 : I), x) = x := by
  refine Subtype.ext ?_
  show max ((1 + ((0 : I) : ℝ)) * (x : ℝ) - ((0 : I) : ℝ)) 0 = (x : ℝ)
  rw [Set.Icc.coe_zero, add_zero, one_mul, sub_zero, max_eq_left x.2.1]

theorem leftParam_apply_zero (s : I) : leftParam (s, (0 : I)) = 0 := by
  refine Subtype.ext ?_
  show min ((1 + (s : ℝ)) * ((0 : I) : ℝ)) 1 = ((0 : I) : ℝ)
  rw [Set.Icc.coe_zero, mul_zero, min_eq_left zero_le_one]

theorem rightParam_apply_zero (s : I) : rightParam (s, (0 : I)) = 0 := by
  refine Subtype.ext ?_
  show max ((1 + (s : ℝ)) * ((0 : I) : ℝ) - (s : ℝ)) 0 = ((0 : I) : ℝ)
  rw [Set.Icc.coe_zero, mul_zero, zero_sub, max_eq_right (by linarith [s.2.1])]

theorem leftParam_apply_one (s : I) : leftParam (s, (1 : I)) = 1 := by
  refine Subtype.ext ?_
  show min ((1 + (s : ℝ)) * ((1 : I) : ℝ)) 1 = ((1 : I) : ℝ)
  rw [Set.Icc.coe_one, mul_one, min_eq_right (by linarith [s.2.1])]

theorem rightParam_apply_one (s : I) : rightParam (s, (1 : I)) = 1 := by
  refine Subtype.ext ?_
  show max ((1 + (s : ℝ)) * ((1 : I) : ℝ) - (s : ℝ)) 0 = ((1 : I) : ℝ)
  rw [Set.Icc.coe_one, mul_one, add_sub_cancel_right, max_eq_left zero_le_one]

/-! ### The homotopy -/

/-- **In a topological monoid the pointwise product of two loops at the unit is homotopic to their
concatenation.** -/
theorem homotopic_loopMul (α β : Path (1 : G) 1) : (loopMul α β).Homotopic (α.trans β) := by
  refine ⟨{ toFun := fun p => α (leftParam p) * β (rightParam p)
            continuous_toFun := (α.continuous.comp leftParam.continuous).mul
              (β.continuous.comp rightParam.continuous)
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }⟩
  · intro x
    show α (leftParam ((0 : I), x)) * β (rightParam ((0 : I), x)) = α x * β x
    rw [leftParam_zero, rightParam_zero]
  · intro x
    show α (leftParam ((1 : I), x)) * β (rightParam ((1 : I), x)) = (α.trans β) x
    rw [Path.trans_apply]
    have hs : ((1 : I) : ℝ) = 1 := Set.Icc.coe_one
    have hexp : (1 + ((1 : I) : ℝ)) * (x : ℝ) = 2 * (x : ℝ) := by rw [hs]; ring
    split
    · rename_i h
      have hl : leftParam ((1 : I), x)
          = ⟨2 * (x : ℝ), ⟨by linarith [x.2.1], by linarith⟩⟩ := by
        refine Subtype.ext ?_
        show min ((1 + ((1 : I) : ℝ)) * (x : ℝ)) 1 = 2 * (x : ℝ)
        rw [hexp]
        exact min_eq_left (by linarith)
      have hr : rightParam ((1 : I), x) = 0 := by
        refine Subtype.ext ?_
        show max ((1 + ((1 : I) : ℝ)) * (x : ℝ) - ((1 : I) : ℝ)) 0 = ((0 : I) : ℝ)
        rw [hexp, hs, Set.Icc.coe_zero]
        exact max_eq_right (by linarith)
      rw [hl, hr, β.source, mul_one]
    · rename_i h
      have hx : 1 / 2 < (x : ℝ) := by push_neg at h; exact h
      have hl : leftParam ((1 : I), x) = 1 := by
        refine Subtype.ext ?_
        show min ((1 + ((1 : I) : ℝ)) * (x : ℝ)) 1 = ((1 : I) : ℝ)
        rw [hexp, hs]
        exact min_eq_right (by linarith)
      have hr : rightParam ((1 : I), x)
          = ⟨2 * (x : ℝ) - 1, ⟨by linarith, by linarith [x.2.2]⟩⟩ := by
        refine Subtype.ext ?_
        show max ((1 + ((1 : I) : ℝ)) * (x : ℝ) - ((1 : I) : ℝ)) 0 = 2 * (x : ℝ) - 1
        rw [hexp, hs]
        exact max_eq_left (by linarith)
      rw [hl, hr, α.target, one_mul]
  · intro s x hx
    show α (leftParam (s, x)) * β (rightParam (s, x)) = α x * β x
    rcases hx with hx | hx
    · rw [hx, leftParam_apply_zero, rightParam_apply_zero]
    · rw [Set.mem_singleton_iff] at hx
      rw [hx, leftParam_apply_one, rightParam_apply_one]

/-! ### Pointwise powers -/

/-- The **pointwise `n`-th power** of a loop based at the unit. -/
def loopPow (α : Path (1 : G) 1) (n : ℕ) : Path (1 : G) 1 where
  toFun t := α t ^ n
  continuous_toFun := (continuous_pow n).comp α.continuous
  source' := by show α 0 ^ n = 1; rw [α.source, one_pow]
  target' := by show α 1 ^ n = 1; rw [α.target, one_pow]

@[simp] theorem loopPow_apply (α : Path (1 : G) 1) (n : ℕ) (t : I) : loopPow α n t = α t ^ n := rfl

theorem loopPow_zero (α : Path (1 : G) 1) : loopPow α 0 = Path.refl 1 :=
  Path.ext (funext fun t => pow_zero (α t))

theorem loopPow_succ (α : Path (1 : G) 1) (n : ℕ) :
    loopPow α (n + 1) = loopMul (loopPow α n) α :=
  Path.ext (funext fun t => pow_succ (α t) n)

/-- **The pointwise `n`-th power of a loop is the `n`-th power of its class in the fundamental
group.** -/
theorem fromPath_loopPow (α : Path (1 : G) 1) (n : ℕ) :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (loopPow α n))
      = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk α) ^ n := by
  induction n with
  | zero => rw [loopPow_zero]; rfl
  | succ n ih =>
    have h : Path.Homotopic.Quotient.mk (loopPow α (n + 1))
        = Path.Homotopic.Quotient.mk ((loopPow α n).trans α) := by
      rw [loopPow_succ]
      exact Quotient.sound (homotopic_loopMul _ _)
    rw [h, pow_succ', ← ih]
    rfl

/-- The `n`-th power map of a topological monoid, as a continuous map. -/
def npowMap (G : Type*) [TopologicalSpace G] [Monoid G] [ContinuousMul G] (n : ℕ) : C(G, G) :=
  ⟨fun x => x ^ n, continuous_pow n⟩

/-- **The `n`-th power map of a topological monoid multiplies the fundamental group at the unit by
`n`.** -/
theorem mapOfEq_npowMap (n : ℕ) (γ : FundamentalGroup G 1) :
    FundamentalGroup.mapOfEq (npowMap G n) (one_pow n) γ = γ ^ n := by
  induction γ using Quotient.inductionOn with
  | h p =>
    have hcast : (p.map (npowMap G n).continuous).cast (one_pow n).symm (one_pow n).symm
        = loopPow p n := Path.ext rfl
    show FundamentalGroup.mapOfEq (npowMap G n) (one_pow n)
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) = _
    rw [FundamentalGroup.mapOfEq_apply, hcast, fromPath_loopPow]
    rfl

end Rigidity.RET

end

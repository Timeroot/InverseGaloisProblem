/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Taylor series of a smooth germ

The passage from a holomorphic function to a formal power series is the local form of the
comparison between the analytic and the algebraic worlds.  Concretely it is the map that sends a
function to the sequence of its derivatives at a point, divided by factorials.  Because the
Leibniz rule for the `n`-th derivative of a product is exactly the convolution of two sequences of
Taylor coefficients, this map is a ring homomorphism on the functions that are infinitely
differentiable at the point.

Two computations make it usable: the Taylor series of a constant is that constant, and the Taylor
series of the identity at the origin is the variable.  Everything else follows from the ring
homomorphism property; in particular the Taylor series of the Kummer coordinate `u ↦ s + u ^ e` is
`s + X ^ e`.  Finally, only the germ of a function matters, so a function vanishing near the point
has vanishing Taylor series.

## Main definitions

* `Rigidity.RET.smoothAt` — the subring of functions infinitely differentiable at a point.
* `Rigidity.RET.taylorHom` — the Taylor series of such a function, as a ring homomorphism.

## Main results

* `Rigidity.RET.taylorHom_const` — the Taylor series of a constant.
* `Rigidity.RET.taylorHom_id` — the Taylor series of the identity at the origin is the variable.
* `Rigidity.RET.taylorHom_eq_zero_of_eventuallyEq` — a function vanishing near the point has
  vanishing Taylor series.
-/

open scoped ContDiff

open Filter Nat Topology

noncomputable section

namespace Rigidity.RET

/-! ### The subring of smooth germs -/

/-- The functions that are **infinitely differentiable at a point** form a subring of all
functions. -/
def smoothAt (x : ℂ) : Subring (ℂ → ℂ) where
  carrier := {f | ContDiffAt ℂ ∞ f x}
  zero_mem' := show ContDiffAt ℂ ∞ (fun _ : ℂ => (0 : ℂ)) x from contDiffAt_const
  one_mem' := show ContDiffAt ℂ ∞ (fun _ : ℂ => (1 : ℂ)) x from contDiffAt_const
  add_mem' := fun {a b} ha hb =>
    show ContDiffAt ℂ ∞ (fun u => a u + b u) x from
      ContDiffAt.add (show ContDiffAt ℂ ∞ a x from ha) (show ContDiffAt ℂ ∞ b x from hb)
  mul_mem' := fun {a b} ha hb =>
    show ContDiffAt ℂ ∞ (fun u => a u * b u) x from
      ContDiffAt.mul (show ContDiffAt ℂ ∞ a x from ha) (show ContDiffAt ℂ ∞ b x from hb)
  neg_mem' := fun {a} ha =>
    show ContDiffAt ℂ ∞ (fun u => -a u) x from
      ContDiffAt.neg (show ContDiffAt ℂ ∞ a x from ha)

theorem mem_smoothAt {x : ℂ} {f : ℂ → ℂ} : f ∈ smoothAt x ↔ ContDiffAt ℂ ∞ f x := Iff.rfl

/-- A smooth germ is `n`-times continuously differentiable for every finite `n`. -/
theorem contDiffAt_coe {x : ℂ} (f : smoothAt x) (n : ℕ) :
    ContDiffAt ℂ n (f : ℂ → ℂ) x :=
  (mem_smoothAt.mp f.2).of_le (mod_cast le_top)

/-! ### The Taylor series -/

/-- The **Taylor series** of a smooth germ: the sequence of its derivatives at the point, divided
by factorials. -/
def taylorHom (x : ℂ) : smoothAt x →+* PowerSeries ℂ where
  toFun f := PowerSeries.mk fun n => iteratedDeriv n (f : ℂ → ℂ) x / (n ! : ℂ)
  map_one' := by
    ext n
    rw [PowerSeries.coeff_mk]
    show iteratedDeriv n (fun _ : ℂ => (1 : ℂ)) x / (n ! : ℂ) = _
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · rw [iteratedDeriv_const, if_neg hn.ne', zero_div, PowerSeries.coeff_one, if_neg hn.ne']
  map_zero' := by
    ext n
    rw [PowerSeries.coeff_mk]
    show iteratedDeriv n (fun _ : ℂ => (0 : ℂ)) x / (n ! : ℂ) = _
    simp
  map_add' f g := by
    ext n
    rw [map_add, PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    show iteratedDeriv n ((f : ℂ → ℂ) + (g : ℂ → ℂ)) x / (n ! : ℂ) = _
    rw [iteratedDeriv_add (contDiffAt_coe f n) (contDiffAt_coe g n), add_div]
  map_mul' f g := by
    ext n
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mk]
    show iteratedDeriv n ((f : ℂ → ℂ) * (g : ℂ → ℂ)) x / (n ! : ℂ) = _
    rw [iteratedDeriv_mul (contDiffAt_coe f n) (contDiffAt_coe g n),
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_div]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hfac : ((n.choose i : ℂ)) * (i ! : ℂ) * ((n - i)! : ℂ) = (n ! : ℂ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℂ) (Nat.choose_mul_factorial_mul_factorial hin)
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    rw [← hfac]
    have h1 : ((i ! : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
    have h2 : (((n - i)! : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - i))
    have h3 : ((n.choose i : ℂ)) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.choose_pos hin).ne'
    field_simp

@[simp] theorem coeff_taylorHom (x : ℂ) (f : smoothAt x) (n : ℕ) :
    PowerSeries.coeff n (taylorHom x f) = iteratedDeriv n (f : ℂ → ℂ) x / (n ! : ℂ) := by
  show PowerSeries.coeff n
      (PowerSeries.mk fun m => iteratedDeriv m (f : ℂ → ℂ) x / (m ! : ℂ)) = _
  rw [PowerSeries.coeff_mk]

/-! ### The basic germs -/

/-- A constant function, as a smooth germ. -/
def constGerm (x c : ℂ) : smoothAt x :=
  ⟨fun _ => c, show ContDiffAt ℂ ∞ (fun _ : ℂ => c) x from contDiffAt_const⟩

@[simp] theorem coe_constGerm (x c : ℂ) : (constGerm x c : ℂ → ℂ) = fun _ => c := rfl

/-- The identity function, as a smooth germ. -/
def idGerm (x : ℂ) : smoothAt x :=
  ⟨fun u => u, show ContDiffAt ℂ ∞ (fun u : ℂ => u) x from contDiffAt_id⟩

@[simp] theorem coe_idGerm (x : ℂ) : (idGerm x : ℂ → ℂ) = fun u => u := rfl

/-- **The Taylor series of a constant is that constant.** -/
@[simp] theorem taylorHom_const (x c : ℂ) : taylorHom x (constGerm x c) = PowerSeries.C c := by
  ext n
  rw [coeff_taylorHom, coe_constGerm]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · rw [iteratedDeriv_const, if_neg hn.ne', zero_div, PowerSeries.coeff_C, if_neg hn.ne']

/-- **The Taylor series of the identity at the origin is the variable.** -/
@[simp] theorem taylorHom_id : taylorHom 0 (idGerm 0) = PowerSeries.X := by
  ext n
  rw [coeff_taylorHom, coe_idGerm, iteratedDeriv_fun_id_zero, PowerSeries.coeff_X]
  rcases eq_or_ne n 1 with hn | hn
  · subst hn; simp
  · rw [if_neg hn, zero_div]

/-! ### Locality -/

/-- **Only the germ matters**: two functions agreeing near the point have the same Taylor
series. -/
theorem taylorHom_congr {x : ℂ} (f g : smoothAt x) (h : (f : ℂ → ℂ) =ᶠ[𝓝 x] (g : ℂ → ℂ)) :
    taylorHom x f = taylorHom x g := by
  ext n
  rw [coeff_taylorHom, coeff_taylorHom, h.iteratedDeriv_eq n]

/-- **A function vanishing near the point has vanishing Taylor series.** -/
theorem taylorHom_eq_zero_of_eventuallyEq {x : ℂ} (f : smoothAt x)
    (h : (f : ℂ → ℂ) =ᶠ[𝓝 x] 0) : taylorHom x f = 0 := by
  rw [taylorHom_congr f 0 h, map_zero]

end Rigidity.RET

end

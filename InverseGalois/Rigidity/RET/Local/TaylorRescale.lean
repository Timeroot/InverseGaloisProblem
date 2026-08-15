/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Local.TaylorSeries

/-!
# Rotating the variable of a smooth germ

Rotating the variable of a holomorphic function multiplies the `n`-th Taylor coefficient by the
`n`-th power of the rotation.  That is the analytic shadow of the substitution `X ↦ ζ X` on formal
power series, and it is what turns a statement about a loop around a branch point — where the local
coordinate comes back multiplied by a root of unity — into a statement about the associated formal
expansion.

The comparison between an analytic identity and a formal one also needs one piece of slack: the
identity between two germs is usually only available away from the point itself, because that is
where the geometry lives.  A germ is continuous, so an identity on a punctured neighbourhood already
forces the identity at the point, and hence equality of the Taylor series.

## Main definitions

* `Rigidity.RET.scaleGerm` — a smooth germ at the origin with its variable rotated.

## Main results

* `Rigidity.RET.taylorHom_congr_of_punctured` — two germs agreeing away from the point have the same
  Taylor series.
* `Rigidity.RET.taylorHom_scaleGerm` — rotating the variable rescales the Taylor series.
-/

open scoped ContDiff

open Filter Nat Topology

noncomputable section

namespace Rigidity.RET

/-! ### Identities away from the point -/

/-- **Two germs agreeing away from the point have the same Taylor series.**  A smooth germ is
continuous, so the values at the point are the limits of the values nearby, and those already
agree. -/
theorem taylorHom_congr_of_punctured {x : ℂ} (f g : smoothAt x)
    (h : (f : ℂ → ℂ) =ᶠ[𝓝[≠] x] (g : ℂ → ℂ)) : taylorHom x f = taylorHom x g := by
  have hfc : ContinuousAt (f : ℂ → ℂ) x := (contDiffAt_coe f 0).continuousAt
  have hgc : ContinuousAt (g : ℂ → ℂ) x := (contDiffAt_coe g 0).continuousAt
  have hval : (f : ℂ → ℂ) x = (g : ℂ → ℂ) x :=
    tendsto_nhds_unique (hfc.continuousWithinAt (s := {x}ᶜ))
      (Filter.Tendsto.congr' h.symm (hgc.continuousWithinAt (s := {x}ᶜ)))
  have hsup : ∀ᶠ y in 𝓝[≠] x ⊔ pure x, (f : ℂ → ℂ) y = (g : ℂ → ℂ) y :=
    Filter.eventually_sup.mpr ⟨h, by simpa using hval⟩
  rw [nhdsNE_sup_pure] at hsup
  exact taylorHom_congr f g hsup

/-! ### Rotating the variable -/

/-- A smooth germ at the origin with its **variable rotated**. -/
def scaleGerm (ζ : ℂ) (f : smoothAt 0) : smoothAt 0 :=
  ⟨fun u => (f : ℂ → ℂ) (ζ * u), by
    have hf : ContDiffAt ℂ ∞ (f : ℂ → ℂ) (ζ * 0) := by
      rw [mul_zero]; exact mem_smoothAt.mp f.2
    exact hf.comp 0 (contDiffAt_const.mul contDiffAt_id)⟩

@[simp] theorem coe_scaleGerm (ζ : ℂ) (f : smoothAt 0) :
    (scaleGerm ζ f : ℂ → ℂ) = fun u => (f : ℂ → ℂ) (ζ * u) := rfl

/-- **Rotating the variable of a smooth germ multiplies its `n`-th derivative at the origin by the
`n`-th power of the rotation.**  The rotation preserves every disc about the origin, so the
computation can be carried out inside one small disc on which the germ is genuinely
differentiable. -/
theorem iteratedDeriv_comp_const_mul_of_contDiffAt {f : ℂ → ℂ} (hf : ContDiffAt ℂ ∞ f 0)
    {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1) (n : ℕ) :
    iteratedDeriv n (fun u => f (ζ * u)) 0 = ζ ^ n * iteratedDeriv n f 0 := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn (m := (n : ℕ∞)) (mod_cast le_top) (by simp)
  obtain ⟨r, hr, hru⟩ := Metric.mem_nhds_iff.mp hu
  have hs : IsOpen (Metric.ball (0 : ℂ) r) := Metric.isOpen_ball
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r := Metric.mem_ball_self hr
  have hmaps : Set.MapsTo (ζ * ·) (Metric.ball (0 : ℂ) r) (Metric.ball (0 : ℂ) r) := by
    intro w hw
    simp only [mem_ball_zero_iff, norm_mul] at hw ⊢
    calc ‖ζ‖ * ‖w‖ ≤ 1 * ‖w‖ := by gcongr
      _ = ‖w‖ := one_mul _
      _ < r := hw
  have key := iteratedDerivWithin_comp_const_smul (n := n) h0 hs.uniqueDiffOn (hfu.mono hru) ζ hmaps
  rw [mul_zero] at key
  have e1 : iteratedDerivWithin n (fun w => f (ζ * w)) (Metric.ball (0 : ℂ) r) 0
      = iteratedDeriv n (fun w => f (ζ * w)) 0 := iteratedDerivWithin_of_isOpen hs h0
  have e2 : iteratedDerivWithin n f (Metric.ball (0 : ℂ) r) 0 = iteratedDeriv n f 0 :=
    iteratedDerivWithin_of_isOpen hs h0
  rw [← e1, ← e2, key, smul_eq_mul]

/-- **Rotating the variable of a smooth germ rescales its Taylor series.** -/
theorem taylorHom_scaleGerm {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1) (f : smoothAt 0) :
    taylorHom 0 (scaleGerm ζ f) = PowerSeries.rescale ζ (taylorHom 0 f) := by
  ext n
  rw [coeff_taylorHom, PowerSeries.coeff_rescale, coeff_taylorHom, coe_scaleGerm,
    iteratedDeriv_comp_const_mul_of_contDiffAt (mem_smoothAt.mp f.2) hζ n]
  ring

end Rigidity.RET

end

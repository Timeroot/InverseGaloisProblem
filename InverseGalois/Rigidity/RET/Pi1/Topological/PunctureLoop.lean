/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Pi1.Topological.CircleGroup
import InverseGalois.Rigidity.RET.Pi1.Topological.Transport
import InverseGalois.Rigidity.RET.Pi1.Topological.PuncturedPlane

/-!
# The punctured disc and its loop

A small disc around a puncture, with the puncture removed, is the local model of a branch point:
the loops of a covering space around that puncture are the loops of the punctured disc, and the
monodromy of the generator of its fundamental group is the local branch cycle.

The punctured disc is homeomorphic to the punctured plane by a radial stretch: the radius `t` of a
point is sent to `t / (ρ - t)`, which increases from `0` to `∞` as `t` runs over `(0, ρ)`, and the
direction is kept.  The fundamental group of the punctured disc is therefore infinite cyclic, at
every basepoint.

## Main definitions

* `Rigidity.RET.puncturedDisc` — a disc with its centre removed.
* `Rigidity.RET.puncturedDiscHomeo` — the radial stretch onto the punctured plane.

## Main results

* `Rigidity.RET.pathConnectedSpace_puncturedDisc` — a punctured disc is path connected.
* `Rigidity.RET.nonempty_fundamentalGroup_puncturedDisc` — the fundamental group of a punctured
  disc is infinite cyclic, at every basepoint.
-/

open Topology

noncomputable section

namespace Rigidity.RET

/-! ### The radial stretch -/

/-- A disc with its centre removed. -/
def puncturedDisc (s : ℂ) (ρ : ℝ) : Set ℂ := Metric.ball s ρ \ {s}

theorem mem_puncturedDisc {s : ℂ} {ρ : ℝ} {z : ℂ} :
    z ∈ puncturedDisc s ρ ↔ ‖z - s‖ < ρ ∧ z ≠ s := by
  simp [puncturedDisc, Metric.mem_ball, dist_eq_norm]

theorem norm_sub_lt_of_mem_puncturedDisc {s : ℂ} {ρ : ℝ} {z : ℂ}
    (hz : z ∈ puncturedDisc s ρ) : ‖z - s‖ < ρ :=
  (mem_puncturedDisc.mp hz).1

theorem sub_ne_zero_of_mem_puncturedDisc {s : ℂ} {ρ : ℝ} {z : ℂ}
    (hz : z ∈ puncturedDisc s ρ) : z - s ≠ 0 :=
  sub_ne_zero_of_ne (mem_puncturedDisc.mp hz).2

/-- The radial stretch of a punctured disc onto the punctured plane. -/
def discOut (s : ℂ) (ρ : ℝ) (z : ℂ) : ℂ := (ρ - ‖z - s‖)⁻¹ • (z - s)

/-- The radial shrink of the punctured plane back into a punctured disc. -/
def discIn (s : ℂ) (ρ : ℝ) (w : ℂ) : ℂ := s + (ρ / (1 + ‖w‖)) • w

theorem discOut_ne_zero {s : ℂ} {ρ : ℝ} {z : ℂ} (hz : z ∈ puncturedDisc s ρ) :
    discOut s ρ z ≠ 0 :=
  smul_ne_zero
    (inv_ne_zero (ne_of_gt (sub_pos.mpr (norm_sub_lt_of_mem_puncturedDisc hz))))
    (sub_ne_zero_of_mem_puncturedDisc hz)

theorem discIn_mem {s : ℂ} {ρ : ℝ} (hρ : 0 < ρ) {w : ℂ} (hw : w ≠ 0) :
    discIn s ρ w ∈ puncturedDisc s ρ := by
  have hpos : (0 : ℝ) < 1 + ‖w‖ := by positivity
  have hnw : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  have hnorm : ‖discIn s ρ w - s‖ = ρ / (1 + ‖w‖) * ‖w‖ := by
    rw [discIn, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  refine mem_puncturedDisc.mpr ⟨?_, ?_⟩
  · rw [hnorm, div_mul_eq_mul_div, div_lt_iff₀ hpos]
    nlinarith
  · intro hc
    have : ‖discIn s ρ w - s‖ = 0 := by rw [hc, sub_self, norm_zero]
    rw [hnorm] at this
    exact absurd this (by positivity)

theorem discIn_discOut {s : ℂ} {ρ : ℝ} {z : ℂ} (hz : z ∈ puncturedDisc s ρ) :
    discIn s ρ (discOut s ρ z) = z := by
  set t : ℝ := ‖z - s‖ with ht
  have htρ : (0 : ℝ) < ρ - t := sub_pos.mpr (norm_sub_lt_of_mem_puncturedDisc hz)
  have hρ0 : (0 : ℝ) < ρ :=
    lt_of_le_of_lt (norm_nonneg _) (norm_sub_lt_of_mem_puncturedDisc hz)
  have hnw : ‖discOut s ρ z‖ = (ρ - t)⁻¹ * t := by
    rw [discOut, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htρ), ← ht]
  have hone : 1 + ‖discOut s ρ z‖ = ρ * (ρ - t)⁻¹ := by
    rw [hnw]
    field_simp
    ring
  have hc : ρ / (1 + ‖discOut s ρ z‖) = ρ - t := by
    rw [hone]
    field_simp
  rw [discIn, hc, discOut, smul_smul, mul_inv_cancel₀ (ne_of_gt htρ), one_smul, add_sub_cancel]

theorem discOut_discIn {s : ℂ} {ρ : ℝ} (hρ : 0 < ρ) {w : ℂ} (hw : w ≠ 0) :
    discOut s ρ (discIn s ρ w) = w := by
  have hpos : (0 : ℝ) < 1 + ‖w‖ := by positivity
  set c : ℝ := ρ / (1 + ‖w‖) with hcdef
  have hcpos : 0 < c := by positivity
  have hnorm : ‖discIn s ρ w - s‖ = c * ‖w‖ := by
    rw [discIn, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
  have hden : ρ - ‖discIn s ρ w - s‖ = c := by
    rw [hnorm, hcdef]
    field_simp
    ring
  rw [discOut, hden, discIn, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (ne_of_gt hcpos),
    one_smul]

theorem continuous_discOut_subtype (s : ℂ) (ρ : ℝ) :
    Continuous fun z : ↥(puncturedDisc s ρ) => discOut s ρ (z : ℂ) := by
  refine Continuous.smul (Continuous.inv₀ ?_ ?_) (continuous_subtype_val.sub continuous_const)
  · exact continuous_const.sub (continuous_subtype_val.sub continuous_const).norm
  · exact fun z => ne_of_gt (sub_pos.mpr (norm_sub_lt_of_mem_puncturedDisc z.2))

theorem continuous_discIn (s : ℂ) (ρ : ℝ) : Continuous (discIn s ρ) := by
  refine continuous_const.add (Continuous.smul ?_ continuous_id)
  exact continuous_const.div (continuous_const.add continuous_norm) fun w => by positivity

/-- **A punctured disc is a punctured plane.**  The radial stretch `t ↦ t / (ρ - t)` carries the
disc of radius `ρ` about `s`, with `s` removed, homeomorphically onto the plane with the origin
removed. -/
def puncturedDiscHomeo (s : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ↥(puncturedDisc s ρ) ≃ₜ {w : ℂ // w ≠ 0} where
  toFun z := ⟨discOut s ρ (z : ℂ), discOut_ne_zero z.2⟩
  invFun w := ⟨discIn s ρ (w : ℂ), discIn_mem hρ w.2⟩
  left_inv z := Subtype.ext (discIn_discOut z.2)
  right_inv w := Subtype.ext (discOut_discIn hρ w.2)
  continuous_toFun := (continuous_discOut_subtype s ρ).subtype_mk _
  continuous_invFun := ((continuous_discIn s ρ).comp continuous_subtype_val).subtype_mk _

/-! ### The fundamental group of a punctured disc -/

/-- A punctured disc is path connected. -/
theorem pathConnectedSpace_puncturedDisc (s : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    PathConnectedSpace ↥(puncturedDisc s ρ) := by
  haveI : PathConnectedSpace {w : ℂ // w ≠ 0} := by
    have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
      rw [Complex.rank_real_complex]; norm_num
    exact isPathConnected_iff_pathConnectedSpace.mp
      ((Set.countable_singleton (0 : ℂ)).isPathConnected_compl_of_one_lt_rank hrank)
  exact (puncturedDiscHomeo s hρ).symm.surjective.pathConnectedSpace
    (puncturedDiscHomeo s hρ).symm.continuous

/-- **The fundamental group of a punctured disc is infinite cyclic.**  A loop of the punctured
disc is determined, up to homotopy, by the number of times it winds around the puncture. -/
theorem nonempty_fundamentalGroup_puncturedDisc (s : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (b : ↥(puncturedDisc s ρ)) :
    Nonempty (FundamentalGroup ↥(puncturedDisc s ρ) b ≃* Multiplicative ℤ) := by
  haveI := pathConnectedSpace_puncturedDisc s hρ
  set e := puncturedDiscHomeo s hρ with he
  set b₀ : ↥(puncturedDisc s ρ) := e.symm ⟨Complex.exp 0, (0 : ℂ).exp_ne_zero⟩ with hb₀
  have hb : e b₀ = ⟨Complex.exp 0, (0 : ℂ).exp_ne_zero⟩ := e.apply_symm_apply _
  refine ⟨((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
    (X := ↥(puncturedDisc s ρ)) b b₀).trans (e.fundamentalGroupMulEquiv b₀)).trans ?_⟩
  rw [hb]
  exact Complex.fundamentalGroupUnitsExp

/-! ### Loops around a puncture -/

/-- A punctured disc contained in a region `X` of the plane sits inside it. -/
def discIncl {X : Set ℂ} {s : ℂ} {ρ : ℝ} (h : puncturedDisc s ρ ⊆ X) :
    C(↥(puncturedDisc s ρ), ↥X) :=
  ⟨fun z => ⟨z.1, h z.2⟩, continuous_subtype_val.subtype_mk _⟩

/-- A loop of a region `X` of the plane **winds once around `s`** when it is obtained, by transport
along a path back to the basepoint, from a generator of the fundamental group of a small punctured
disc about `s` contained in `X`.  The point `s` itself is of course missing from `X`. -/
def IsPunctureLoop (X : Set ℂ) (s : ℂ) {z₀ : ℂ} (hz₀ : z₀ ∈ X)
    (γ : FundamentalGroup ↥X ⟨z₀, hz₀⟩) : Prop :=
  ∃ (ρ : ℝ) (h : puncturedDisc s ρ ⊆ X) (b : ↥(puncturedDisc s ρ))
    (g : FundamentalGroup ↥(puncturedDisc s ρ) b)
    (δ : Path (discIncl h b) (⟨z₀, hz₀⟩ : ↥X)),
    0 < ρ ∧ Subgroup.zpowers g = ⊤ ∧
      γ = FundamentalGroup.fundamentalGroupMulEquivOfPath δ (FundamentalGroup.map (discIncl h) b g)

/-- Around any point of an open set there is a punctured disc inside it and avoiding a given finite
set. -/
theorem exists_radius {W : Set ℂ} (hW : IsOpen W) {s : ℂ} (hs : s ∈ W) {S : Set ℂ}
    (hS : S.Finite) : ∃ ρ : ℝ, 0 < ρ ∧ puncturedDisc s ρ ⊆ W \ S := by
  have hclosed : IsClosed (S \ {s}) := (hS.subset Set.diff_subset).isClosed
  have hmem : s ∈ W ∩ (S \ {s})ᶜ := ⟨hs, by simp⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp (hW.inter hclosed.isOpen_compl) s hmem
  refine ⟨ρ, hρ, fun z hz => ?_⟩
  have hz1 : z ∈ Metric.ball s ρ := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact norm_sub_lt_of_mem_puncturedDisc hz
  exact ⟨(hball hz1).1, fun hzS => (hball hz1).2 ⟨hzS, (mem_puncturedDisc.mp hz).2⟩⟩

/-- The generator of an infinite cyclic group, read off a description of it. -/
theorem zpowers_ofAdd_one_eq_top : Subgroup.zpowers (Multiplicative.ofAdd (1 : ℤ)) = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  refine Subgroup.mem_zpowers_iff.mpr ⟨Multiplicative.toAdd x, ?_⟩
  simp [← ofAdd_zsmul]

/-- A punctured disc has a distinguished basepoint. -/
theorem midpoint_mem_puncturedDisc (s : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    s + ((ρ / 2 : ℝ) : ℂ) ∈ puncturedDisc s ρ := by
  have hhalf : (0 : ℝ) < ρ / 2 := by positivity
  refine mem_puncturedDisc.mpr ⟨?_, ?_⟩
  · rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hhalf]
    linarith
  · have hne : ((ρ / 2 : ℝ) : ℂ) ≠ 0 := by simpa using hhalf.ne'
    simpa using hne

/-- A punctured disc has a generator of its fundamental group at every basepoint. -/
theorem exists_zpowers_eq_top_puncturedDisc (s : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (b : ↥(puncturedDisc s ρ)) :
    ∃ g : FundamentalGroup ↥(puncturedDisc s ρ) b, Subgroup.zpowers g = ⊤ := by
  obtain ⟨e⟩ := nonempty_fundamentalGroup_puncturedDisc s hρ b
  refine ⟨e.symm (Multiplicative.ofAdd (1 : ℤ)), ?_⟩
  have h1 := MonoidHom.map_zpowers
    (e.symm : Multiplicative ℤ →* FundamentalGroup ↥(puncturedDisc s ρ) b)
    (Multiplicative.ofAdd (1 : ℤ))
  rw [zpowers_ofAdd_one_eq_top, Subgroup.map_top_of_surjective _ e.symm.surjective] at h1
  exact h1.symm

/-- **Every puncture carries a loop.**  A punctured disc about `s` inside a path connected region
`X` gives a loop of `X` at any basepoint winding once around `s`. -/
theorem exists_isPunctureLoop {X : Set ℂ} [PathConnectedSpace ↥X] {s : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : puncturedDisc s ρ ⊆ X) {z₀ : ℂ} (hz₀ : z₀ ∈ X) :
    ∃ γ : FundamentalGroup ↥X ⟨z₀, hz₀⟩, IsPunctureLoop X s hz₀ γ := by
  set b : ↥(puncturedDisc s ρ) :=
    ⟨s + ((ρ / 2 : ℝ) : ℂ), midpoint_mem_puncturedDisc s hρ⟩ with hbdef
  obtain ⟨g, hgen⟩ := exists_zpowers_eq_top_puncturedDisc s hρ b
  exact ⟨_, ρ, hsub, b, g, PathConnectedSpace.somePath (discIncl hsub b) ⟨z₀, hz₀⟩,
    hρ, hgen, rfl⟩

end Rigidity.RET

end

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Pi1.Topological.PunctureFill
import InverseGalois.Rigidity.RET.Pi1.Topological.ConvexPunctured

/-!
# A punctured disc carries all the loops of a punctured convex region

A convex region with one point removed shrinks radially into any disc about that point: the map
`z ↦ s + ρ/(1 + ‖z - s‖) · (z - s)` lands in the punctured disc, and moving a point radially
towards the puncture never crosses it and never leaves the region, because the whole segment from
the puncture to the point lies in the region.  The inclusion of the punctured disc into the
punctured region is therefore a homotopy equivalence, and it is an isomorphism on fundamental
groups.

Consequently a loop that winds once around `s` is not merely a loop drawn near `s`: its image in
the region punctured at `s` alone *generates* an infinite cyclic group, so it has infinite order,
and in particular it is not contractible.

## Main definitions

* `Rigidity.RET.discShrink` — the radial shrinking of a punctured convex region into a punctured
  disc.
* `Rigidity.RET.puncturedDiscHomotopyEquiv` — the inclusion of a punctured disc into a punctured
  convex region, as a homotopy equivalence.

## Main results

* `Rigidity.RET.fundamentalGroup_map_bijective` — a homotopy equivalence is an isomorphism on
  fundamental groups.
* `Rigidity.RET.nonempty_fundamentalGroup_diff_singleton` — a convex region with one point removed
  has infinite cyclic fundamental group.
* `Rigidity.RET.zpowers_map_subsetIncl_eq_top` — a loop winding once around a puncture generates
  the fundamental group of the region punctured at that point alone.
* `Rigidity.RET.IsPunctureLoop.ne_one` — a loop winding once around a puncture is not
  contractible.
* `Rigidity.RET.exists_punctureLoopSystem` — a system of loops, one winding around each of a
  prescribed list of points.
* `Rigidity.RET.eq_zero_of_prod_zpow_eq_one` — loops around distinct punctures are independent.
-/

open CategoryTheory FundamentalGroupoid FundamentalGroupoidFunctor ContinuousMap Topology
open scoped unitInterval

noncomputable section

namespace Rigidity.RET

/-! ### A homotopy equivalence is an isomorphism on fundamental groups -/

/-- **Homotopy equivalent spaces have equivalent fundamental groupoids.** -/
def homotopyEquivGroupoid {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₕ Y) :
    FundamentalGroupoid X ≌ FundamentalGroupoid Y :=
  CategoryTheory.Equivalence.mk (FundamentalGroupoid.map h.toFun)
      (FundamentalGroupoid.map h.invFun)
    (by simpa only [FundamentalGroupoid.map_id, FundamentalGroupoid.map_comp]
      using (asIso (homotopicMapsNatIso h.left_inv.some)).symm)
    (by simpa only [FundamentalGroupoid.map_id, FundamentalGroupoid.map_comp]
      using asIso (homotopicMapsNatIso h.right_inv.some))

/-- **A homotopy equivalence is an isomorphism on fundamental groups.** -/
theorem fundamentalGroup_map_bijective {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₕ Y) (x : X) : Function.Bijective (FundamentalGroup.map h.toFun x) := by
  have hff : (FundamentalGroupoid.map h.toFun).FullyFaithful :=
    (homotopyEquivGroupoid h).fullyFaithfulFunctor
  haveI := hff.full
  haveI := hff.faithful
  refine ⟨fun a b hab => (FundamentalGroupoid.map h.toFun).map_injective hab, fun c => ?_⟩
  obtain ⟨a, ha⟩ := (FundamentalGroupoid.map h.toFun).map_surjective c
  exact ⟨a, ha⟩

/-- The fundamental group transported along a homotopy equivalence. -/
def fundamentalGroupMulEquivOfHomotopyEquiv {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (h : X ≃ₕ Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (h.toFun x) :=
  MulEquiv.ofBijective _ (fundamentalGroup_map_bijective h x)

/-! ### The radial straight-line homotopy -/

/-- The scaling factor interpolating between a radial rescaling by `a` and the identity. -/
def radialScale (a t : ℝ) : ℝ := (1 - t) * a + t

@[simp] theorem radialScale_zero (a : ℝ) : radialScale a 0 = a := by simp [radialScale]

@[simp] theorem radialScale_one (a : ℝ) : radialScale a 1 = 1 := by simp [radialScale]

theorem radialScale_pos {a t : ℝ} (ha : 0 < a) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < radialScale a t := by
  rcases ht1.eq_or_lt with rfl | h
  · simp
  · have h1t : (0 : ℝ) < 1 - t := by linarith
    have := mul_pos h1t ha
    simp only [radialScale]
    linarith

theorem radialScale_mul_lt {a t u ρ : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (h1 : a * u < ρ)
    (h2 : u < ρ) : radialScale a t * u < ρ := by
  rcases ht1.eq_or_lt with rfl | h
  · rw [radialScale_one, one_mul]; exact h2
  · have h1t : (0 : ℝ) < 1 - t := by linarith
    have hA : (1 - t) * (a * u) < (1 - t) * ρ := mul_lt_mul_of_pos_left h1 h1t
    have hB : t * u ≤ t * ρ := mul_le_mul_of_nonneg_left h2.le ht0
    have hsplit : radialScale a t * u = (1 - t) * (a * u) + t * u := by
      simp only [radialScale]; ring
    rw [hsplit]
    linarith

/-- The radial shrinking factor of a punctured plane onto a punctured disc, as a continuous
function on any subset of the plane. -/
def radialFactor (s : ℂ) (ρ : ℝ) (X : Set ℂ) : C(↥X, ℝ) :=
  ⟨fun z => ρ / (1 + ‖(z : ℂ) - s‖), by
    refine continuous_const.div (continuous_const.add ?_) fun z => by positivity
    exact (continuous_subtype_val.sub continuous_const).norm⟩

@[simp] theorem radialFactor_apply (s : ℂ) (ρ : ℝ) (X : Set ℂ) (z : ↥X) :
    radialFactor s ρ X z = ρ / (1 + ‖(z : ℂ) - s‖) := rfl

/-- **The straight-line homotopy from a radial rescaling to the identity.**  Rescaling a point by
a positive factor along the ray through `s` never crosses `s`, so the segment joining a point to
its rescaling stays inside any set closed under such rescalings. -/
def radialHomotopy {X : Set ℂ} (s : ℂ) (ρ : ℝ) (f : C(↥X, ↥X))
    (hf : ∀ z : ↥X, (f z : ℂ) = s + (ρ / (1 + ‖(z : ℂ) - s‖)) • ((z : ℂ) - s))
    (hmem : ∀ (t : ℝ), 0 ≤ t → t ≤ 1 → ∀ z : ↥X,
      s + radialScale (ρ / (1 + ‖(z : ℂ) - s‖)) t • ((z : ℂ) - s) ∈ X) :
    ContinuousMap.Homotopy f (ContinuousMap.id ↥X) where
  toFun p :=
    ⟨s + radialScale (radialFactor s ρ X p.2) (p.1 : ℝ) • ((p.2 : ℂ) - s),
      hmem (p.1 : ℝ) p.1.2.1 p.1.2.2 p.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_const.add (Continuous.smul ?_ ?_)) _
    · show Continuous fun p : I × ↥X =>
        (1 - (p.1 : ℝ)) * (radialFactor s ρ X p.2) + (p.1 : ℝ)
      exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        ((radialFactor s ρ X).continuous.comp continuous_snd)).add
        (continuous_subtype_val.comp continuous_fst)
    · exact (continuous_subtype_val.comp continuous_snd).sub continuous_const
  map_zero_left z := Subtype.ext <| by
    simp only [Set.Icc.coe_zero, radialFactor_apply, radialScale_zero]
    exact (hf z).symm
  map_one_left z := Subtype.ext <| by
    simp only [Set.Icc.coe_one, radialScale_one, one_smul, ContinuousMap.id_apply]
    exact add_sub_cancel _ _

/-! ### The shrinking of a punctured convex region into a punctured disc -/

/-- A punctured disc inside a region sits inside the region with only its centre removed. -/
theorem puncturedDisc_subset_diff_singleton {W : Set ℂ} {s : ℂ} {ρ : ℝ}
    (hball : Metric.ball s ρ ⊆ W) : puncturedDisc s ρ ⊆ W \ {s} :=
  fun _ hz => ⟨hball hz.1, hz.2⟩

/-- A punctured disc grows with its radius. -/
theorem puncturedDisc_mono {s : ℂ} {ρ' ρ : ℝ} (hle : ρ' ≤ ρ) :
    puncturedDisc s ρ' ⊆ puncturedDisc s ρ :=
  fun _ hz => ⟨Metric.ball_subset_ball hle hz.1, hz.2⟩

/-- A punctured disc sits inside the region containing it with only its centre removed. -/
def discInclLocal {W : Set ℂ} {s : ℂ} {ρ : ℝ} (hball : Metric.ball s ρ ⊆ W) :
    C(↥(puncturedDisc s ρ), ↥(W \ {s})) :=
  discIncl (puncturedDisc_subset_diff_singleton hball)

/-- **The radial shrinking of a punctured region into a punctured disc.**  The shrinking radius
`ρ'` may be taken smaller than the radius `ρ` of the target disc; this extra room is what lets the
straight-line homotopy back to the identity stay inside a convex region. -/
def discShrink {W : Set ℂ} (s : ℂ) {ρ' ρ : ℝ} (hρ' : 0 < ρ') (hle : ρ' ≤ ρ) :
    C(↥(W \ {s}), ↥(puncturedDisc s ρ)) :=
  ⟨fun z => ⟨discIn s ρ' ((z : ℂ) - s),
      puncturedDisc_mono hle (discIn_mem hρ' (sub_ne_zero_of_ne z.2.2))⟩,
    (((continuous_discIn s ρ').comp
      (continuous_subtype_val.sub continuous_const)).subtype_mk _)⟩

/-- A point of a punctured disc stays inside it under a radial rescaling towards its centre. -/
theorem radial_mem_puncturedDisc {s : ℂ} {ρ' ρ : ℝ} (hρ' : 0 < ρ') (hle : ρ' ≤ ρ) {z : ℂ}
    (hz : z ∈ puncturedDisc s ρ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    s + radialScale (ρ' / (1 + ‖z - s‖)) t • (z - s) ∈ puncturedDisc s ρ := by
  have hu : ‖z - s‖ < ρ := norm_sub_lt_of_mem_puncturedDisc hz
  have hu0 : 0 < ‖z - s‖ := norm_pos_iff.mpr (sub_ne_zero_of_mem_puncturedDisc hz)
  have hρ : 0 < ρ := lt_of_lt_of_le hρ' hle
  have hden : (0 : ℝ) < 1 + ‖z - s‖ := by positivity
  have ha : 0 < ρ' / (1 + ‖z - s‖) := by positivity
  have hau : ρ' / (1 + ‖z - s‖) * ‖z - s‖ < ρ := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith
  have hlam : 0 < radialScale (ρ' / (1 + ‖z - s‖)) t := radialScale_pos ha ht0 ht1
  refine mem_puncturedDisc.mpr ⟨?_, ?_⟩
  · rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
    exact radialScale_mul_lt ht0 ht1 hau hu
  · intro hc
    have hnorm : ‖s + radialScale (ρ' / (1 + ‖z - s‖)) t • (z - s) - s‖ = 0 := by
      rw [hc, sub_self, norm_zero]
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hlam] at hnorm
    nlinarith [mul_pos hlam hu0]

/-- A point of a punctured convex region stays inside it under a radial rescaling towards the
puncture, provided the rescaling never pushes a point away from the centre: the rescaled point
then lies on the segment from the centre to the original point. -/
theorem radial_mem_diff_singleton {W : Set ℂ} (hconv : Convex ℝ W) {s : ℂ} (hs : s ∈ W)
    {ρ' : ℝ} (hρ' : 0 < ρ') (hρ'1 : ρ' ≤ 1) {z : ℂ} (hz : z ∈ W \ {s}) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    s + radialScale (ρ' / (1 + ‖z - s‖)) t • (z - s) ∈ W \ {s} := by
  have hzs : z ≠ s := hz.2
  have hu0 : 0 < ‖z - s‖ := norm_pos_iff.mpr (sub_ne_zero_of_ne hzs)
  have hden : (0 : ℝ) < 1 + ‖z - s‖ := by positivity
  have ha : 0 < ρ' / (1 + ‖z - s‖) := by positivity
  have ha1 : ρ' / (1 + ‖z - s‖) ≤ 1 := by rw [div_le_one hden]; linarith
  have hlam0 : 0 < radialScale (ρ' / (1 + ‖z - s‖)) t := radialScale_pos ha ht0 ht1
  have hlam1 : radialScale (ρ' / (1 + ‖z - s‖)) t ≤ 1 := by
    simp only [radialScale]
    nlinarith [mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 ha1)]
  refine ⟨?_, ?_⟩
  · have hcomb : s + radialScale (ρ' / (1 + ‖z - s‖)) t • (z - s)
        = (1 - radialScale (ρ' / (1 + ‖z - s‖)) t) • s
          + radialScale (ρ' / (1 + ‖z - s‖)) t • z := by module
    rw [hcomb]
    exact hconv hs hz.1 (by linarith) hlam0.le (by ring)
  · intro hc
    have hnorm : ‖s + radialScale (ρ' / (1 + ‖z - s‖)) t • (z - s) - s‖ = 0 := by
      rw [Set.mem_singleton_iff.mp hc, sub_self, norm_zero]
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hlam0] at hnorm
    nlinarith [mul_pos hlam0 hu0]

/-- **The inclusion of a punctured disc into a punctured convex region is a homotopy
equivalence**, in a form that keeps the shrinking radius explicit. -/
def puncturedDiscHomotopyEquivAux {W : Set ℂ} (hconv : Convex ℝ W) {s : ℂ} {ρ' ρ : ℝ}
    (hρ' : 0 < ρ') (hρ'1 : ρ' ≤ 1) (hle : ρ' ≤ ρ) (hball : Metric.ball s ρ ⊆ W) :
    ↥(puncturedDisc s ρ) ≃ₕ ↥(W \ {s}) where
  toFun := discInclLocal hball
  invFun := discShrink s hρ' hle
  left_inv :=
    ⟨radialHomotopy s ρ' ((discShrink s hρ' hle).comp (discInclLocal hball)) (fun _ => rfl)
      fun _ ht0 ht1 z => radial_mem_puncturedDisc hρ' hle z.2 ht0 ht1⟩
  right_inv :=
    ⟨radialHomotopy s ρ' ((discInclLocal hball).comp (discShrink s hρ' hle)) (fun _ => rfl)
      fun _ ht0 ht1 z =>
        radial_mem_diff_singleton hconv
          (hball (Metric.mem_ball_self (lt_of_lt_of_le hρ' hle))) hρ' hρ'1 z.2 ht0 ht1⟩

/-- **The inclusion of a punctured disc into a punctured convex region is a homotopy
equivalence.** -/
def puncturedDiscHomotopyEquiv {W : Set ℂ} (hconv : Convex ℝ W) {s : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hball : Metric.ball s ρ ⊆ W) : ↥(puncturedDisc s ρ) ≃ₕ ↥(W \ {s}) :=
  puncturedDiscHomotopyEquivAux hconv (lt_min hρ one_pos) (min_le_right _ _) (min_le_left _ _)
    hball

/-- **The loops of a punctured disc are the loops of the punctured convex region around it.** -/
theorem fundamentalGroup_map_discInclLocal_bijective {W : Set ℂ} (hconv : Convex ℝ W) {s : ℂ}
    {ρ : ℝ} (hρ : 0 < ρ) (hball : Metric.ball s ρ ⊆ W) (b : ↥(puncturedDisc s ρ)) :
    Function.Bijective (FundamentalGroup.map (discInclLocal hball) b) :=
  fundamentalGroup_map_bijective (puncturedDiscHomotopyEquiv hconv hρ hball) b

/-! ### The fundamental group of a convex region with one point removed -/

/-- **A convex region with one point removed has infinite cyclic fundamental group.** -/
theorem nonempty_fundamentalGroup_diff_singleton {W : Set ℂ} (hconv : Convex ℝ W) (hW : IsOpen W)
    {s : ℂ} (hs : s ∈ W) (y : ↥(W \ {s})) :
    Nonempty (FundamentalGroup ↥(W \ {s}) y ≃* Multiplicative ℤ) := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hW s hs
  haveI : PathConnectedSpace ↥(W \ {s}) :=
    Convex.pathConnectedSpace_diff_countable_complex hconv hW (Set.countable_singleton s)
      ⟨(y : ℂ), y.2⟩
  set b : ↥(puncturedDisc s ρ) :=
    ⟨s + ((ρ / 2 : ℝ) : ℂ), midpoint_mem_puncturedDisc s hρ⟩ with hbdef
  obtain ⟨e⟩ := nonempty_fundamentalGroup_puncturedDisc s hρ b
  exact ⟨((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected y
      (discInclLocal hball b)).trans
    (MulEquiv.ofBijective _
      (fundamentalGroup_map_discInclLocal_bijective hconv hρ hball b)).symm).trans e⟩

/-! ### A loop around a puncture is a generator, hence not contractible -/

/-- The image of a generator under a surjection is a generator. -/
theorem zpowers_map_eq_top {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) {g : G} (hg : Subgroup.zpowers g = ⊤) :
    Subgroup.zpowers (f g) = ⊤ := by
  have h1 := MonoidHom.map_zpowers f g
  rw [hg, Subgroup.map_top_of_surjective f hf] at h1
  exact h1.symm

/-- The image of a generator under an isomorphism is a generator. -/
theorem zpowers_mulEquiv_eq_top {G H : Type*} [Group G] [Group H] (e : G ≃* H) {g : G}
    (hg : Subgroup.zpowers g = ⊤) : Subgroup.zpowers (e g) = ⊤ :=
  zpowers_map_eq_top (e : G →* H) e.surjective hg

/-- **A loop winding once around a puncture generates the fundamental group of the region punctured
at that point alone.**  Filling in every puncture but `s` leaves an infinite cyclic group, and the
loop around `s` is a generator of it. -/
theorem zpowers_map_subsetIncl_eq_top {W X : Set ℂ} (hconv : Convex ℝ W) {s : ℂ} (hs : s ∈ W)
    (hsub : X ⊆ W \ {s}) {z₀ : ℂ} {hz₀ : z₀ ∈ X} {γ : FundamentalGroup ↥X ⟨z₀, hz₀⟩}
    (hγ : IsPunctureLoop X s hz₀ γ) :
    Subgroup.zpowers (FundamentalGroup.map (subsetIncl hsub) (⟨z₀, hz₀⟩ : ↥X) γ) = ⊤ := by
  obtain ⟨ρ, h, b, g, δ, hρ, hgen, rfl⟩ := hγ
  have hball : Metric.ball s ρ ⊆ W := by
    intro z hz
    rcases eq_or_ne z s with rfl | hzs
    · exact hs
    · exact (hsub (h ⟨hz, hzs⟩)).1
  rw [map_fundamentalGroupMulEquivOfPath, ← fundamentalGroup_map_comp]
  refine zpowers_mulEquiv_eq_top _ ?_
  exact zpowers_map_eq_top _
    (fundamentalGroup_map_discInclLocal_bijective hconv hρ hball b).surjective hgen

/-! ### Generators of an infinite cyclic group -/

/-- A generator of the additive integers is not zero. -/
theorem toAdd_ne_zero_of_zpowers_eq_top {m : Multiplicative ℤ}
    (hm : Subgroup.zpowers m = ⊤) : Multiplicative.toAdd m ≠ 0 := by
  intro h0
  have hone : Multiplicative.ofAdd (1 : ℤ) ∈ Subgroup.zpowers m := by
    rw [hm]; exact Subgroup.mem_top _
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hone
  have := congrArg Multiplicative.toAdd hn
  simp [h0] at this

/-- **A generator of an infinite cyclic group has infinite order.** -/
theorem eq_zero_of_zpow_eq_one {G : Type*} [Group G] (e : G ≃* Multiplicative ℤ) {g : G}
    (hg : Subgroup.zpowers g = ⊤) {n : ℤ} (hn : g ^ n = 1) : n = 0 := by
  have hm := toAdd_ne_zero_of_zpowers_eq_top (zpowers_mulEquiv_eq_top e hg)
  have h1 : (e g) ^ n = 1 := by rw [← map_zpow, hn, map_one]
  have h2 := congrArg Multiplicative.toAdd h1
  rw [toAdd_zpow, toAdd_one] at h2
  rcases mul_eq_zero.mp h2 with h | h
  · exact h
  · exact absurd h hm

/-- A generator of an infinite cyclic group is not the identity. -/
theorem ne_one_of_zpowers_eq_top {G : Type*} [Group G] (e : G ≃* Multiplicative ℤ) {g : G}
    (hg : Subgroup.zpowers g = ⊤) : g ≠ 1 := fun h =>
  one_ne_zero (eq_zero_of_zpow_eq_one e hg (n := 1) (by simpa using h))

/-- **A loop winding once around a puncture is not contractible.** -/
theorem IsPunctureLoop.ne_one {W X : Set ℂ} (hconv : Convex ℝ W) (hW : IsOpen W) {s : ℂ}
    (hs : s ∈ W) (hsub : X ⊆ W \ {s}) {z₀ : ℂ} {hz₀ : z₀ ∈ X}
    {γ : FundamentalGroup ↥X ⟨z₀, hz₀⟩} (hγ : IsPunctureLoop X s hz₀ γ) : γ ≠ 1 := by
  intro hone
  obtain ⟨e⟩ :=
    nonempty_fundamentalGroup_diff_singleton hconv hW hs (subsetIncl hsub (⟨z₀, hz₀⟩ : ↥X))
  refine ne_one_of_zpowers_eq_top e (zpowers_map_subsetIncl_eq_top hconv hs hsub hγ) ?_
  rw [hone, map_one]

/-! ### A system of loops, one around each puncture -/

/-- **Every finite set of punctures carries a system of loops, one winding around each.** -/
theorem exists_punctureLoopSystem {W : Set ℂ} (hW : IsOpen W) {S : Set ℂ} (hS : S.Finite)
    [PathConnectedSpace ↥(W \ S)] {r : ℕ} {t : Fin r → ℂ} (ht : ∀ i, t i ∈ W) {z₀ : ℂ}
    (hz₀ : z₀ ∈ W \ S) :
    ∃ γ : Fin r → FundamentalGroup ↥(W \ S) ⟨z₀, hz₀⟩,
      ∀ i, IsPunctureLoop (W \ S) (t i) hz₀ (γ i) := by
  choose ρ hρ hsub using fun i => exists_radius hW (ht i) hS
  exact ⟨fun i => (exists_isPunctureLoop (hρ i) (hsub i) hz₀).choose,
    fun i => (exists_isPunctureLoop (hρ i) (hsub i) hz₀).choose_spec⟩

/-- **Loops around distinct punctures are independent.**  Filling in every puncture but one turns
the region into a region with a single point removed, where only the loop around the surviving
puncture is visible; so a product of powers of loops around distinct punctures is trivial only if
every exponent vanishes. -/
theorem eq_zero_of_prod_zpow_eq_one {W : Set ℂ} (hconv : Convex ℝ W) (hW : IsOpen W) {S : Set ℂ}
    (hSW : S ⊆ W) {r : ℕ} {t : Fin r → ℂ} (ht : Function.Injective t) (hts : ∀ i, t i ∈ S)
    {z₀ : ℂ} {hz₀ : z₀ ∈ W \ S} {γ : Fin r → FundamentalGroup ↥(W \ S) ⟨z₀, hz₀⟩}
    (hγ : ∀ i, IsPunctureLoop (W \ S) (t i) hz₀ (γ i)) {n : Fin r → ℤ}
    (hn : (List.ofFn fun j => γ j ^ n j).prod = 1) (i : Fin r) : n i = 0 := by
  have hsub : W \ S ⊆ W \ {t i} :=
    Set.diff_subset_diff_right (Set.singleton_subset_iff.mpr (hts i))
  obtain ⟨e⟩ := nonempty_fundamentalGroup_diff_singleton hconv hW (hSW (hts i))
    (subsetIncl hsub (⟨z₀, hz₀⟩ : ↥(W \ S)))
  set f : FundamentalGroup ↥(W \ S) ⟨z₀, hz₀⟩ →* Multiplicative ℤ :=
    (e : _ →* Multiplicative ℤ).comp
      (FundamentalGroup.map (subsetIncl hsub) ⟨z₀, hz₀⟩) with hfdef
  have hzero : ∀ j, j ≠ i → f (γ j) = 1 := by
    intro j hj
    have hne : t j ∈ W \ {t i} :=
      ⟨hSW (hts j), fun hc => hj (ht (Set.mem_singleton_iff.mp hc))⟩
    have := map_eq_one_of_isPunctureLoop hsub hne (hγ j)
    rw [hfdef]
    simp only [MonoidHom.coe_comp, Function.comp_apply, this, map_one]
  have hgen : Subgroup.zpowers (f (γ i)) = ⊤ :=
    zpowers_mulEquiv_eq_top e (zpowers_map_subsetIncl_eq_top hconv (hSW (hts i)) hsub (hγ i))
  have hmap : (List.ofFn fun j => f (γ j) ^ n j).prod = 1 := by
    have h := congrArg f hn
    rw [map_one, map_list_prod, List.map_ofFn] at h
    simpa [Function.comp_def] using h
  rw [List.prod_ofFn] at hmap
  rw [Finset.prod_eq_single i (fun j _ hj => by rw [hzero j hj, one_zpow])
    (fun hi => absurd (Finset.mem_univ i) hi)] at hmap
  exact eq_zero_of_zpow_eq_one (MulEquiv.refl _) hgen hmap

end Rigidity.RET

end

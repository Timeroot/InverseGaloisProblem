/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Pi1.Topological.CircleLoop
import InverseGalois.Rigidity.RET.Pi1.Topological.Exterior

/-!
# The loop at infinity

The exterior of a disc is a neighbourhood of the point at infinity of the line with that point
removed, so it plays at infinity the role a punctured disc plays at a point of the line.  Inversion
identifies the two: it carries the exterior of the disc of radius `R` homeomorphically onto the
punctured disc of radius `R⁻¹` about the origin.

The loop that winds once around the point at infinity is therefore the circle, traversed
*clockwise*: inversion reverses the sense of rotation, so the clockwise circle of the exterior is
carried exactly onto the counterclockwise circle of the punctured disc, on the nose and with no
reparametrisation.  Since the latter generates, so does the former.

## Main definitions

* `Rigidity.RET.extRegionHomeo` — inversion, as a homeomorphism of an exterior region onto a
  punctured disc.
* `Rigidity.RET.extLoop` — the loop of an exterior region running once around the point at infinity
  through a given point.
* `Rigidity.RET.IsSupportedAtInfinity` — a loop of a region of the plane comes from a loop of an
  exterior region.

## Main results

* `Rigidity.RET.zpowers_extLoop_eq_top` — the loop at infinity generates the fundamental group of an
  exterior region.
* `Rigidity.RET.isSupportedAtInfinity_extLoop` — the loop at infinity is supported at the point at
  infinity, at any basepoint.
-/

open Topology unitInterval

noncomputable section

namespace Rigidity.RET

/-! ### Inversion identifies an exterior region with a punctured disc -/

theorem inv_mem_puncturedDisc_of_mem_extRegion {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ extRegion R) : z⁻¹ ∈ puncturedDisc (0 : ℂ) R⁻¹ := by
  have hz0 : z ≠ 0 := ne_zero_of_mem_extRegion hR.le hz
  refine mem_puncturedDisc.mpr ⟨?_, inv_ne_zero hz0⟩
  rw [sub_zero, norm_inv]
  exact (inv_lt_inv₀ (norm_pos_iff.2 hz0) hR).2 hz

theorem inv_mem_extRegion_of_mem_puncturedDisc {R : ℝ} (hR : 0 < R) {w : ℂ}
    (hw : w ∈ puncturedDisc (0 : ℂ) R⁻¹) : w⁻¹ ∈ extRegion R :=
  inv_mem_extRegion hR le_rfl w hw

/-- **An exterior region is a punctured disc.**  Inversion carries the points of norm more than `R`
onto the points of norm less than `R⁻¹` other than the origin. -/
def extRegionHomeo {R : ℝ} (hR : 0 < R) : ↥(extRegion R) ≃ₜ ↥(puncturedDisc (0 : ℂ) R⁻¹) where
  toFun z := ⟨(z : ℂ)⁻¹, inv_mem_puncturedDisc_of_mem_extRegion hR z.2⟩
  invFun w := ⟨(w : ℂ)⁻¹, inv_mem_extRegion_of_mem_puncturedDisc hR w.2⟩
  left_inv _ := Subtype.ext (inv_inv _)
  right_inv _ := Subtype.ext (inv_inv _)
  continuous_toFun :=
    (continuousOn_inv₀.comp_continuous continuous_subtype_val
      fun z => ne_zero_of_mem_extRegion hR.le z.2).subtype_mk _
  continuous_invFun :=
    (continuousOn_inv₀.comp_continuous continuous_subtype_val
      fun w => (mem_puncturedDisc.mp w.2).2).subtype_mk _

@[simp] theorem coe_extRegionHomeo {R : ℝ} (hR : 0 < R) (z : ↥(extRegion R)) :
    ((extRegionHomeo hR z : ↥(puncturedDisc (0 : ℂ) R⁻¹)) : ℂ) = (z : ℂ)⁻¹ := rfl

/-- An exterior region is path connected. -/
theorem pathConnectedSpace_extRegion {R : ℝ} (hR : 0 < R) :
    PathConnectedSpace ↥(extRegion R) := by
  haveI := pathConnectedSpace_puncturedDisc (0 : ℂ) (inv_pos.2 hR)
  exact (extRegionHomeo hR).symm.surjective.pathConnectedSpace (extRegionHomeo hR).symm.continuous

/-! ### The loop at infinity -/

theorem extCircle_mem_extRegion {R : ℝ} {b : ℂ} (hb : b ∈ extRegion R) (t : ℝ) :
    Complex.exp (-(t : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * b ∈ extRegion R := by
  have hnorm : ‖Complex.exp (-(t : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))‖ = 1 := by
    rw [show -(t : ℂ) = (((-t : ℝ)) : ℂ) by push_cast; ring]
    exact norm_exp_two_pi_mul_I _
  rw [mem_extRegion, norm_mul, hnorm, one_mul]
  exact hb

/-- The loop of an exterior region running once around the point at infinity through a given point:
the circle through that point, traversed clockwise. -/
def extLoop {R : ℝ} (b : ↥(extRegion R)) : Path b b where
  toFun t :=
    ⟨Complex.exp (-(((t : ℝ)) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * (b : ℂ),
      extCircle_mem_extRegion b.2 _⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  source' := by
    refine Subtype.ext ?_
    simp
  target' := by
    refine Subtype.ext ?_
    show Complex.exp (-((((1 : I) : ℝ)) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * (b : ℂ)
      = (b : ℂ)
    rw [Set.Icc.coe_one, Complex.ofReal_one, neg_mul, one_mul, Complex.exp_neg,
      Complex.exp_two_pi_mul_I, inv_one, one_mul]

@[simp] theorem coe_extLoop {R : ℝ} (b : ↥(extRegion R)) (t : I) :
    ((extLoop b t : ↥(extRegion R)) : ℂ)
      = Complex.exp (-(((t : ℝ)) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * (b : ℂ) := rfl

/-- **Inversion carries the loop at infinity to the circle loop of a punctured disc**, on the nose:
inverting the clockwise circle of radius `r` gives the counterclockwise circle of radius `r⁻¹`, with
the same parametrisation. -/
theorem map_extLoop {R : ℝ} (hR : 0 < R) (b : ↥(extRegion R)) :
    (extLoop b).map (extRegionHomeo hR).continuous = discLoop 0 (extRegionHomeo hR b) := by
  refine Path.ext (funext fun t => Subtype.ext ?_)
  show (Complex.exp (-(((t : ℝ)) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * (b : ℂ))⁻¹
    = 0 + Complex.exp ((((t : ℝ)) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * ((b : ℂ)⁻¹ - 0)
  rw [zero_add, sub_zero, mul_inv, neg_mul, Complex.exp_neg, inv_inv]

/-- **The loop at infinity generates the fundamental group of an exterior region.**  Inversion is a
homeomorphism onto a punctured disc, hence an isomorphism on fundamental groups, and it carries the
loop at infinity to the circle loop of the disc. -/
theorem zpowers_extLoop_eq_top {R : ℝ} (hR : 0 < R) (b : ↥(extRegion R)) :
    Subgroup.zpowers
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (extLoop b))) = ⊤ := by
  set φ := extRegionHomeo hR with hφ
  set F := FundamentalGroup.map (φ.toHomotopyEquiv.toFun) b with hF
  have hinj : Function.Injective F := (fundamentalGroup_map_bijective φ.toHomotopyEquiv b).1
  have hFγ : F (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (extLoop b)))
      = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (discLoop 0 (φ b))) := by
    show Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.mk (extLoop b))
        φ.toHomotopyEquiv.toFun = Path.Homotopic.Quotient.mk (discLoop 0 (φ b))
    rw [← Path.Homotopic.Quotient.mk_map, map_extLoop]
  refine eq_top_iff.mpr fun y _ => ?_
  have hmem : F y ∈ Subgroup.zpowers
      (F (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (extLoop b)))) := by
    rw [hFγ, zpowers_discLoop_eq_top 0 (inv_pos.2 hR)]
    exact Subgroup.mem_top _
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
  exact Subgroup.mem_zpowers_iff.mpr ⟨n, hinj (by rwa [map_zpow])⟩

/-! ### Loops around the point at infinity -/

/-- An exterior region contained in a region `X` of the plane sits inside it. -/
def extIncl {X : Set ℂ} {R : ℝ} (h : extRegion R ⊆ X) : C(↥(extRegion R), ↥X) :=
  ⟨fun z => ⟨z.1, h z.2⟩, continuous_subtype_val.subtype_mk _⟩

@[simp] theorem coe_extIncl {X : Set ℂ} {R : ℝ} (h : extRegion R ⊆ X) (z : ↥(extRegion R)) :
    ((extIncl h z : ↥X) : ℂ) = (z : ℂ) := rfl

/-- A loop of a region `X` of the plane is **supported at the point at infinity** when it is
obtained, by transport along a path back to the basepoint, from a loop of an exterior region
contained in `X`. -/
def IsSupportedAtInfinity (X : Set ℂ) {z₀ : ℂ} (hz₀ : z₀ ∈ X)
    (γ : FundamentalGroup ↥X ⟨z₀, hz₀⟩) : Prop :=
  ∃ (R : ℝ) (h : extRegion R ⊆ X) (b : ↥(extRegion R))
    (g : FundamentalGroup ↥(extRegion R) b)
    (δ : Path (extIncl h b) (⟨z₀, hz₀⟩ : ↥X)),
    0 < R ∧
      γ = FundamentalGroup.fundamentalGroupMulEquivOfPath δ (FundamentalGroup.map (extIncl h) b g)

/-- The inverse of a loop supported at the point at infinity is supported there too. -/
theorem IsSupportedAtInfinity.inv {X : Set ℂ} {z₀ : ℂ} {hz₀ : z₀ ∈ X}
    {γ : FundamentalGroup ↥X ⟨z₀, hz₀⟩} (h : IsSupportedAtInfinity X hz₀ γ) :
    IsSupportedAtInfinity X hz₀ γ⁻¹ := by
  obtain ⟨R, hsub, b, g, δ, hR, rfl⟩ := h
  exact ⟨R, hsub, b, g⁻¹, δ, hR, by rw [map_inv, map_inv]⟩

/-- An exterior region has a distinguished basepoint. -/
theorem two_mul_mem_extRegion {R : ℝ} (hR : 0 < R) : ((2 * R : ℝ) : ℂ) ∈ extRegion R := by
  rw [mem_extRegion, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  linarith

/-- **The loop at infinity is supported at the point at infinity**, at any basepoint of a region
containing an exterior region and joined to it by a path. -/
theorem isSupportedAtInfinity_extLoop {X : Set ℂ} {R : ℝ} (hR : 0 < R)
    (hsub : extRegion R ⊆ X) (b : ↥(extRegion R)) {z₀ : ℂ} (hz₀ : z₀ ∈ X)
    (δ : Path (extIncl hsub b) (⟨z₀, hz₀⟩ : ↥X)) :
    IsSupportedAtInfinity X hz₀
      (FundamentalGroup.fundamentalGroupMulEquivOfPath δ
        (FundamentalGroup.map (extIncl hsub) b
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (extLoop b))))) :=
  ⟨R, hsub, b, _, δ, hR, rfl⟩

end Rigidity.RET

end

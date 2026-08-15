/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Rigidity.RET.Pi1.Topological.PowerDisc

/-!
# The parameter at infinity multiplies loops by its exponent

The exterior of a large disc is the neighbourhood of the point at infinity of the line, and the
parameter that describes it is `u ↦ (uᵈ)⁻¹`: as `u` runs over a small punctured disc at the origin
the value runs over the exterior, wrapping `d` times.  On fundamental groups this parameter
multiplies by `d`, exactly as the Kummer coordinate does at a point of the line.

Nothing new has to be proved for that.  Inversion carries a punctured disc at the origin onto the
exterior of a disc, so the parameter at infinity is the Kummer coordinate `u ↦ uᵈ` at the origin
followed by a continuous map, and a `d`-th power stays a `d`-th power when pushed forward.

## Main definitions

* `Rigidity.RET.extRegion` — the exterior of a closed disc centred at the origin.
* `Rigidity.RET.invRegionMap` — inversion, from a punctured disc into an exterior region.
* `Rigidity.RET.invPowRegionMap` — the parameter at infinity `u ↦ (uᵈ)⁻¹`, as a map between
  regions of the plane.

## Main results

* `Rigidity.RET.inv_mem_extRegion` — inversion maps a small punctured disc into an exterior region.
* `Rigidity.RET.exists_eq_pow_map_invPowRegionMap` — the image of a loop under the parameter at
  infinity is a `d`-th power.
-/

noncomputable section

namespace Rigidity.RET

/-! ### The exterior of a disc -/

/-- The **exterior region** of radius `R`: the points of the plane of norm more than `R`.  For
`R` at least the norm of every branch point it is a neighbourhood of the point at infinity meeting
no branch point. -/
def extRegion (R : ℝ) : Set ℂ := {z : ℂ | R < ‖z‖}

theorem mem_extRegion {R : ℝ} {z : ℂ} : z ∈ extRegion R ↔ R < ‖z‖ := Iff.rfl

theorem isOpen_extRegion (R : ℝ) : IsOpen (extRegion R) :=
  isOpen_lt continuous_const continuous_norm

theorem ne_zero_of_mem_extRegion {R : ℝ} (hR : 0 ≤ R) {z : ℂ} (hz : z ∈ extRegion R) : z ≠ 0 := by
  intro h
  rw [h, mem_extRegion, norm_zero] at hz
  exact absurd hz (not_lt.2 hR)

/-! ### Inversion into the exterior -/

/-- **Inversion maps a small punctured disc into an exterior region.** -/
theorem inv_mem_extRegion {ρ R : ℝ} (hR : 0 < R) (hρ : ρ ≤ R⁻¹) :
    ∀ z ∈ puncturedDisc (0 : ℂ) ρ, z⁻¹ ∈ extRegion R := by
  intro z hz
  obtain ⟨hlt, hne⟩ := mem_puncturedDisc.mp hz
  rw [sub_zero] at hlt
  have hpos : 0 < ‖z‖ := norm_pos_iff.2 hne
  have hlt' : ‖z‖ < R⁻¹ := lt_of_lt_of_le hlt hρ
  rw [mem_extRegion, norm_inv, ← inv_inv R]
  exact (inv_lt_inv₀ (inv_pos.2 hR) hpos).2 hlt'

/-- **Inversion**, as a map from a punctured disc at the origin to an exterior region. -/
def invRegionMap {ρ R : ℝ} (h : ∀ z ∈ puncturedDisc (0 : ℂ) ρ, z⁻¹ ∈ extRegion R) :
    C(↥(puncturedDisc (0 : ℂ) ρ), ↥(extRegion R)) :=
  ⟨fun z => ⟨(z : ℂ)⁻¹, h z z.2⟩,
    ((continuousOn_inv₀.comp_continuous continuous_subtype_val
      fun z => (mem_puncturedDisc.mp z.2).2)).subtype_mk _⟩

@[simp] theorem coe_invRegionMap {ρ R : ℝ}
    (h : ∀ z ∈ puncturedDisc (0 : ℂ) ρ, z⁻¹ ∈ extRegion R) (z : ↥(puncturedDisc (0 : ℂ) ρ)) :
    ((invRegionMap h z : ↥(extRegion R)) : ℂ) = (z : ℂ)⁻¹ := rfl

/-! ### The parameter at infinity -/

/-- The **parameter at infinity** `u ↦ (uᵈ)⁻¹`, as a map from a punctured disc at the origin to an
exterior region: the Kummer coordinate at the origin followed by inversion. -/
def invPowRegionMap {ρ' ρ R : ℝ} (d : ℕ)
    (hmap : ∀ u ∈ puncturedDisc (0 : ℂ) ρ', (0 : ℂ) + u ^ d ∈ puncturedDisc (0 : ℂ) ρ)
    (hinv : ∀ z ∈ puncturedDisc (0 : ℂ) ρ, z⁻¹ ∈ extRegion R) :
    C(↥(puncturedDisc (0 : ℂ) ρ'), ↥(extRegion R)) :=
  (invRegionMap hinv).comp (kummerRegionMap 0 d hmap)

@[simp] theorem coe_invPowRegionMap {ρ' ρ R : ℝ} (d : ℕ)
    (hmap : ∀ u ∈ puncturedDisc (0 : ℂ) ρ', (0 : ℂ) + u ^ d ∈ puncturedDisc (0 : ℂ) ρ)
    (hinv : ∀ z ∈ puncturedDisc (0 : ℂ) ρ, z⁻¹ ∈ extRegion R)
    (u : ↥(puncturedDisc (0 : ℂ) ρ')) :
    ((invPowRegionMap d hmap hinv u : ↥(extRegion R)) : ℂ) = ((u : ℂ) ^ d)⁻¹ := by
  show ((0 : ℂ) + (u : ℂ) ^ d)⁻¹ = ((u : ℂ) ^ d)⁻¹
  rw [zero_add]

/-- **The image of a loop under the parameter at infinity is a `d`-th power.**  A loop of a
punctured disc around the origin, transported by `u ↦ (uᵈ)⁻¹` into the exterior of a disc, is a
`d`-th power in the fundamental group of the exterior region. -/
theorem exists_eq_pow_map_invPowRegionMap {ρ' ρ R : ℝ} (hρ : 0 < ρ) (d : ℕ)
    (hmap : ∀ u ∈ puncturedDisc (0 : ℂ) ρ', (0 : ℂ) + u ^ d ∈ puncturedDisc (0 : ℂ) ρ)
    (hinv : ∀ z ∈ puncturedDisc (0 : ℂ) ρ, z⁻¹ ∈ extRegion R)
    (b : ↥(puncturedDisc (0 : ℂ) ρ'))
    (γ : FundamentalGroup ↥(puncturedDisc (0 : ℂ) ρ') b) :
    ∃ t : FundamentalGroup ↥(extRegion R) (invPowRegionMap d hmap hinv b),
      FundamentalGroup.map (invPowRegionMap d hmap hinv) b γ = t ^ d := by
  obtain ⟨t₀, ht₀⟩ := exists_eq_pow_map_kummerRegionMap hρ 0 d hmap b γ
  refine ⟨FundamentalGroup.map (invRegionMap hinv) (kummerRegionMap 0 d hmap b) t₀, ?_⟩
  have hcomp : FundamentalGroup.map (invPowRegionMap d hmap hinv) b γ
      = FundamentalGroup.map (invRegionMap hinv) (kummerRegionMap 0 d hmap b)
          (FundamentalGroup.map (kummerRegionMap 0 d hmap) b γ) :=
    fundamentalGroup_map_comp _ _ b γ
  rw [hcomp, ht₀, map_pow]

end Rigidity.RET

end

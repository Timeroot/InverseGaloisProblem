/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Rigidity.RET.Pi1.Topological.PowerBase
import InverseGalois.Rigidity.RET.Pi1.Topological.PunctureLocal

/-!
# The Kummer coordinate multiplies loops by its exponent

The Kummer coordinate `u ↦ s + uᵉ` maps a small punctured disc around the origin into a punctured
disc around `s`.  On fundamental groups it multiplies by `e`: a loop winding once around the
origin has an image winding `e` times around `s`.  What a comparison of covers actually needs is
only the divisibility, that the image is an `e`-th power, and that weaker statement is available
without ever naming a generator.

The proof factors the Kummer coordinate, followed by the inclusion of the target disc into the
plane punctured at `s`, through the multiplicative group of the plane: shifting by `s` identifies
the plane punctured at `s` with the units, and in the units the Kummer coordinate is literally the
`e`-th power map, which raises loops to their `e`-th power.  The inclusion of a punctured disc into
the punctured plane is an isomorphism on fundamental groups, so the `e`-th root can be pulled back
into the disc.

## Main definitions

* `Rigidity.RET.kummerRegionMap` — the Kummer coordinate as a map between regions of the plane.
* `Rigidity.RET.unitsRegionMap` — a region avoiding the origin, viewed inside the units.
* `Rigidity.RET.shiftUnitsMap` — translation by `s`, from the units to the plane punctured at `s`.

## Main results

* `Rigidity.RET.exists_eq_pow_of_bijective` — a bijective homomorphism reflects `n`-th powers.
* `Rigidity.RET.isOpen_puncturedDisc` — a punctured disc is open.
* `Rigidity.RET.kummer_mem_puncturedDisc` — the Kummer coordinate maps a punctured disc of radius
  `ρ'` into the punctured disc of radius `ρ'ᵉ`.
* `Rigidity.RET.exists_eq_pow_map_kummerRegionMap` — the image of a loop under the Kummer
  coordinate is an `e`-th power.
-/

noncomputable section

namespace Rigidity.RET

/-! ### Reflecting powers along a bijective homomorphism -/

/-- **A bijective homomorphism reflects `n`-th powers.** -/
theorem exists_eq_pow_of_bijective {H₁ H₂ : Type*} [Group H₁] [Group H₂] (f : H₁ →* H₂)
    (hf : Function.Bijective f) {x : H₁} {y : H₂} {n : ℕ} (h : f x = y ^ n) :
    ∃ t : H₁, x = t ^ n := by
  obtain ⟨t, rfl⟩ := hf.2 y
  exact ⟨t, hf.1 (by rw [h, map_pow])⟩

/-! ### The three maps -/

/-- The **Kummer coordinate** `u ↦ s + uᵉ`, as a map between regions of the plane. -/
def kummerRegionMap {A B : Set ℂ} (s : ℂ) (e : ℕ) (h : ∀ u ∈ A, s + u ^ e ∈ B) : C(↥A, ↥B) :=
  ⟨fun u => ⟨s + (u : ℂ) ^ e, h u u.2⟩,
    (continuous_const.add (continuous_subtype_val.pow e)).subtype_mk _⟩

@[simp] theorem coe_kummerRegionMap {A B : Set ℂ} (s : ℂ) (e : ℕ) (h : ∀ u ∈ A, s + u ^ e ∈ B)
    (u : ↥A) : ((kummerRegionMap s e h u : ↥B) : ℂ) = s + (u : ℂ) ^ e := rfl

/-- A **region avoiding the origin**, viewed inside the multiplicative group of the plane. -/
def unitsRegionMap {A : Set ℂ} (hA : ∀ u ∈ A, u ≠ 0) : C(↥A, ℂˣ) :=
  ⟨fun u => Units.mk0 (u : ℂ) (hA u u.2), Units.continuous_iff.2
    ⟨continuous_subtype_val,
      continuousOn_inv₀.comp_continuous continuous_subtype_val fun u => hA u u.2⟩⟩

@[simp] theorem coe_unitsRegionMap {A : Set ℂ} (hA : ∀ u ∈ A, u ≠ 0) (u : ↥A) :
    ((unitsRegionMap hA u : ℂˣ) : ℂ) = (u : ℂ) := rfl

/-- **Translation by `s`**, from the multiplicative group of the plane to the plane punctured at
`s`. -/
def shiftUnitsMap (s : ℂ) : C(ℂˣ, ↥((Set.univ : Set ℂ) \ {s})) :=
  ⟨fun v => ⟨s + (v : ℂ), ⟨Set.mem_univ _, fun hv => v.ne_zero
      (by simpa using Set.mem_singleton_iff.mp hv)⟩⟩,
    (continuous_const.add Units.continuous_val).subtype_mk _⟩

@[simp] theorem coe_shiftUnitsMap (s : ℂ) (v : ℂˣ) :
    ((shiftUnitsMap s v : ↥((Set.univ : Set ℂ) \ {s})) : ℂ) = s + (v : ℂ) := rfl

/-! ### The Kummer coordinate lands in a punctured disc -/

/-- **A punctured disc is open.** -/
theorem isOpen_puncturedDisc (s : ℂ) (ρ : ℝ) : IsOpen (puncturedDisc s ρ) :=
  Metric.isOpen_ball.sdiff isClosed_singleton

/-- **The Kummer coordinate maps a punctured disc of radius `ρ'` into the punctured disc of radius
`ρ'ᵉ`.** -/
theorem kummer_mem_puncturedDisc {ρ' ρ : ℝ} {e : ℕ} (he : e ≠ 0) (hρ : ρ' ^ e ≤ ρ) (s : ℂ) :
    ∀ u ∈ puncturedDisc (0 : ℂ) ρ', s + u ^ e ∈ puncturedDisc s ρ := by
  intro u hu
  obtain ⟨hlt, hne⟩ := mem_puncturedDisc.mp hu
  rw [sub_zero] at hlt
  refine mem_puncturedDisc.mpr ⟨?_, ?_⟩
  · rw [add_sub_cancel_left, norm_pow]
    exact lt_of_lt_of_le (pow_lt_pow_left₀ hlt (norm_nonneg u) he) hρ
  · exact fun hcon => pow_ne_zero e hne (by simpa using hcon)

/-! ### The degree computation -/

/-- **The image of a loop under the Kummer coordinate is an `e`-th power.**  A loop of a punctured
disc around the origin, transported by `u ↦ s + uᵉ` into a punctured disc around `s`, is an `e`-th
power in the fundamental group of the target. -/
theorem exists_eq_pow_map_kummerRegionMap {ρ' ρ : ℝ} (hρ : 0 < ρ) (s : ℂ) (e : ℕ)
    (hmap : ∀ u ∈ puncturedDisc (0 : ℂ) ρ', s + u ^ e ∈ puncturedDisc s ρ)
    (b : ↥(puncturedDisc (0 : ℂ) ρ'))
    (γ : FundamentalGroup ↥(puncturedDisc (0 : ℂ) ρ') b) :
    ∃ t : FundamentalGroup ↥(puncturedDisc s ρ) (kummerRegionMap s e hmap b),
      FundamentalGroup.map (kummerRegionMap s e hmap) b γ = t ^ e := by
  have hA : ∀ u ∈ puncturedDisc (0 : ℂ) ρ', u ≠ 0 := fun u hu => (mem_puncturedDisc.mp hu).2
  have hball : Metric.ball s ρ ⊆ (Set.univ : Set ℂ) := fun _ _ => Set.mem_univ _
  obtain ⟨t₀, ht₀⟩ := exists_eq_pow_map_npowMap e (unitsRegionMap hA b)
    (FundamentalGroup.map (unitsRegionMap hA) b γ)
  have key : FundamentalGroup.map (discInclLocal hball) (kummerRegionMap s e hmap b)
      (FundamentalGroup.map (kummerRegionMap s e hmap) b γ)
      = (FundamentalGroup.map (shiftUnitsMap s) ((unitsRegionMap hA b) ^ e) t₀) ^ e :=
    calc FundamentalGroup.map (discInclLocal hball) (kummerRegionMap s e hmap b)
            (FundamentalGroup.map (kummerRegionMap s e hmap) b γ)
        = FundamentalGroup.map ((discInclLocal hball).comp (kummerRegionMap s e hmap)) b γ :=
          (fundamentalGroup_map_comp _ _ b γ).symm
      _ = FundamentalGroup.map
            ((shiftUnitsMap s).comp ((npowMap ℂˣ e).comp (unitsRegionMap hA))) b γ := rfl
      _ = FundamentalGroup.map (shiftUnitsMap s) _
            (FundamentalGroup.map ((npowMap ℂˣ e).comp (unitsRegionMap hA)) b γ) :=
          fundamentalGroup_map_comp _ _ b γ
      _ = FundamentalGroup.map (shiftUnitsMap s) _
            (FundamentalGroup.map (npowMap ℂˣ e) (unitsRegionMap hA b)
              (FundamentalGroup.map (unitsRegionMap hA) b γ)) := by
          rw [fundamentalGroup_map_comp]
          rfl
      _ = FundamentalGroup.map (shiftUnitsMap s) _ (t₀ ^ e) := by rw [ht₀]; rfl
      _ = (FundamentalGroup.map (shiftUnitsMap s) _ t₀) ^ e := map_pow _ _ _
  exact exists_eq_pow_of_bijective _
    (fundamentalGroup_map_discInclLocal_bijective convex_univ hρ hball _) key

end Rigidity.RET

end

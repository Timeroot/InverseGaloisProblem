/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Pi1.Topological.Lifting
import InverseGalois.Rigidity.RET.Pi1.Topological.PowerDisc
import InverseGalois.Rigidity.RET.Pi1.Topological.PunctureFill

/-!
# The Kummer coordinate lifts through a covering

A covering of a region of the plane need not have a section over a punctured disc around a boundary
point: following the puncture permutes the sheets.  Passing to the Kummer coordinate `u ↦ s + uᵉ`
multiplies loops of the punctured disc by `e`, so the obstruction disappears as soon as the `e`-th
power of the local monodromy fixes the sheet one wants to follow.  On the `e`-fold Kummer cover of
the punctured disc the chosen sheet is then a genuine continuous map.

The proof is the lifting criterion for covering spaces, in the monodromy form: the image of a loop
of the source punctured disc is an `e`-th power in the fundamental group of the target punctured
disc, so its monodromy is an `e`-th power of a permutation of the fibre and fixes the chosen point
by hypothesis.

## Main results

* `Rigidity.RET.exists_lift_kummerRegionMap` — the Kummer coordinate lifts through a covering
  through a prescribed point of the fibre.
* `Rigidity.RET.exists_lift_kummerRegionMap_of_gen` — the same, checking only a generator of the
  fundamental group of the punctured disc.
-/

noncomputable section

namespace Rigidity.RET

variable {E : Type*} [TopologicalSpace E] {X : Set ℂ} {p : E → ↥X}

/-- **The Kummer coordinate lifts through a covering.**  If the `e`-th power of the monodromy of
every loop of a punctured disc around `s` fixes a chosen point of the fibre, then the Kummer
coordinate `u ↦ s + uᵉ` of a punctured disc at the origin lifts to the total space of the covering
through that point. -/
theorem exists_lift_kummerRegionMap (cov : IsCoveringMap p) {s : ℂ} {ρ ρ' : ℝ} {e : ℕ}
    (hρ : 0 < ρ) (hρ' : 0 < ρ') (hsub : puncturedDisc s ρ ⊆ X)
    (hmap : ∀ u ∈ puncturedDisc (0 : ℂ) ρ', s + u ^ e ∈ puncturedDisc s ρ)
    (b : ↥(puncturedDisc (0 : ℂ) ρ')) {q₀ : E}
    (hq₀ : p q₀ = subsetIncl hsub (kummerRegionMap s e hmap b))
    (hexp : ∀ τ : FundamentalGroup ↥(puncturedDisc s ρ) (kummerRegionMap s e hmap b),
      (cov.monodromyHom (subsetIncl hsub (kummerRegionMap s e hmap b))
            (FundamentalGroup.map (subsetIncl hsub) (kummerRegionMap s e hmap b) τ) ^ e)
          ⟨q₀, hq₀⟩ = ⟨q₀, hq₀⟩) :
    ∃ F : C(↥(puncturedDisc (0 : ℂ) ρ'), E), F b = q₀ ∧
      ∀ u : ↥(puncturedDisc (0 : ℂ) ρ'), ((p (F u) : ℂ)) = s + (u : ℂ) ^ e := by
  haveI : PathConnectedSpace ↥(puncturedDisc (0 : ℂ) ρ') :=
    pathConnectedSpace_puncturedDisc 0 hρ'
  haveI : LocPathConnectedSpace ↥(puncturedDisc (0 : ℂ) ρ') :=
    (isOpen_puncturedDisc (0 : ℂ) ρ').locPathConnectedSpace
  set κ : C(↥(puncturedDisc (0 : ℂ) ρ'), ↥(puncturedDisc s ρ)) := kummerRegionMap s e hmap with hκ
  set f : C(↥(puncturedDisc (0 : ℂ) ρ'), ↥X) := (subsetIncl hsub).comp κ with hf
  have hfix : ∀ γ : FundamentalGroup ↥(puncturedDisc (0 : ℂ) ρ') b,
      cov.monodromyHom (f b) (FundamentalGroup.map f b γ) ⟨q₀, hq₀⟩ = ⟨q₀, hq₀⟩ := by
    intro γ
    obtain ⟨t, ht⟩ := exists_eq_pow_map_kummerRegionMap hρ s e hmap b γ
    have hcomp : FundamentalGroup.map f b γ
        = FundamentalGroup.map (subsetIncl hsub) (κ b) (FundamentalGroup.map κ b γ) :=
      fundamentalGroup_map_comp _ _ b γ
    rw [hcomp, ht, map_pow, map_pow]
    exact hexp t
  obtain ⟨F, hF0, hFlift⟩ := cov.exists_lift_of_monodromy_fixed f b q₀ hq₀ hfix
  exact ⟨F, hF0, fun u => congrArg Subtype.val (congrFun hFlift u)⟩

/-- **The Kummer coordinate lifts through a covering**, in the form that only tests a generator.
The fundamental group of a punctured disc is cyclic, so it is enough that the `e`-th power of the
monodromy of one generating loop fixes the chosen point of the fibre. -/
theorem exists_lift_kummerRegionMap_of_gen (cov : IsCoveringMap p) {s : ℂ} {ρ ρ' : ℝ} {e : ℕ}
    (hρ : 0 < ρ) (hρ' : 0 < ρ') (hsub : puncturedDisc s ρ ⊆ X)
    (hmap : ∀ u ∈ puncturedDisc (0 : ℂ) ρ', s + u ^ e ∈ puncturedDisc s ρ)
    (b : ↥(puncturedDisc (0 : ℂ) ρ')) {q₀ : E}
    (hq₀ : p q₀ = subsetIncl hsub (kummerRegionMap s e hmap b))
    {δ : FundamentalGroup ↥(puncturedDisc s ρ) (kummerRegionMap s e hmap b)}
    (hδ : Subgroup.zpowers δ = ⊤)
    (hfix : (cov.monodromyHom (subsetIncl hsub (kummerRegionMap s e hmap b))
            (FundamentalGroup.map (subsetIncl hsub) (kummerRegionMap s e hmap b) δ) ^ e)
          ⟨q₀, hq₀⟩ = ⟨q₀, hq₀⟩) :
    ∃ F : C(↥(puncturedDisc (0 : ℂ) ρ'), E), F b = q₀ ∧
      ∀ u : ↥(puncturedDisc (0 : ℂ) ρ'), ((p (F u) : ℂ)) = s + (u : ℂ) ^ e :=
  exists_lift_kummerRegionMap cov hρ hρ' hsub hmap b hq₀ fun τ =>
    pow_apply_eq_self_of_zpowers_eq_top hδ
      ((cov.monodromyHom (subsetIncl hsub (kummerRegionMap s e hmap b))).comp
        (FundamentalGroup.map (subsetIncl hsub) (kummerRegionMap s e hmap b))) hfix τ

end Rigidity.RET

end

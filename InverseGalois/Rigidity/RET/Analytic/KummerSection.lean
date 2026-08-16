/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.RootMonodromy
import InverseGalois.Rigidity.RET.Analytic.RootSection
import InverseGalois.Rigidity.RET.Pi1.Topological.Lifting
import InverseGalois.Rigidity.RET.Pi1.Topological.PowerDisc
import InverseGalois.Rigidity.RET.Pi1.Topological.KummerLift

/-!
# A single-valued root of a family in the Kummer coordinate

Around a parameter where a monic family of equations degenerates, the roots need not be
single-valued functions of the parameter: following a small loop around the bad parameter permutes
them.  Passing to the Kummer coordinate `u ↦ s + uᵉ` multiplies loops by `e`, so the ambiguity is
killed as soon as the `e`-th power of the local monodromy fixes the root one wants to follow.  This
is the analytic half of the Puiseux expansion: after an `e`-fold cover of the parameter disc the
chosen root becomes a genuine function.

The proof is the lifting criterion for covering spaces, in the monodromy form.  The root variety of
the family is a covering of the parameters away from the degeneracy set; the Kummer coordinate maps
a small punctured disc at the origin into a punctured disc around the bad parameter, and every loop
of the source has an image that is an `e`-th power.  Its monodromy is therefore an `e`-th power of a
permutation of the fibre, and by hypothesis fixes the chosen root, so the Kummer coordinate lifts to
the root variety.  The second coordinate of the lift is the root, as a function of `u`.

## Main definitions

* `Rigidity.RET.Analytic.fibrePoint` — a root of a specialized equation, as a point of the fibre of
  the punctured root cover.

## Main results

* `Rigidity.RET.Analytic.exists_root_on_puncturedDisc` — a continuous root of the family in the
  Kummer coordinate on a punctured disc.
* `Rigidity.RET.Analytic.exists_root_on_puncturedDisc_of_gen` — the same, checking only a generator
  of the fundamental group of the punctured disc.
-/

open Polynomial Rigidity.RET

noncomputable section

namespace Rigidity.RET.Analytic

variable {P : Polynomial (Polynomial ℂ)} {S : Finset ℂ}

/-! ### Points of the fibre -/

/-- A root of a specialized equation, as a **point of the fibre** of the punctured root cover. -/
def fibrePoint (x : ↥((S : Set ℂ)ᶜ)) {y : ℂ} (hy : (spec P (x : ℂ)).eval y = 0) :
    ↥(puncturedProj P S ⁻¹' {x}) :=
  ⟨⟨⟨((x : ℂ), y), hy⟩, x.2⟩, rfl⟩

@[simp] theorem fibrePoint_snd (x : ↥((S : Set ℂ)ᶜ)) {y : ℂ}
    (hy : (spec P (x : ℂ)).eval y = 0) :
    (((fibrePoint x hy).1.1 : ℂ × ℂ)).2 = y := rfl

/-! ### The lift of the Kummer coordinate -/

/-- **A root of the family becomes single-valued in the Kummer coordinate.**  If the `e`-th power of
the monodromy of every loop of the punctured disc around `s` fixes the chosen root, then the roots
of the family, read in the Kummer coordinate `u ↦ s + uᵉ`, contain a continuous branch through that
root on a punctured disc at the origin. -/
theorem exists_root_on_puncturedDisc (hP : P.Monic)
    (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {s : ℂ} {ρ ρ' : ℝ} {e : ℕ}
    (hρ : 0 < ρ) (hρ' : 0 < ρ') (hsub : puncturedDisc s ρ ⊆ ((S : Set ℂ))ᶜ)
    (hmap : ∀ u ∈ puncturedDisc (0 : ℂ) ρ', s + u ^ e ∈ puncturedDisc s ρ)
    (b : ↥(puncturedDisc (0 : ℂ) ρ')) {y₀ : ℂ}
    (hy₀ : (spec P (s + (b : ℂ) ^ e)).eval y₀ = 0)
    (hexp : ∀ τ : FundamentalGroup ↥(puncturedDisc s ρ) (kummerRegionMap s e hmap b),
      ((isCoveringMap_puncturedProj hP hS).monodromyHom
            (subsetIncl hsub (kummerRegionMap s e hmap b))
            (FundamentalGroup.map (subsetIncl hsub) (kummerRegionMap s e hmap b) τ) ^ e)
          (fibrePoint (subsetIncl hsub (kummerRegionMap s e hmap b)) hy₀)
        = fibrePoint (subsetIncl hsub (kummerRegionMap s e hmap b)) hy₀) :
    ∃ g : ℂ → ℂ, ContinuousOn g (puncturedDisc (0 : ℂ) ρ') ∧ g (b : ℂ) = y₀ ∧
      ∀ u ∈ puncturedDisc (0 : ℂ) ρ', (spec P (s + u ^ e)).eval (g u) = 0 := by
  classical
  set κ : C(↥(puncturedDisc (0 : ℂ) ρ'), ↥(puncturedDisc s ρ)) := kummerRegionMap s e hmap with hκ
  set q := fibrePoint (subsetIncl hsub (κ b)) hy₀ with hq
  obtain ⟨F, hF0, hfst⟩ := exists_lift_kummerRegionMap (isCoveringMap_puncturedProj hP hS)
    hρ hρ' hsub hmap b q.2 hexp
  have hroot : ∀ u : ↥(puncturedDisc (0 : ℂ) ρ'),
      (spec P (s + (u : ℂ) ^ e)).eval (((F u).1.1 : ℂ × ℂ)).2 = 0 := by
    intro u
    have hmem : biEval P ((F u).1.1 : ℂ × ℂ) = 0 := (F u).1.2
    rw [← hfst u]
    exact hmem
  refine ⟨fun u => if h : u ∈ puncturedDisc (0 : ℂ) ρ' then ((F ⟨u, h⟩).1.1 : ℂ × ℂ).2 else 0,
    ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_restrict]
    have hres : (Set.restrict (puncturedDisc (0 : ℂ) ρ')
        fun u => if h : u ∈ puncturedDisc (0 : ℂ) ρ' then ((F ⟨u, h⟩).1.1 : ℂ × ℂ).2 else 0)
        = fun u : ↥(puncturedDisc (0 : ℂ) ρ') => ((F u).1.1 : ℂ × ℂ).2 :=
      funext fun u => dif_pos u.2
    rw [hres]
    exact (continuous_subtype_val.comp (continuous_subtype_val.comp F.continuous)).snd
  · refine (dif_pos b.2).trans ?_
    show ((F b).1.1 : ℂ × ℂ).2 = y₀
    rw [hF0, hq]
    exact fibrePoint_snd _ hy₀
  · intro u hu
    show (spec P (s + u ^ e)).eval
      (if h : u ∈ puncturedDisc (0 : ℂ) ρ' then ((F ⟨u, h⟩).1.1 : ℂ × ℂ).2 else 0) = 0
    rw [dif_pos hu]
    exact hroot ⟨u, hu⟩

/-- **A root of the family becomes single-valued in the Kummer coordinate**, in the form that only
tests a generator.  The fundamental group of a punctured disc is cyclic, so it is enough that the
`e`-th power of the monodromy of one generating loop fixes the chosen root. -/
theorem exists_root_on_puncturedDisc_of_gen (hP : P.Monic)
    (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {s : ℂ} {ρ ρ' : ℝ} {e : ℕ}
    (hρ : 0 < ρ) (hρ' : 0 < ρ') (hsub : puncturedDisc s ρ ⊆ ((S : Set ℂ))ᶜ)
    (hmap : ∀ u ∈ puncturedDisc (0 : ℂ) ρ', s + u ^ e ∈ puncturedDisc s ρ)
    (b : ↥(puncturedDisc (0 : ℂ) ρ')) {y₀ : ℂ}
    (hy₀ : (spec P (s + (b : ℂ) ^ e)).eval y₀ = 0)
    {δ : FundamentalGroup ↥(puncturedDisc s ρ) (kummerRegionMap s e hmap b)}
    (hδ : Subgroup.zpowers δ = ⊤)
    (hfix : ((isCoveringMap_puncturedProj hP hS).monodromyHom
            (subsetIncl hsub (kummerRegionMap s e hmap b))
            (FundamentalGroup.map (subsetIncl hsub) (kummerRegionMap s e hmap b) δ) ^ e)
          (fibrePoint (subsetIncl hsub (kummerRegionMap s e hmap b)) hy₀)
        = fibrePoint (subsetIncl hsub (kummerRegionMap s e hmap b)) hy₀) :
    ∃ g : ℂ → ℂ, ContinuousOn g (puncturedDisc (0 : ℂ) ρ') ∧ g (b : ℂ) = y₀ ∧
      ∀ u ∈ puncturedDisc (0 : ℂ) ρ', (spec P (s + u ^ e)).eval (g u) = 0 :=
  exists_root_on_puncturedDisc hP hS hρ hρ' hsub hmap b hy₀ fun τ =>
    pow_apply_eq_self_of_zpowers_eq_top hδ
      (((isCoveringMap_puncturedProj hP hS).monodromyHom
          (subsetIncl hsub (kummerRegionMap s e hmap b))).comp
        (FundamentalGroup.map (subsetIncl hsub) (kummerRegionMap s e hmap b))) hfix τ

end Rigidity.RET.Analytic

end

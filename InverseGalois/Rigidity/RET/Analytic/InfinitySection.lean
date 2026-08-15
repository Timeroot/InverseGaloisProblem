/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.KummerSection
import InverseGalois.Rigidity.RET.Pi1.Topological.Exterior

/-!
# A single-valued root of a family in the parameter at infinity

Near the point at infinity the roots of a monic family need not be single-valued functions of the
parameter: following a large circle permutes them.  Passing to the parameter at infinity
`u ↦ (uᵈ)⁻¹` multiplies loops by `d`, so the ambiguity is killed as soon as the `d`-th power of the
monodromy of every exterior loop is trivial.  Taking for `d` a multiple of the order of the
symmetric group on a fibre makes that automatic, and no information about the monodromy is needed
at all.

The proof is the one used in the Kummer coordinate at a point of the line, with the Kummer
coordinate replaced by the parameter at infinity; the only new ingredient is that the image of a
loop under that parameter is again a `d`-th power.

## Main results

* `Rigidity.RET.Analytic.pow_factorial_card_eq_one` — a permutation of a finite set is killed by
  any multiple of the factorial of its cardinality.
* `Rigidity.RET.Analytic.exists_root_on_puncturedDisc_inv` — a continuous root of the family in the
  parameter at infinity on a punctured disc.
-/

open Polynomial Rigidity.RET

noncomputable section

namespace Rigidity.RET.Analytic

variable {P : Polynomial (Polynomial ℂ)} {S : Finset ℂ}

/-! ### Killing every permutation of a fibre -/

/-- **A permutation of a finite set is killed by any multiple of the factorial of its
cardinality.** -/
theorem pow_factorial_card_eq_one {α : Type*} [Finite α] {n d : ℕ} (hcard : Nat.card α = n)
    (hd : Nat.factorial n ∣ d) (σ : Equiv.Perm α) : σ ^ d = 1 := by
  refine orderOf_dvd_iff_pow_eq_one.1 (dvd_trans ?_ hd)
  rw [← hcard, ← Nat.card_perm]
  exact orderOf_dvd_natCard σ

/-! ### The lift of the parameter at infinity -/

/-- **A root of the family becomes single-valued in the parameter at infinity.**  Read in the
parameter `u ↦ (uᵈ)⁻¹` with `d` a multiple of the factorial of the degree, the roots of the family
contain a continuous branch through any chosen root, on a punctured disc at the origin.

No hypothesis on the monodromy is needed: the parameter at infinity multiplies loops by `d`, and
the `d`-th power of every permutation of a fibre is trivial for that choice of `d`. -/
theorem exists_root_on_puncturedDisc_inv (hP : P.Monic)
    (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {R ρ ρ' : ℝ} {d : ℕ}
    (hρ : 0 < ρ) (hρ' : 0 < ρ') (hd : Nat.factorial P.natDegree ∣ d)
    (hsub : extRegion R ⊆ ((S : Set ℂ))ᶜ)
    (hmap : ∀ u ∈ puncturedDisc (0 : ℂ) ρ', (0 : ℂ) + u ^ d ∈ puncturedDisc (0 : ℂ) ρ)
    (hinv : ∀ z ∈ puncturedDisc (0 : ℂ) ρ, z⁻¹ ∈ extRegion R)
    (b : ↥(puncturedDisc (0 : ℂ) ρ')) {y₀ : ℂ}
    (hy₀ : (spec P (((b : ℂ) ^ d)⁻¹)).eval y₀ = 0) :
    ∃ g : ℂ → ℂ, ContinuousOn g (puncturedDisc (0 : ℂ) ρ') ∧ g (b : ℂ) = y₀ ∧
      ∀ u ∈ puncturedDisc (0 : ℂ) ρ', (spec P ((u ^ d)⁻¹)).eval (g u) = 0 := by
  classical
  haveI : PathConnectedSpace ↥(puncturedDisc (0 : ℂ) ρ') :=
    pathConnectedSpace_puncturedDisc 0 hρ'
  haveI : LocPathConnectedSpace ↥(puncturedDisc (0 : ℂ) ρ') :=
    (isOpen_puncturedDisc (0 : ℂ) ρ').locPathConnectedSpace
  set cov := isCoveringMap_puncturedProj hP hS with hcov
  set κ : C(↥(puncturedDisc (0 : ℂ) ρ'), ↥(extRegion R)) := invPowRegionMap d hmap hinv with hκ
  set f : C(↥(puncturedDisc (0 : ℂ) ρ'), ↥((S : Set ℂ)ᶜ)) := (subsetIncl hsub).comp κ with hf
  have hcoe : ∀ u : ↥(puncturedDisc (0 : ℂ) ρ'),
      ((f u : ↥((S : Set ℂ)ᶜ)) : ℂ) = ((u : ℂ) ^ d)⁻¹ :=
    fun u => coe_invPowRegionMap d hmap hinv u
  have hy₀' : (spec P ((f b : ↥((S : Set ℂ)ᶜ)) : ℂ)).eval y₀ = 0 := by
    rw [hcoe b]; exact hy₀
  set q := fibrePoint (f b) hy₀' with hq
  haveI : Finite ↥(puncturedProj P S ⁻¹' {f b}) := (finite_puncturedFiber hP (f b).2).to_subtype
  have hfix : ∀ γ : FundamentalGroup ↥(puncturedDisc (0 : ℂ) ρ') b,
      cov.monodromyHom (f b) (FundamentalGroup.map f b γ) ⟨q.1, q.2⟩ = ⟨q.1, q.2⟩ := by
    intro γ
    obtain ⟨t, ht⟩ := exists_eq_pow_map_invPowRegionMap hρ d hmap hinv b γ
    have hcomp : FundamentalGroup.map f b γ
        = FundamentalGroup.map (subsetIncl hsub) (κ b) (FundamentalGroup.map κ b γ) :=
      fundamentalGroup_map_comp _ _ b γ
    have h1 : (cov.monodromyHom (f b)) (FundamentalGroup.map (subsetIncl hsub) (κ b) t) ^ d = 1 :=
      pow_factorial_card_eq_one (card_puncturedFiber hP hS (f b).2) hd _
    rw [hcomp, ht, map_pow, map_pow, h1]
    rfl
  obtain ⟨F, hF0, hFlift⟩ := cov.exists_lift_of_monodromy_fixed f b q.1 q.2 hfix
  have hfst : ∀ u : ↥(puncturedDisc (0 : ℂ) ρ'),
      ((F u).1.1 : ℂ × ℂ).1 = ((u : ℂ) ^ d)⁻¹ := fun u => by
    rw [← hcoe u]
    exact congrArg Subtype.val (congrFun hFlift u)
  have hroot : ∀ u : ↥(puncturedDisc (0 : ℂ) ρ'),
      (spec P (((u : ℂ) ^ d)⁻¹)).eval (((F u).1.1 : ℂ × ℂ)).2 = 0 := by
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
    exact fibrePoint_snd _ hy₀'
  · intro u hu
    show (spec P ((u ^ d)⁻¹)).eval
      (if h : u ∈ puncturedDisc (0 : ℂ) ρ' then ((F ⟨u, h⟩).1.1 : ℂ × ℂ).2 else 0) = 0
    rw [dif_pos hu]
    exact hroot ⟨u, hu⟩

end Rigidity.RET.Analytic

end

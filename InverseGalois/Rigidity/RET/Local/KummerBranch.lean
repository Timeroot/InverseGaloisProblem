/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.KummerSection
import InverseGalois.Rigidity.RET.Local.PuiseuxAssembly

/-!
# A Puiseux parametrisation from the local monodromy

The local monodromy of the equation of a cover around a point is a permutation of the roots, and
the exponent of the group it generates is the only obstruction to following a root single-valuedly
around the point.  Passing to the Kummer coordinate `u ↦ s + uᵉ` multiplies loops by `e`, so as soon
as `e` annihilates the local monodromy the chosen root becomes a genuine function of `u`; it is then
bounded and holomorphic on a punctured disc, extends across the puncture, and its Taylor series is a
Puiseux parametrisation of the cover of index `e`.

Nothing has to be checked at the puncture itself, and no generator of the local monodromy has to be
named: the hypothesis is only that the `e`-th power of the monodromy of every loop of the punctured
disc is trivial.  Since the punctured disc has cyclic fundamental group, that is one condition on
one permutation, and it is automatic when `e` is the order of the local monodromy.

## Main results

* `Rigidity.RET.exists_puiseuxEmbedding_of_monodromy_pow` — an exponent for the local monodromy
  gives a Puiseux parametrisation of that index.
* `Rigidity.RET.exists_puiseuxEmbedding_of_orderOf_monodromy` — the order of the monodromy of a
  generating loop is such an exponent.
-/

open Polynomial Filter Topology GeomAKLB Rigidity.RET.Analytic

noncomputable section

namespace Rigidity.RET

/-! ### Exponents of a cyclic group -/

/-- **In a cyclic group an exponent of the generator is an exponent of every element.** -/
theorem pow_eq_one_of_zpowers_eq_top {H : Type*} [Group H] {g : H}
    (hgen : Subgroup.zpowers g = ⊤) {H' : Type*} [Group H'] (ψ : H →* H') {n : ℕ}
    (hn : ψ g ^ n = 1) (t : H) : ψ t ^ n = 1 := by
  obtain ⟨m, rfl⟩ : t ∈ Subgroup.zpowers g := hgen ▸ Subgroup.mem_top t
  rw [map_zpow, ← zpow_natCast (ψ g ^ m) n, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hn,
    one_zpow]

variable {Ω : Type} [Field Ω] [Algebra (RatFunc k) Ω] [Algebra (Polynomial k) Ω]
  [IsScalarTower (Polynomial k) (RatFunc k) Ω] [Algebra k ℂ]

/-! ### A root of the fibre equation -/

omit [Algebra (RatFunc k) Ω] [IsScalarTower (Polynomial k) (RatFunc k) Ω] in
/-- **The equation of the cover has a root over every point of the complex line.** -/
theorem exists_root_complexEquation {α : Ω} (hα : IsIntegral (Polynomial k) α) (z : ℂ) :
    ∃ y : ℂ, (Analytic.spec (complexEquation α) z).eval y = 0 := by
  have hmon : (Analytic.spec (complexEquation α) z).Monic :=
    Analytic.spec_monic (monic_complexEquation hα) z
  have hdeg : 0 < (Analytic.spec (complexEquation α) z).degree := by
    rw [Polynomial.degree_eq_natDegree hmon.ne_zero, Analytic.natDegree_spec
      (monic_complexEquation hα) z]
    exact_mod_cast natDegree_complexEquation_pos hα
  obtain ⟨y, hy⟩ := Complex.exists_root hdeg
  exact ⟨y, hy⟩

/-! ### From an exponent of the local monodromy to a Puiseux parametrisation -/

/-- **An exponent for the local monodromy gives a Puiseux parametrisation of that index.**  If the
`e`-th power of the monodromy of every loop of a punctured disc around the point is trivial, then a
root of the equation of the cover can be followed single-valuedly in the Kummer coordinate of index
`e`, and the resulting branch is a Puiseux parametrisation. -/
theorem exists_puiseuxEmbedding_of_monodromy_pow (s : k) {α : Ω}
    (hα : IsIntegral (Polynomial k) α) (hgen : IntermediateField.adjoin (RatFunc k) {α} = ⊤)
    {S : Finset ℂ} (hS : ∀ z ∉ (S : Set ℂ), (Analytic.spec (complexEquation α) z).Separable)
    {ρ ρ' : ℝ} (hρ : 0 < ρ) (hρ' : 0 < ρ')
    (hsub : puncturedDisc (algebraMap k ℂ s) ρ ⊆ ((S : Set ℂ))ᶜ) {e : ℕ} (he : 0 < e)
    (hmap : ∀ u ∈ puncturedDisc (0 : ℂ) ρ',
      algebraMap k ℂ s + u ^ e ∈ puncturedDisc (algebraMap k ℂ s) ρ)
    (b : ↥(puncturedDisc (0 : ℂ) ρ'))
    (hpow : ∀ τ : FundamentalGroup ↥(puncturedDisc (algebraMap k ℂ s) ρ)
        (kummerRegionMap (algebraMap k ℂ s) e hmap b),
      ((isCoveringMap_puncturedProj (monic_complexEquation hα) hS).monodromyHom
          (subsetIncl hsub (kummerRegionMap (algebraMap k ℂ s) e hmap b))
          (FundamentalGroup.map (subsetIncl hsub)
            (kummerRegionMap (algebraMap k ℂ s) e hmap b) τ)) ^ e = 1) :
    Nonempty (PuiseuxEmbedding Ω ℂ s e) := by
  obtain ⟨y₀, hy₀⟩ :=
    exists_root_complexEquation hα (algebraMap k ℂ s + (b : ℂ) ^ e)
  obtain ⟨g, hcont, -, hroot⟩ := Analytic.exists_root_on_puncturedDisc
    (monic_complexEquation hα) hS hρ hρ' hsub hmap b hy₀ fun τ => by
      rw [hpow τ]; rfl
  exact exists_puiseuxEmbedding_of_branch s he α hα hgen hρ'
    (fun u hu => hS _ (hsub (hmap u hu))) hcont hroot

/-- **The order of the monodromy of a generating loop is an exponent for the local monodromy.**
The fundamental group of a punctured disc is cyclic, so the order of the monodromy of one
generating loop bounds the index of a Puiseux parametrisation at the point. -/
theorem exists_puiseuxEmbedding_of_orderOf_monodromy (s : k) {α : Ω}
    (hα : IsIntegral (Polynomial k) α) (hgen : IntermediateField.adjoin (RatFunc k) {α} = ⊤)
    {S : Finset ℂ} (hS : ∀ z ∉ (S : Set ℂ), (Analytic.spec (complexEquation α) z).Separable)
    {ρ ρ' : ℝ} (hρ : 0 < ρ) (hρ' : 0 < ρ')
    (hsub : puncturedDisc (algebraMap k ℂ s) ρ ⊆ ((S : Set ℂ))ᶜ) {e : ℕ} (he : 0 < e)
    (hmap : ∀ u ∈ puncturedDisc (0 : ℂ) ρ',
      algebraMap k ℂ s + u ^ e ∈ puncturedDisc (algebraMap k ℂ s) ρ)
    (b : ↥(puncturedDisc (0 : ℂ) ρ'))
    {δ : FundamentalGroup ↥(puncturedDisc (algebraMap k ℂ s) ρ)
      (kummerRegionMap (algebraMap k ℂ s) e hmap b)} (hδ : Subgroup.zpowers δ = ⊤)
    (hord : ((isCoveringMap_puncturedProj (monic_complexEquation hα) hS).monodromyHom
          (subsetIncl hsub (kummerRegionMap (algebraMap k ℂ s) e hmap b))
          (FundamentalGroup.map (subsetIncl hsub)
            (kummerRegionMap (algebraMap k ℂ s) e hmap b) δ)) ^ e = 1) :
    Nonempty (PuiseuxEmbedding Ω ℂ s e) :=
  exists_puiseuxEmbedding_of_monodromy_pow s hα hgen hS hρ hρ' hsub he hmap b
    (pow_eq_one_of_zpowers_eq_top hδ
      (((isCoveringMap_puncturedProj (monic_complexEquation hα) hS).monodromyHom
          (subsetIncl hsub (kummerRegionMap (algebraMap k ℂ s) e hmap b))).comp
        (FundamentalGroup.map (subsetIncl hsub)
          (kummerRegionMap (algebraMap k ℂ s) e hmap b))) hord)

end Rigidity.RET

end

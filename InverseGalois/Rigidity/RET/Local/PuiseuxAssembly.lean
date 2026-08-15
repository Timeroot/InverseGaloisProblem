/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Local.KummerGerm
import InverseGalois.Rigidity.RET.Local.PuiseuxRoot

/-!
# From a holomorphic branch of the roots to a Puiseux parametrisation

The local analysis of a cover of the line at a point produces a holomorphic branch of the roots of
the equation of the cover, read in the Kummer coordinate on a punctured disc.  This file turns that
analytic object into the algebraic one it is meant to feed: a Puiseux embedding of the function
field of the cover into formal Laurent series.

Two steps separate them.  First the branch extends across the puncture and its Taylor series is a
formal power series solving the equation; that is the content of the removable singularity.  Second
the equation itself has to be recognised: the minimal polynomial of a primitive element over the
coordinate ring is monic with polynomial coefficients, its image over the rational function field
is the minimal polynomial there, and substituting the Kummer coordinate into it is the same as
extending the coefficients to the complex numbers and substituting the complex Kummer coordinate.
A formal root of the complexified equation is therefore a Laurent series root of the minimal
polynomial over the rational function field, which is exactly a Puiseux embedding.

## Main results

* `Rigidity.RET.exists_puiseuxEmbedding_of_powerSeries_root` — a formal power series root of the
  complexified equation of the cover is a Puiseux parametrisation.
* `Rigidity.RET.exists_germ_puiseuxEmbedding_of_branch` — a holomorphic branch of the roots on a
  punctured disc in the Kummer coordinate extends to a germ, and the Taylor series of that germ is
  the image of the primitive element under a Puiseux parametrisation.
* `Rigidity.RET.exists_puiseuxEmbedding_of_branch` — a holomorphic branch of the roots on a
  punctured disc in the Kummer coordinate is a Puiseux parametrisation.
-/

open Polynomial Filter Topology GeomAKLB

noncomputable section

namespace Rigidity.RET

variable {Ω : Type} [Field Ω] [Algebra (RatFunc k) Ω] [Algebra (Polynomial k) Ω]
  [IsScalarTower (Polynomial k) (RatFunc k) Ω] [Algebra k ℂ]

/-- The **equation of the cover with complex coefficients**: the minimal polynomial of a primitive
element over the coordinate ring of the line, with its coefficients extended to the complex
numbers. -/
def complexEquation (α : Ω) : Polynomial (Polynomial ℂ) :=
  (minpoly (Polynomial k) α).map (Polynomial.mapRingHom (algebraMap k ℂ))

omit [Algebra (RatFunc k) Ω] [IsScalarTower (Polynomial k) (RatFunc k) Ω] in
theorem monic_complexEquation {α : Ω} (hα : IsIntegral (Polynomial k) α) :
    (complexEquation α).Monic :=
  (minpoly.monic hα).map _

omit [Algebra (RatFunc k) Ω] [IsScalarTower (Polynomial k) (RatFunc k) Ω] in
theorem natDegree_complexEquation_pos {α : Ω} (hα : IsIntegral (Polynomial k) α) :
    0 < (complexEquation α).natDegree := by
  have hdeg : (complexEquation α).natDegree = (minpoly (Polynomial k) α).natDegree :=
    (minpoly.monic hα).natDegree_map _
  rw [hdeg]
  exact minpoly.natDegree_pos hα

/-! ### The formal bridge -/

/-- **A formal power series root of the complexified equation is a Puiseux parametrisation sending
the primitive element to that root.** -/
theorem exists_puiseuxEmbedding_hom_eq_of_powerSeries_root (s : k) {e : ℕ} (he : 0 < e) (α : Ω)
    (hα : IsIntegral (Polynomial k) α) (hgen : IntermediateField.adjoin (RatFunc k) {α} = ⊤)
    (Y : PowerSeries ℂ)
    (hY : Polynomial.eval₂ (kummerSubstC (algebraMap k ℂ s) e) Y (complexEquation α) = 0) :
    ∃ ψ : PuiseuxEmbedding Ω ℂ s e,
      ψ.hom α = algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) Y := by
  refine exists_puiseuxEmbedding_hom_eq_of_eval₂_eq_zero ℂ s he α hα.tower_top hgen
    (algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) Y) ?_
  have hcomp : (kummerLift ℂ s he).comp (algebraMap (Polynomial k) (RatFunc k))
      = (algebraMap (PowerSeries ℂ) (LaurentSeries ℂ)).comp (kummerSubst ℂ s e) :=
    RingHom.ext fun p => kummerLift_algebraMap ℂ s he p
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' (RatFunc k) hα, Polynomial.eval₂_map, hcomp,
    ← Polynomial.hom_eval₂, kummerSubst_eq_kummerSubstC, ← Polynomial.eval₂_map]
  rw [show (minpoly (Polynomial k) α).map (Polynomial.mapRingHom (algebraMap k ℂ))
      = complexEquation α from rfl, hY, map_zero]

/-- **A formal power series root of the complexified equation is a Puiseux parametrisation.** -/
theorem exists_puiseuxEmbedding_of_powerSeries_root (s : k) {e : ℕ} (he : 0 < e) (α : Ω)
    (hα : IsIntegral (Polynomial k) α) (hgen : IntermediateField.adjoin (RatFunc k) {α} = ⊤)
    (Y : PowerSeries ℂ)
    (hY : Polynomial.eval₂ (kummerSubstC (algebraMap k ℂ s) e) Y (complexEquation α) = 0) :
    Nonempty (PuiseuxEmbedding Ω ℂ s e) :=
  let ⟨ψ, _⟩ := exists_puiseuxEmbedding_hom_eq_of_powerSeries_root s he α hα hgen Y hY
  ⟨ψ⟩

/-! ### The analytic bridge -/

/-- **A holomorphic branch of the roots in the Kummer coordinate extends to a germ whose Taylor
series is the image of a primitive element under a Puiseux parametrisation.**  The branch extends
across the puncture because it is bounded, its Taylor series solves the complexified equation of
the cover formally, and a formal solution is a Puiseux embedding. -/
theorem exists_germ_puiseuxEmbedding_of_branch (s : k) {e : ℕ} (he : 0 < e) (α : Ω)
    (hα : IsIntegral (Polynomial k) α) (hgen : IntermediateField.adjoin (RatFunc k) {α} = ⊤)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hsep : ∀ u ∈ puncturedDisc (0 : ℂ) ρ,
      (Analytic.spec (complexEquation α) (algebraMap k ℂ s + u ^ e)).Separable)
    {g : ℂ → ℂ} (hcont : ContinuousOn g (puncturedDisc (0 : ℂ) ρ))
    (hroot : ∀ u ∈ puncturedDisc (0 : ℂ) ρ,
      (Analytic.spec (complexEquation α) (algebraMap k ℂ s + u ^ e)).eval (g u) = 0) :
    ∃ (G : smoothAt (0 : ℂ)) (ψ : PuiseuxEmbedding Ω ℂ s e),
      (∀ u ∈ puncturedDisc (0 : ℂ) ρ, (G : ℂ → ℂ) u = g u) ∧
        ψ.hom α = algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) (taylorHom 0 G) := by
  obtain ⟨G, hGeq, hGroot⟩ := exists_smoothAt_root (monic_complexEquation hα)
    (natDegree_complexEquation_pos hα) hρ hsep hcont hroot
  obtain ⟨ψ, hψ⟩ := exists_puiseuxEmbedding_hom_eq_of_powerSeries_root s he α hα hgen (taylorHom 0 G)
    (eval₂_kummerSubstC_eq_zero _ _ e G hGroot)
  exact ⟨G, ψ, hGeq, hψ⟩

/-- **A holomorphic branch of the roots in the Kummer coordinate is a Puiseux parametrisation.**
The branch extends across the puncture because it is bounded, its Taylor series solves the
complexified equation of the cover formally, and a formal solution is a Puiseux embedding. -/
theorem exists_puiseuxEmbedding_of_branch (s : k) {e : ℕ} (he : 0 < e) (α : Ω)
    (hα : IsIntegral (Polynomial k) α) (hgen : IntermediateField.adjoin (RatFunc k) {α} = ⊤)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hsep : ∀ u ∈ puncturedDisc (0 : ℂ) ρ,
      (Analytic.spec (complexEquation α) (algebraMap k ℂ s + u ^ e)).Separable)
    {g : ℂ → ℂ} (hcont : ContinuousOn g (puncturedDisc (0 : ℂ) ρ))
    (hroot : ∀ u ∈ puncturedDisc (0 : ℂ) ρ,
      (Analytic.spec (complexEquation α) (algebraMap k ℂ s + u ^ e)).eval (g u) = 0) :
    Nonempty (PuiseuxEmbedding Ω ℂ s e) :=
  let ⟨_, ψ, _, _⟩ := exists_germ_puiseuxEmbedding_of_branch s he α hα hgen hρ hsep hcont hroot
  ⟨ψ⟩

end Rigidity.RET

end

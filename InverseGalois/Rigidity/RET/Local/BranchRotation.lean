/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.DeckData
import InverseGalois.Rigidity.RET.Local.Rescale
import InverseGalois.Rigidity.RET.Local.TaylorRescale

/-!
# A branch of the roots that rotates is an inertia element

An automorphism of a cover of the line is a formula `w ↦ N(z, w) / d(z)` in the coordinate `z` of
the line and a primitive element `w`.  Reading that formula along a holomorphic branch of the roots
in the Kummer coordinate `z = s + uᵉ` turns it into a germ at the origin, and the Taylor series of
that germ is exactly what the Puiseux embedding of the cover computes: the numerator formula
evaluated at the Puiseux expansion of the primitive element, divided by the denominator.

That is the whole content of this file.  On the one side sits an algebraic identity — the formula
of an automorphism computes that automorphism on a primitive element — and on the other an analytic
one: the branch, followed once around the point, comes back rotated.  Taylor expansion identifies
the two, because it is a ring homomorphism, only sees the germ, and turns a rotation of the
variable into a rescaling of the series.  So an automorphism whose formula rotates the branch is an
automorphism whose Puiseux expansion rescales, and such an automorphism lies in the inertia group
at the point.

## Main definitions

* `Rigidity.RET.DeckData.numGerm` — the numerator formula, read along a branch in the Kummer
  coordinate.
* `Rigidity.RET.DeckData.denGerm` — the denominator, read in the Kummer coordinate.

## Main results

* `Rigidity.RET.DeckData.hom_inv_apply_mul_den` — the Puiseux expansion of the image of a primitive
  element, cleared of the denominator, is the numerator formula evaluated at its expansion.
* `Rigidity.RET.DeckData.hom_inv_apply_eq_rescale` — an automorphism whose formula rotates the
  branch rescales the Puiseux expansion.
* `Rigidity.RET.LineCover.isInertiaAt_of_act_rotate` — an automorphism whose formula rotates the
  branch is an inertia element at the point.
-/

open Polynomial Filter Topology GeomAKLB

noncomputable section

namespace Rigidity.RET

/-! ### Two small computations -/

/-- **Evaluating the Kummer coordinate of a polynomial at a point** is evaluating the polynomial at
the Kummer image of that point. -/
theorem coe_kummerGerm (s : ℂ) (e : ℕ) (p : Polynomial ℂ) (u : ℂ) :
    ((kummerGerm s e p : smoothAt (0 : ℂ)) : ℂ → ℂ) u = p.eval (s + u ^ e) :=
  congrArg (fun f : Polynomial ℂ →+* ℂ => f p) (evalGermHom_comp_kummerGerm s e u)

/-- A punctured disc is a neighbourhood of the centre away from the centre. -/
theorem puncturedDisc_mem_nhdsNE {ρ : ℝ} (hρ : 0 < ρ) :
    puncturedDisc (0 : ℂ) ρ ∈ 𝓝[≠] (0 : ℂ) := by
  have h := inter_mem_nhdsWithin ({(0 : ℂ)}ᶜ) (Metric.ball_mem_nhds (0 : ℂ) hρ)
  rw [Set.inter_comm, ← Set.diff_eq] at h
  exact h

variable {Ω : Type} [Field Ω] [Algebra (RatFunc k) Ω] [Algebra (Polynomial k) Ω]
  [IsScalarTower (Polynomial k) (RatFunc k) Ω] [Algebra k ℂ]

namespace DeckData

variable {α : Ω} (D : DeckData α) (s : k) (e : ℕ)

/-! ### The formulas as germs in the Kummer coordinate -/

/-- The **numerator formula of an automorphism, read along a branch of the roots** in the Kummer
coordinate. -/
def numGerm (G : smoothAt (0 : ℂ)) (g : Ω ≃ₐ[RatFunc k] Ω) : smoothAt (0 : ℂ) :=
  Polynomial.eval₂ (kummerGerm (algebraMap k ℂ s) e) G (D.toIntegralDeck.num g)

/-- The **common denominator of the formulas, read in the Kummer coordinate.** -/
def denGerm : smoothAt (0 : ℂ) := kummerGerm (algebraMap k ℂ s) e D.toIntegralDeck.den

variable {D s e}

omit [IsScalarTower (Polynomial k) (RatFunc k) Ω] in
theorem coe_numGerm (G : smoothAt (0 : ℂ)) (g : Ω ≃ₐ[RatFunc k] Ω) (u : ℂ) :
    ((D.numGerm s e G g : smoothAt (0 : ℂ)) : ℂ → ℂ) u
      = (Analytic.spec (D.toIntegralDeck.num g) (algebraMap k ℂ s + u ^ e)).eval
          ((G : ℂ → ℂ) u) :=
  coe_eval₂_kummerGerm _ _ _ _ _

omit [IsScalarTower (Polynomial k) (RatFunc k) Ω] in
theorem coe_denGerm (u : ℂ) :
    ((D.denGerm s e : smoothAt (0 : ℂ)) : ℂ → ℂ) u
      = D.toIntegralDeck.den.eval (algebraMap k ℂ s + u ^ e) :=
  coe_kummerGerm _ _ _ _

omit [IsScalarTower (Polynomial k) (RatFunc k) Ω] in
theorem taylorHom_numGerm (G : smoothAt (0 : ℂ)) (g : Ω ≃ₐ[RatFunc k] Ω) :
    taylorHom 0 (D.numGerm s e G g)
      = Polynomial.eval₂ (kummerSubstC (algebraMap k ℂ s) e) (taylorHom 0 G)
          (D.toIntegralDeck.num g) := by
  rw [numGerm, Polynomial.hom_eval₂, taylorHom_comp_kummerGerm]

omit [IsScalarTower (Polynomial k) (RatFunc k) Ω] in
theorem taylorHom_denGerm :
    taylorHom 0 (D.denGerm s e) = kummerSubstC (algebraMap k ℂ s) e D.toIntegralDeck.den := by
  rw [denGerm, ← taylorHom_comp_kummerGerm (algebraMap k ℂ s) e, RingHom.comp_apply]

omit [IsScalarTower (Polynomial k) (RatFunc k) Ω] in
/-- **The numerator germ is the formula times the denominator germ**, wherever the denominator does
not vanish. -/
theorem coe_numGerm_eq_act_mul (G : smoothAt (0 : ℂ)) (g : Ω ≃ₐ[RatFunc k] Ω) {u : ℂ}
    (hu : D.toIntegralDeck.den.eval (algebraMap k ℂ s + u ^ e) ≠ 0) :
    ((D.numGerm s e G g : smoothAt (0 : ℂ)) : ℂ → ℂ) u
      = D.toIntegralDeck.act g (algebraMap k ℂ s + u ^ e) ((G : ℂ → ℂ) u)
          * ((D.denGerm s e : smoothAt (0 : ℂ)) : ℂ → ℂ) u := by
  rw [coe_numGerm, coe_denGerm, Analytic.IntegralDeck.act, div_mul_cancel₀ _ hu]

/-! ### The denominator is not a zero divisor -/

omit [IsScalarTower (Polynomial k) (RatFunc k) Ω] [Algebra k ℂ] in
theorem den_ne_zero : D.den ≠ 0 := fun h => D.bad_ne (zero_dvd_iff.mp (h ▸ D.den_dvd))

omit [IsScalarTower (Polynomial k) (RatFunc k) Ω] in
theorem kummerSubstC_den_eq :
    kummerSubstC (algebraMap k ℂ s) e D.toIntegralDeck.den = kummerSubst ℂ s e D.den :=
  (congrArg (fun f : Polynomial k →+* PowerSeries ℂ => f D.den)
    (kummerSubst_eq_kummerSubstC s e)).symm

omit [IsScalarTower (Polynomial k) (RatFunc k) Ω] in
theorem kummerSubstC_den_ne_zero (he : 0 < e) :
    kummerSubstC (algebraMap k ℂ s) e D.toIntegralDeck.den ≠ 0 := by
  rw [kummerSubstC_den_eq (D := D) (s := s)]
  intro h
  exact D.den_ne_zero (kummerSubst_injective ℂ s he (by rw [h, map_zero]))

/-! ### The algebraic half: clearing the denominator -/

/-- **The Puiseux expansion of the image of a primitive element, cleared of the denominator, is the
numerator formula evaluated at its expansion.**  This is the algebraic identity defining the
formulas, read through the Puiseux embedding. -/
theorem hom_inv_apply_mul_den (ψ : PuiseuxEmbedding Ω ℂ s e) {G : smoothAt (0 : ℂ)}
    (hψ : ψ.hom α = algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) (taylorHom 0 G))
    (g : Ω ≃ₐ[RatFunc k] Ω) :
    ψ.hom (g⁻¹ α) * algebraMap (PowerSeries ℂ) (LaurentSeries ℂ)
          (kummerSubstC (algebraMap k ℂ s) e D.toIntegralDeck.den)
      = algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) (taylorHom 0 (D.numGerm s e G g)) := by
  have hcomp : (kummerLift ℂ s ψ.index_pos).comp (algebraMap (Polynomial k) (RatFunc k))
      = (algebraMap (PowerSeries ℂ) (LaurentSeries ℂ)).comp
          ((kummerSubstC (algebraMap k ℂ s) e).comp
            (Polynomial.mapRingHom (algebraMap k ℂ))) := by
    refine RingHom.ext fun p => ?_
    rw [RingHom.comp_apply, kummerLift_algebraMap, RingHom.comp_apply, RingHom.comp_apply,
      kummerSubst_eq_kummerSubstC s e, RingHom.comp_apply]
  have hkey := congrArg ψ.hom (D.aeval_num g)
  rw [ψ.hom_aeval, Polynomial.eval₂_map, hcomp, hψ, ← Polynomial.hom_eval₂,
    ← Polynomial.eval₂_map, map_mul, ψ.hom_algebraMap_ratFunc, kummerLift_algebraMap,
    kummerSubst_eq_kummerSubstC s e, RingHom.comp_apply] at hkey
  rw [taylorHom_numGerm, num_toIntegralDeck, mul_comm]
  exact hkey.symm

/-! ### The analytic half: a rotating branch -/

/-- **An automorphism whose formula rotates the branch rescales the Puiseux expansion of a
primitive element.** -/
theorem hom_inv_apply_eq_rescale (ψ : PuiseuxEmbedding Ω ℂ s e) {G : smoothAt (0 : ℂ)}
    (hψ : ψ.hom α = algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) (taylorHom 0 G))
    {ζ : ℂ} (hζ0 : ζ ≠ 0) (hζ : ‖ζ‖ ≤ 1) (g : Ω ≃ₐ[RatFunc k] Ω)
    (hden : ∀ᶠ u in 𝓝[≠] (0 : ℂ),
      D.toIntegralDeck.den.eval (algebraMap k ℂ s + u ^ e) ≠ 0)
    (hact : ∀ᶠ u in 𝓝[≠] (0 : ℂ),
      D.toIntegralDeck.act g (algebraMap k ℂ s + u ^ e) ((G : ℂ → ℂ) u) = (G : ℂ → ℂ) (ζ * u)) :
    ψ.hom (g⁻¹ α) = laurentRescale hζ0 (ψ.hom α) := by
  -- the numerator germ is the rotated branch times the denominator germ
  have hgerm : taylorHom 0 (D.numGerm s e G g)
      = taylorHom 0 (scaleGerm ζ G * D.denGerm s e) := by
    refine taylorHom_congr_of_punctured _ _ ?_
    filter_upwards [hden, hact] with u hu hu'
    show ((D.numGerm s e G g : smoothAt (0 : ℂ)) : ℂ → ℂ) u
      = ((scaleGerm ζ G * D.denGerm s e : smoothAt (0 : ℂ)) : ℂ → ℂ) u
    rw [coe_numGerm_eq_act_mul G g hu, hu']
    rfl
  rw [map_mul, taylorHom_scaleGerm hζ, taylorHom_denGerm] at hgerm
  -- cancel the denominator
  have hmain := hom_inv_apply_mul_den (D := D) ψ hψ g
  rw [hgerm, map_mul] at hmain
  have hne : algebraMap (PowerSeries ℂ) (LaurentSeries ℂ)
      (kummerSubstC (algebraMap k ℂ s) e D.toIntegralDeck.den) ≠ 0 := fun h =>
    kummerSubstC_den_ne_zero (D := D) (s := s) ψ.index_pos
      (IsFractionRing.injective (PowerSeries ℂ) (LaurentSeries ℂ) (by rw [h, map_zero]))
  rw [hψ, laurentRescale_algebraMap]
  exact mul_right_cancel₀ hne hmain

end DeckData

/-! ### The inertia element -/

namespace LineCover

variable (L : LineCover) {s : k} {e : ℕ} {α : L.M} (D : DeckData α)

/-- **An automorphism whose formula rotates a branch of the roots is an inertia element at the
point.**  Rotating the branch rescales the Puiseux expansion of a primitive element, and a deck
transformation the Puiseux embedding turns into a rescaling stabilizes the place it cuts out. -/
theorem isInertiaAt_of_act_rotate (ψ : PuiseuxEmbedding L.M ℂ s e) {G : smoothAt (0 : ℂ)}
    (hψ : ψ.hom α = algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) (taylorHom 0 G))
    (hα : IsIntegral (RatFunc k) α) (hgen : IntermediateField.adjoin (RatFunc k) {α} = ⊤)
    {ζ : ℂ} (hζ0 : ζ ≠ 0) (hζ1 : ‖ζ‖ ≤ 1) (hζe : ζ ^ e = 1) (g : L.deck)
    (hden : ∀ᶠ u in 𝓝[≠] (0 : ℂ),
      D.toIntegralDeck.den.eval (algebraMap k ℂ s + u ^ e) ≠ 0)
    (hact : ∀ᶠ u in 𝓝[≠] (0 : ℂ),
      D.toIntegralDeck.act g (algebraMap k ℂ s + u ^ e) ((G : ℂ → ℂ) u) = (G : ℂ → ℂ) (ζ * u)) :
    L.IsInertiaAt s g := by
  have hinv : L.IsInertiaAt s g⁻¹ :=
    L.isInertiaAt_of_rescale ψ hζ0
      (ψ.intertwine_of_apply_eq hζ0 hζe hα hgen
        (D.hom_inv_apply_eq_rescale ψ hψ hζ0 hζ1 g hden hact))
  obtain ⟨Q, hmax, hover, hmem⟩ := hinv
  exact ⟨Q, hmax, hover, by simpa using inv_mem hmem⟩

end LineCover

end Rigidity.RET

end

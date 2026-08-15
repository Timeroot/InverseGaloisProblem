/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Local.PowerSeriesPlace

/-!
# Puiseux parametrisations from a Laurent series root

A Puiseux embedding of a cover at a point is an abstract piece of data — a ring homomorphism of the
function field into formal Laurent series — but it is produced from something entirely concrete: a
single Laurent series `y` satisfying the equation of the cover in the local coordinate.  This file
builds the bridge.

The Kummer substitution `X ↦ s + u ^ e` of the coordinate ring into formal power series is
injective, because it factors as a coefficient extension, a translation, an `e`-fold expansion and
the inclusion of polynomials into power series, all of which are injective.  Injectivity lets it be
extended to the rational function field, and once the constants are embedded, a homomorphism of the
function field of the cover into Laurent series is exactly a root, in Laurent series, of the minimal
polynomial of a primitive element.

## Main definitions

* `Rigidity.RET.kummerLift` — the Kummer substitution extended to the rational function field.

## Main results

* `Rigidity.RET.kummerSubst_injective` — the Kummer substitution is injective.
* `Rigidity.RET.PuiseuxEmbedding.ofRingHom` — a homomorphism into Laurent series lying over the
  Kummer substitution is a Puiseux embedding.
* `Rigidity.RET.exists_puiseuxEmbedding_of_eval₂_eq_zero` — a Laurent series root of the minimal
  polynomial of a primitive element is a Puiseux parametrisation of the cover.
-/

open Polynomial GeomAKLB

noncomputable section

namespace Rigidity.RET

variable (K : Type) [Field K] [Algebra k K]

/-! ### Injectivity of the Kummer substitution -/

/-- The Kummer substitution factors as coefficient extension, translation, `e`-fold expansion and
the inclusion of polynomials into power series. -/
theorem kummerSubst_eq_comp (s : k) (e : ℕ) (p : Polynomial k) :
    kummerSubst K s e p
      = ((expand K e) (taylor (algebraMap k K s) (p.map (algebraMap k K))) :
          Polynomial K) := by
  have h : ((Polynomial.coeToPowerSeries.ringHom (R := K)).comp
        ((expand K e).toRingHom.comp
          (((taylorAlgHom (R := K) (algebraMap k K s)).toRingHom).comp
            (Polynomial.mapRingHom (algebraMap k K)))))
      = kummerSubst K s e := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp
    · simp [add_comm]
  exact congrArg (fun f => f p) h.symm

/-- **The Kummer substitution is injective.** -/
theorem kummerSubst_injective (s : k) {e : ℕ} (he : 0 < e) :
    Function.Injective (kummerSubst K s e) := by
  intro p q hpq
  rw [kummerSubst_eq_comp, kummerSubst_eq_comp] at hpq
  exact Polynomial.map_injective _ (algebraMap k K).injective
    (taylor_injective _ (Polynomial.expand_injective he (Polynomial.coe_injective K hpq)))

/-! ### The Kummer substitution on the rational function field -/

/-- The composite of the Kummer substitution with the inclusion of power series into Laurent
series. -/
def kummerSubstLaurent (s : k) (e : ℕ) : Polynomial k →+* LaurentSeries K :=
  (algebraMap (PowerSeries K) (LaurentSeries K)).comp (kummerSubst K s e)

theorem kummerSubstLaurent_injective (s : k) {e : ℕ} (he : 0 < e) :
    Function.Injective (kummerSubstLaurent K s e) :=
  (IsFractionRing.injective (PowerSeries K) (LaurentSeries K)).comp (kummerSubst_injective K s he)

/-- **The Kummer substitution on the rational function field**: the local coordinate `X = s + u ^ e`
turns a rational function of the line into a formal Laurent series. -/
def kummerLift (s : k) {e : ℕ} (he : 0 < e) : RatFunc k →+* LaurentSeries K :=
  IsFractionRing.lift (A := Polynomial k) (K := RatFunc k)
    (kummerSubstLaurent_injective K s he)

@[simp] theorem kummerLift_algebraMap (s : k) {e : ℕ} (he : 0 < e) (p : Polynomial k) :
    kummerLift K s he (algebraMap (Polynomial k) (RatFunc k) p)
      = algebraMap (PowerSeries K) (LaurentSeries K) (kummerSubst K s e p) :=
  IsFractionRing.lift_algebraMap _ p

/-! ### Puiseux embeddings from a root -/

section OfRoot

variable {Ω : Type} [Field Ω] [Algebra (RatFunc k) Ω] [Algebra (Polynomial k) Ω]
  [IsScalarTower (Polynomial k) (RatFunc k) Ω]

/-- A homomorphism of the function field into Laurent series lying over the Kummer substitution of
the rational function field is a Puiseux embedding. -/
def PuiseuxEmbedding.ofRingHom (s : k) {e : ℕ} (he : 0 < e) (φ : Ω →+* LaurentSeries K)
    (hφ : ∀ x : RatFunc k, φ (algebraMap (RatFunc k) Ω x) = kummerLift K s he x) :
    PuiseuxEmbedding Ω K s e where
  hom := φ
  index_pos := he
  compat p := by
    rw [IsScalarTower.algebraMap_apply (Polynomial k) (RatFunc k) Ω, hφ, kummerLift_algebraMap]

/-- **A Laurent series root of the minimal polynomial of a primitive element is a Puiseux
parametrisation of the cover.** -/
theorem exists_puiseuxEmbedding_of_eval₂_eq_zero (s : k) {e : ℕ} (he : 0 < e) (α : Ω)
    (hα : IsIntegral (RatFunc k) α) (hgen : IntermediateField.adjoin (RatFunc k) {α} = ⊤)
    (y : LaurentSeries K)
    (hy : Polynomial.eval₂ (kummerLift K s he) y (minpoly (RatFunc k) α) = 0) :
    Nonempty (PuiseuxEmbedding Ω K s e) := by
  set g : Ω ≃ₐ[RatFunc k] AdjoinRoot (minpoly (RatFunc k) α) :=
    (IntermediateField.topEquiv.symm.trans
      ((IntermediateField.equivOfEq hgen).symm.trans
        (IntermediateField.adjoinRootEquivAdjoin (RatFunc k) hα).symm)) with hg
  refine ⟨PuiseuxEmbedding.ofRingHom K s he
    ((AdjoinRoot.lift (kummerLift K s he) y hy).comp (g : Ω →+* AdjoinRoot _)) fun x => ?_⟩
  have hx : g (algebraMap (RatFunc k) Ω x) = algebraMap (RatFunc k) _ x :=
    g.commutes x
  show AdjoinRoot.lift (kummerLift K s he) y hy (g (algebraMap (RatFunc k) Ω x)) = _
  rw [hx, AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.lift_of hy

end OfRoot

end Rigidity.RET

end

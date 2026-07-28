/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Hilbert.Analytic.NewtonPuiseux
import InverseGalois.Hilbert.Analytic.Primitivity

/-!
# The shared Serre base cover and its primitive geometric monodromy

This file establishes the *shared base polynomial cover* underlying both Serre alternating
families (`serreAnFamily` even and `serreAnFamilyOdd`), and proves its geometric monodromy is
**primitive** (preprimitive as a permutation action of the geometric Galois group over `ℚ̄(T)`).

The base cover is `p(X) = Xⁿ − (n/(n−1))·X^{n−1}` (the monic normalisation of Serre's
`(n−1)Xⁿ − nX^{n−1}`), with `p'(X) = n·X^{n−2}·(X−1)`.  The base *family* `p(X) − T` is **linear
in `T`**, so it is a polynomial cover, its root field over `ℚ̄(T)` is *rational*, and the
existing rational-cover machinery (`RittComposition`/`NewtonPuiseux`) applies.

The primitivity reduces (family-agnostically, via `InverseGalois.Primitivity`) to the
**indecomposability** of `p` (`serreBaseP_indecomposable`), which we prove by a short
*order-of-vanishing* argument at the degenerate critical point `X = 0` (order exactly `n−1`),
rather than the Morse critical-point count used for `Xⁿ − X`.

## Main definitions

* `SerreBaseCover.serreBaseP` — the cover polynomial `p(X)` over `ℚ̄`.
* `SerreBaseCover.serreBaseC` — the base family `p(X) − T` over `ℚ̄[T]`.
* `SerreBaseCover.serreBaseGeomPoly` — the base family base-changed to `ℚ̄(T)`.

## Main results

* `SerreBaseCover.serreBaseP_indecomposable` — `p` admits no decomposition `h ∘ g` with
  `deg h, deg g ≥ 2`.
* `SerreBaseCover.linearCover_adjoin_root_isAtom` — GENERIC: for any indecomposable `g₀`, a root
  of the linear cover generates an atom intermediate field.
* `SerreBaseCover.serreBaseGeomPoly_adjoin_root_isAtom` — the atom statement for the base cover.
* `SerreBaseCover.serreBaseGeomPoly_isPreprimitive` — the geometric monodromy action is
  preprimitive.
-/

open Polynomial
open scoped Polynomial.Bivariate

noncomputable section

namespace SerreBaseCover

/-- The polynomial always splits in its own splitting field (local `Fact` instance so that the
permutation representation `galActionHom` is well-formed). -/
local instance splitsInSplittingFieldSerre (F : Type*) [Field F] (p : F[X]) :
    Fact ((p.map (algebraMap F p.SplittingField)).Splits) := ⟨SplittingField.splits p⟩

/-! ## The generic linear cover -/

/-- The **linear cover family** attached to a base polynomial `g₀ ∈ ℚ̄[X]`: `g₀(X) − T`, viewed
over `ℚ̄[T]` (with the coefficient variable `C X` playing the role of `T`).  Mirror of
`genPolyC`, but with `Xⁿ − X` replaced by an arbitrary `g₀`. -/
noncomputable def linearCoverC (g₀ : (AlgebraicClosure ℚ)[X]) :
    (Polynomial (AlgebraicClosure ℚ))[X] :=
  g₀.map C - C X

/-- The linear cover family base-changed to the geometric base field `ℚ̄(T)`.  Mirror of
`morseGeomPoly`. -/
noncomputable def linearCoverGeom (g₀ : (AlgebraicClosure ℚ)[X]) : GeomBase[X] :=
  (linearCoverC g₀).map (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase)

/-- `linearCoverC g₀ = g₀(X) − T` is irreducible over `ℚ̄[T]`: it is linear in the coefficient
variable, so `Bivariate.swap` sends it (up to a unit) to `X − C g₀`, which is irreducible. -/
theorem linearCoverC_irreducible (g₀ : (AlgebraicClosure ℚ)[X]) :
    Irreducible (linearCoverC g₀) := by
  have hswap : Polynomial.Bivariate.swap (linearCoverC g₀)
      = -(X - C g₀) := by
    unfold linearCoverC
    rw [map_sub, Polynomial.Bivariate.swap_map_C, Polynomial.Bivariate.swap_C, Polynomial.map_X]
    ring
  have hirr : Irreducible (Polynomial.Bivariate.swap (linearCoverC g₀)) := by
    rw [hswap]
    have h := irreducible_X_sub_C (R := Polynomial (AlgebraicClosure ℚ)) g₀
    have hassoc : Associated (X - C g₀ : (Polynomial (AlgebraicClosure ℚ))[X])
        (-(X - C g₀)) := ⟨-1, by simp⟩
    exact hassoc.irreducible h
  exact (MulEquiv.irreducible_iff
    (Polynomial.Bivariate.swap (R := AlgebraicClosure ℚ)).toMulEquiv).mp hirr

/-- `linearCoverC g₀` is monic when `g₀` is monic of positive degree. -/
theorem linearCoverC_monic (g₀ : (AlgebraicClosure ℚ)[X]) (hg : g₀.Monic)
    (hd : 1 ≤ g₀.natDegree) : (linearCoverC g₀).Monic := by
  unfold linearCoverC
  rw [sub_eq_add_neg]
  refine (hg.map C).add_of_left ?_
  rw [degree_neg]
  refine lt_of_le_of_lt degree_C_le ?_
  rw [degree_eq_natDegree (hg.map C).ne_zero, natDegree_map_eq_of_injective Polynomial.C_injective]
  exact_mod_cast hd

/-- The degree of `linearCoverC g₀` equals the degree of `g₀`. -/
theorem linearCoverC_natDegree (g₀ : (AlgebraicClosure ℚ)[X]) (hd : 1 ≤ g₀.natDegree) :
    (linearCoverC g₀).natDegree = g₀.natDegree := by
  have hnd : (g₀.map C).natDegree = g₀.natDegree :=
    natDegree_map_eq_of_injective Polynomial.C_injective g₀
  unfold linearCoverC
  have hlt : (C X : (Polynomial (AlgebraicClosure ℚ))[X]).natDegree < (g₀.map C).natDegree := by
    rw [natDegree_C, hnd]; omega
  rw [natDegree_sub_eq_left_of_natDegree_lt hlt, hnd]

/-- `linearCoverGeom g₀` is monic when `g₀` is monic of positive degree. -/
theorem linearCoverGeom_monic (g₀ : (AlgebraicClosure ℚ)[X]) (hg : g₀.Monic)
    (hd : 1 ≤ g₀.natDegree) : (linearCoverGeom g₀).Monic :=
  (linearCoverC_monic g₀ hg hd).map _

/-- `linearCoverGeom g₀` is irreducible over `ℚ̄(T)` (Gauss's lemma from `ℚ̄[T]`). -/
theorem linearCoverGeom_irreducible (g₀ : (AlgebraicClosure ℚ)[X]) (hg : g₀.Monic)
    (hd : 1 ≤ g₀.natDegree) : Irreducible (linearCoverGeom g₀) := by
  rw [linearCoverGeom]
  exact (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map
    (linearCoverC_monic g₀ hg hd)).mp (linearCoverC_irreducible g₀)

/-- The degree of `linearCoverGeom g₀` equals the degree of `g₀`. -/
theorem linearCoverGeom_natDegree (g₀ : (AlgebraicClosure ℚ)[X]) (hd : 1 ≤ g₀.natDegree) :
    (linearCoverGeom g₀).natDegree = g₀.natDegree := by
  rw [linearCoverGeom, natDegree_map_eq_of_injective (IsFractionRing.injective _ _),
    linearCoverC_natDegree g₀ hd]

/-- `linearCoverGeom g₀` is separable over `ℚ̄(T)` (irreducible over a perfect base field). -/
theorem linearCoverGeom_separable (g₀ : (AlgebraicClosure ℚ)[X]) (hg : g₀.Monic)
    (hd : 1 ≤ g₀.natDegree) : (linearCoverGeom g₀).Separable :=
  (linearCoverGeom_irreducible g₀ hg hd).separable

/-- The root set of `linearCoverGeom g₀` in its splitting field has `g₀.natDegree` elements. -/
theorem linearCoverGeom_card_rootSet (g₀ : (AlgebraicClosure ℚ)[X]) (hg : g₀.Monic)
    (hd : 1 ≤ g₀.natDegree) :
    Fintype.card ((linearCoverGeom g₀).rootSet (linearCoverGeom g₀).SplittingField)
      = g₀.natDegree := by
  rw [Polynomial.card_rootSet_eq_natDegree (linearCoverGeom_separable g₀ hg hd)
      (SplittingField.splits _), linearCoverGeom_natDegree g₀ hd]

/-! ## The atom transport chain (generic in `g₀`) -/

/-- The root relation: for a root `↑a` of the linear cover, `aeval (↑a) g₀ = T`, the image of the
base transcendental.  Generalises `morse_aeval_gsub` (whose special fact was `aeval x (Xⁿ−X)=T`).
-/
theorem linearCover_aeval_g₀ (g₀ : (AlgebraicClosure ℚ)[X])
    (a : (linearCoverGeom g₀).rootSet (linearCoverGeom g₀).SplittingField) :
    aeval (↑a : (linearCoverGeom g₀).SplittingField) g₀
      = algebraMap GeomBase (linearCoverGeom g₀).SplittingField
          (algebraMap (AlgebraicClosure ℚ)[X] GeomBase X) := by
  have ha2 := (Polynomial.mem_rootSet.mp a.2).2
  have hcomp : ((algebraMap (AlgebraicClosure ℚ)[X] GeomBase).comp
      (C : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ)[X]))
      = algebraMap (AlgebraicClosure ℚ) GeomBase := by
    rw [← Polynomial.algebraMap_eq (R := AlgebraicClosure ℚ),
      IsScalarTower.algebraMap_eq (AlgebraicClosure ℚ) (AlgebraicClosure ℚ)[X] GeomBase]
  -- Rewrite the base-changed polynomial through `algebraMap ℚ̄ → ℚ̄(T)` (avoids a missing
  -- `Algebra ℚ̄[X] L` instance).
  have hpoly : linearCoverGeom g₀
      = g₀.map (algebraMap (AlgebraicClosure ℚ) GeomBase)
        - C (algebraMap (AlgebraicClosure ℚ)[X] GeomBase X) := by
    unfold linearCoverGeom linearCoverC
    rw [Polynomial.map_sub, Polynomial.map_map, hcomp, Polynomial.map_C]
  have haeval : aeval (↑a : (linearCoverGeom g₀).SplittingField) (linearCoverGeom g₀)
      = aeval (↑a : (linearCoverGeom g₀).SplittingField) g₀
        - algebraMap GeomBase (linearCoverGeom g₀).SplittingField
            (algebraMap (AlgebraicClosure ℚ)[X] GeomBase X) := by
    rw [congrArg (aeval (↑a : (linearCoverGeom g₀).SplittingField)) hpoly, map_sub,
      Polynomial.aeval_map_algebraMap, aeval_C]
  have hkey : aeval (↑a : (linearCoverGeom g₀).SplittingField) g₀
      - algebraMap GeomBase (linearCoverGeom g₀).SplittingField
          (algebraMap (AlgebraicClosure ℚ)[X] GeomBase X) = 0 := by
    rw [← haeval]; exact ha2
  exact sub_eq_zero.mp hkey

/-- A root `↑a` of the linear cover is transcendental over `ℚ̄`.  (Because `aeval (↑a) g₀ = T` is
transcendental, and `transcendental_aeval_iff` transfers this to `↑a`.)  Generalises
`morse_root_transcendental`. -/
theorem linearCover_root_transcendental (g₀ : (AlgebraicClosure ℚ)[X])
    (a : (linearCoverGeom g₀).rootSet (linearCoverGeom g₀).SplittingField) :
    Transcendental (AlgebraicClosure ℚ) (↑a : (linearCoverGeom g₀).SplittingField) := by
  have h_tL : aeval (↑a : (linearCoverGeom g₀).SplittingField) g₀
      = algebraMap GeomBase (linearCoverGeom g₀).SplittingField
          (algebraMap (AlgebraicClosure ℚ)[X] GeomBase X) := linearCover_aeval_g₀ g₀ a
  have h_tL_transc : Transcendental (AlgebraicClosure ℚ)
      (algebraMap GeomBase (linearCoverGeom g₀).SplittingField
        (algebraMap (AlgebraicClosure ℚ)[X] GeomBase X)) := by
    intro h
    convert geomBase_gen_transcendental using 1
    constructor <;> intro h <;> rw [Transcendental] at * <;> simp_all [IsAlgebraic]
  rw [← h_tL] at h_tL_transc
  exact (transcendental_aeval_iff.mp h_tL_transc).1

/-- The `ℚ̄`-algebra hom `Ψ : RatFunc ℚ̄ →ₐ[ℚ̄] L` sending `X ↦ ↑a`, well-defined and injective
because `↑a` is transcendental over `ℚ̄`.  Generalises `morseLift`. -/
noncomputable def linearCoverLift (g₀ : (AlgebraicClosure ℚ)[X])
    (a : (linearCoverGeom g₀).rootSet (linearCoverGeom g₀).SplittingField) :
    RatFunc (AlgebraicClosure ℚ) →ₐ[AlgebraicClosure ℚ]
      (linearCoverGeom g₀).SplittingField :=
  RatFunc.liftAlgHom (Polynomial.aeval (↑a : (linearCoverGeom g₀).SplittingField))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (transcendental_iff_injective.mp (linearCover_root_transcendental g₀ a)))

theorem linearCoverLift_apply_poly (g₀ : (AlgebraicClosure ℚ)[X])
    (a : (linearCoverGeom g₀).rootSet (linearCoverGeom g₀).SplittingField)
    (p : (AlgebraicClosure ℚ)[X]) :
    linearCoverLift g₀ a (algebraMap (AlgebraicClosure ℚ)[X] (RatFunc (AlgebraicClosure ℚ)) p)
      = aeval (↑a : (linearCoverGeom g₀).SplittingField) p := by
  have h := @RatFunc.liftAlgHom_apply_div
  have hnz := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (transcendental_iff_injective.mp (linearCover_root_transcendental g₀ a))
  convert h (Polynomial.aeval (a : (linearCoverGeom g₀).SplittingField)) hnz p 1 using 1 <;>
    simp [linearCoverLift]

theorem linearCoverLift_injective (g₀ : (AlgebraicClosure ℚ)[X])
    (a : (linearCoverGeom g₀).rootSet (linearCoverGeom g₀).SplittingField) :
    Function.Injective (linearCoverLift g₀ a) := by
  convert RatFunc.liftAlgHom_injective _ _
  exact transcendental_iff_injective.mp (linearCover_root_transcendental g₀ a)

/-- The range of `Ψ` is `ℚ̄(↑a)`.  Generalises `morseLift_fieldRange`. -/
theorem linearCoverLift_fieldRange (g₀ : (AlgebraicClosure ℚ)[X])
    (a : (linearCoverGeom g₀).rootSet (linearCoverGeom g₀).SplittingField) :
    (linearCoverLift g₀ a).fieldRange
      = IntermediateField.adjoin (AlgebraicClosure ℚ)
          {(↑a : (linearCoverGeom g₀).SplittingField)} := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨p, hp⟩ := hx
    simp at hp
    have h_image : p ∈ IntermediateField.adjoin (AlgebraicClosure ℚ) {RatFunc.X} := by
      rw [RatFunc.adjoin_X_top] at *
      aesop
    rw [← hp, IntermediateField.mem_adjoin_simple_iff] at *
    obtain ⟨r, s, rfl⟩ := h_image
    use r, s
    simp [linearCoverLift_apply_poly]
  · simp [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    use RatFunc.X
    convert linearCoverLift_apply_poly g₀ a Polynomial.X using 1
    norm_num

/-- Every element of the base `GeomBase`, mapped into `L`, lies in `ℚ̄(aeval (↑a) g₀)`.
Generalises `geomBase_image_mem_adjoin`. -/
theorem linearCover_geomBase_image_mem_adjoin (g₀ : (AlgebraicClosure ℚ)[X])
    (a : (linearCoverGeom g₀).rootSet (linearCoverGeom g₀).SplittingField) (y : GeomBase) :
    algebraMap GeomBase (linearCoverGeom g₀).SplittingField y
      ∈ IntermediateField.adjoin (AlgebraicClosure ℚ)
          {aeval (↑a : (linearCoverGeom g₀).SplittingField) g₀} := by
  obtain ⟨num, den, hden, hy⟩ :
      ∃ num den : Polynomial (AlgebraicClosure ℚ),
        den ∈ nonZeroDivisors (Polynomial (AlgebraicClosure ℚ)) ∧
          y = (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase num)
            / (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase den) := by
    have := IsFractionRing.div_surjective (A := Polynomial (AlgebraicClosure ℚ)) y
    aesop
  have h_algebraMap : ∀ p : Polynomial (AlgebraicClosure ℚ),
      algebraMap GeomBase (linearCoverGeom g₀).SplittingField
          (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase p)
        = aeval (aeval (↑a : (linearCoverGeom g₀).SplittingField) g₀) p := by
    have key : (IsScalarTower.toAlgHom (AlgebraicClosure ℚ) GeomBase
          (linearCoverGeom g₀).SplittingField).comp
          (IsScalarTower.toAlgHom (AlgebraicClosure ℚ) (Polynomial (AlgebraicClosure ℚ)) GeomBase)
        = (aeval (aeval (↑a : (linearCoverGeom g₀).SplittingField) g₀) :
            (AlgebraicClosure ℚ)[X] →ₐ[AlgebraicClosure ℚ] (linearCoverGeom g₀).SplittingField) := by
      apply Polynomial.algHom_ext
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', aeval_X]
      exact (linearCover_aeval_g₀ g₀ a).symm
    intro p
    have hp := DFunLike.congr_fun key p
    simpa only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] using hp
  simp_all [IntermediateField.mem_adjoin_simple_iff]
  exact ⟨num, den, rfl⟩

/-- The base subfield `GeomBase`, restricted to `ℚ̄`, equals `ℚ̄(aeval (↑a) g₀)`.
Generalises `geomBase_bot_restrict`. -/
theorem linearCover_geomBase_bot_restrict (g₀ : (AlgebraicClosure ℚ)[X])
    (a : (linearCoverGeom g₀).rootSet (linearCoverGeom g₀).SplittingField) :
    (⊥ : IntermediateField GeomBase (linearCoverGeom g₀).SplittingField).restrictScalars
        (AlgebraicClosure ℚ)
      = IntermediateField.adjoin (AlgebraicClosure ℚ)
          {aeval (↑a : (linearCoverGeom g₀).SplittingField) g₀} := by
  refine le_antisymm ?_ ?_
  · intro z hz
    obtain ⟨y, rfl⟩ := hz
    exact linearCover_geomBase_image_mem_adjoin g₀ a y
  · simp [IntermediateField.mem_bot]
    use algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase (Polynomial.X)
    rw [← linearCover_aeval_g₀ g₀ a]

/-- `ℚ̄(T)(↑a) = ℚ̄(↑a)`: the base-restriction of `adjoin GeomBase {↑a}` is `ℚ̄(↑a)`.
Generalises `adjoin_geomBase_restrict`. -/
theorem linearCover_adjoin_geomBase_restrict (g₀ : (AlgebraicClosure ℚ)[X])
    (a : (linearCoverGeom g₀).rootSet (linearCoverGeom g₀).SplittingField) :
    (IntermediateField.adjoin GeomBase
        {(↑a : (linearCoverGeom g₀).SplittingField)}).restrictScalars (AlgebraicClosure ℚ)
      = IntermediateField.adjoin (AlgebraicClosure ℚ)
          {(↑a : (linearCoverGeom g₀).SplittingField)} := by
  refine le_antisymm ?_ ?_
  · intro x hx
    have hbot := linearCover_geomBase_bot_restrict g₀ a
    have h_adjoin : IntermediateField.adjoin (AlgebraicClosure ℚ)
          {aeval (↑a : (linearCoverGeom g₀).SplittingField) g₀}
        ≤ IntermediateField.adjoin (AlgebraicClosure ℚ)
            {(↑a : (linearCoverGeom g₀).SplittingField)} := by
      rw [IntermediateField.adjoin_simple_le_iff]
      exact IntermediateField.algebra_adjoin_le_adjoin _ _
        (Polynomial.aeval_mem_adjoin_singleton _ _)
    rw [← hbot] at *
    simp_all [IntermediateField.restrictScalars]
    rw [Subsemiring.mem_closure] at hx
    refine hx _ fun z hz ↦ ?_
    rcases hz with (rfl | ⟨z, rfl⟩)
    · exact IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
    · exact h_adjoin (Set.mem_range_self _)
  · simp

/-- A root `↑a` of the linear cover generates a nontrivial intermediate field.  Generalises
`morseGeomPoly_adjoin_root_ne_bot`. -/
theorem linearCover_adjoin_root_ne_bot (g₀ : (AlgebraicClosure ℚ)[X]) (hg : g₀.Monic)
    (hd : 2 ≤ g₀.natDegree)
    (a : (linearCoverGeom g₀).rootSet (linearCoverGeom g₀).SplittingField) :
    IntermediateField.adjoin GeomBase
        {(↑a : (linearCoverGeom g₀).SplittingField)} ≠ ⊥ := by
  have h_min_poly : minpoly GeomBase (a : (linearCoverGeom g₀).SplittingField)
      = linearCoverGeom g₀ := by
    refine Eq.symm (minpoly.eq_of_irreducible_of_monic ?_ ?_ ?_) <;>
      norm_num [linearCoverGeom_irreducible g₀ hg (by omega), linearCoverGeom_monic g₀ hg (by omega)]
    exact Polynomial.mem_rootSet.mp a.2 |>.2
  intro h
  have h_deg : (minpoly GeomBase (a : (linearCoverGeom g₀).SplittingField)).natDegree ≤ 1 := by
    have h_deg : ∃ c : GeomBase,
        (algebraMap GeomBase (linearCoverGeom g₀).SplittingField) c = a :=
      IntermediateField.mem_bot.mp (h ▸ IntermediateField.mem_adjoin_simple_self GeomBase _)
    obtain ⟨c, hc⟩ := h_deg
    have hac : (a : (linearCoverGeom g₀).SplittingField)
        = (algebraMap GeomBase (linearCoverGeom g₀).SplittingField) c := hc.symm
    rw [hac]
    simp [minpoly.eq_X_sub_C]
  refine absurd h_deg ?_
  rw [h_min_poly, linearCoverGeom_natDegree g₀ (by omega)]
  omega

/-- **[GENERIC — no intermediate field]** For an indecomposable base polynomial `g₀`, there is no
intermediate field strictly between `ℚ̄(T)` and `ℚ̄(T)(↑a)`.  Generalises
`morseGeomPoly_no_intermediate`; the only family-specific fact used is `linearCover_aeval_g₀`,
and indecomposability of `g₀` is fed to `RatFunc.isCoatom_adjoin_of_indecomposable`. -/
theorem linearCover_no_intermediate (g₀ : (AlgebraicClosure ℚ)[X]) (_hg : g₀.Monic)
    (hd : 2 ≤ g₀.natDegree)
    (hind : ∀ h g : (AlgebraicClosure ℚ)[X], 2 ≤ h.natDegree → 2 ≤ g.natDegree → g₀ ≠ h.comp g)
    (a : (linearCoverGeom g₀).rootSet (linearCoverGeom g₀).SplittingField)
    (b : IntermediateField GeomBase (linearCoverGeom g₀).SplittingField)
    (hb : b < IntermediateField.adjoin GeomBase
        {(↑a : (linearCoverGeom g₀).SplittingField)}) :
    b = ⊥ := by
  by_contra h
  set M := IntermediateField.comap (linearCoverLift g₀ a) (b.restrictScalars (AlgebraicClosure ℚ))
  have hM : M = ⊤ ∨ M = IntermediateField.adjoin (AlgebraicClosure ℚ)
      {(algebraMap (AlgebraicClosure ℚ)[X] (RatFunc (AlgebraicClosure ℚ)) g₀)} := by
    have hCoatom : IsCoatom (IntermediateField.adjoin (AlgebraicClosure ℚ)
        {(algebraMap (AlgebraicClosure ℚ)[X] (RatFunc (AlgebraicClosure ℚ)) g₀)}) := by
      apply RatFunc.isCoatom_adjoin_of_indecomposable
      · exact hd
      · exact fun h g hh hg' ↦ hind h g hh hg'
    have hle : IntermediateField.adjoin (AlgebraicClosure ℚ)
          {(algebraMap (AlgebraicClosure ℚ)[X] (RatFunc (AlgebraicClosure ℚ)) g₀)} ≤ M := by
      rw [IntermediateField.adjoin_simple_le_iff]
      have hmem : (linearCoverLift g₀ a) (algebraMap (AlgebraicClosure ℚ)[X]
          (RatFunc (AlgebraicClosure ℚ)) g₀) ∈ b := by
        convert b.algebraMap_mem (algebraMap (AlgebraicClosure ℚ)[X] GeomBase X) using 1
        convert linearCover_aeval_g₀ g₀ a using 1
        exact linearCoverLift_apply_poly g₀ a _
      exact hmem
    cases eq_or_lt_of_le hle <;> simp_all [IsCoatom]
    grind
  cases' hM with hM hM
  · have h_image : IntermediateField.adjoin (AlgebraicClosure ℚ)
          {(↑a : (linearCoverGeom g₀).SplittingField)}
        ≤ b.restrictScalars (AlgebraicClosure ℚ) := by
      have h_map_le : IntermediateField.map (linearCoverLift g₀ a) ⊤
          ≤ b.restrictScalars (AlgebraicClosure ℚ) := by
        rw [IntermediateField.map_le_iff_le_comap]
        aesop
      convert h_map_le using 1
      rw [← linearCoverLift_fieldRange]
      ext
      simp [AlgHom.fieldRange_eq_map]
    apply hb.not_ge
    simpa [linearCover_adjoin_geomBase_restrict] using h_image
  · have h_map : IntermediateField.map (linearCoverLift g₀ a) M
        = b.restrictScalars (AlgebraicClosure ℚ) := by
      rw [IntermediateField.map_comap_eq]
      apply inf_eq_left.mpr
      rw [linearCoverLift_fieldRange]
      refine le_trans (IntermediateField.restrictScalars_le_iff _ |>.2 hb.le) ?_
      simp [linearCover_adjoin_geomBase_restrict]
    have h_map_adjoin : IntermediateField.map (linearCoverLift g₀ a) M
        = IntermediateField.adjoin (AlgebraicClosure ℚ)
            {aeval (↑a : (linearCoverGeom g₀).SplittingField) g₀} := by
      rw [hM, IntermediateField.adjoin_map, Set.image_singleton, linearCoverLift_apply_poly]
    have h_contra : b.restrictScalars (AlgebraicClosure ℚ)
        = (⊥ : IntermediateField GeomBase (linearCoverGeom g₀).SplittingField).restrictScalars
            (AlgebraicClosure ℚ) := by
      rw [← h_map, h_map_adjoin, ← linearCover_geomBase_bot_restrict g₀ a]
    apply h
    simpa using congr_arg (fun x ↦ x) h_contra

/-- **[GENERIC — the atom]** For an indecomposable base polynomial `g₀`, every root of the linear
cover generates an atom `ℚ̄(T)(↑a)` in the lattice of intermediate fields.  This is the linchpin
for primitivity.  Generalises `morseGeomPoly_adjoin_root_isAtom`. -/
theorem linearCover_adjoin_root_isAtom (g₀ : (AlgebraicClosure ℚ)[X]) (hg : g₀.Monic)
    (hd : 2 ≤ g₀.natDegree)
    (hind : ∀ h g : (AlgebraicClosure ℚ)[X], 2 ≤ h.natDegree → 2 ≤ g.natDegree → g₀ ≠ h.comp g)
    (a : (linearCoverGeom g₀).rootSet (linearCoverGeom g₀).SplittingField) :
    IsAtom (IntermediateField.adjoin GeomBase
      {(↑a : (linearCoverGeom g₀).SplittingField)}) :=
  ⟨linearCover_adjoin_root_ne_bot g₀ hg hd a,
    linearCover_no_intermediate g₀ hg hd hind a⟩

/-! ## The Serre base cover -/

/-- The **Serre base cover** `p(X) = Xⁿ − (n/(n−1))·X^{n−1} ∈ ℚ̄[X]` (the monic normalisation of
Serre's `(n−1)Xⁿ − nX^{n−1}`).  Its derivative is `n·X^{n−2}·(X−1)`, so `X = 0` is a critical
point of order `n−1` and `X = 1` is a simple critical point.  This is the shared cover underlying
both the even (`serreAnFamily`) and odd (`serreAnFamilyOdd`) Serre alternating families. -/
noncomputable def serreBaseP (n : ℕ) : (AlgebraicClosure ℚ)[X] :=
  X ^ n - C ((n : AlgebraicClosure ℚ) / ((n : AlgebraicClosure ℚ) - 1)) * X ^ (n - 1)

/-- The Serre base family `p(X) − T` over `ℚ̄[T]`.  Definitionally `linearCoverC (serreBaseP n)`,
i.e. `Xⁿ − C(C(n/(n−1)))·X^{n−1} − C X`. -/
noncomputable def serreBaseC (n : ℕ) : (Polynomial (AlgebraicClosure ℚ))[X] :=
  linearCoverC (serreBaseP n)

/-- The Serre base family base-changed to the geometric base field `ℚ̄(T)`.  Definitionally
`linearCoverGeom (serreBaseP n)`. -/
noncomputable def serreBaseGeomPoly (n : ℕ) : GeomBase[X] :=
  linearCoverGeom (serreBaseP n)

/-- The nonzero scalar `n/(n−1) ∈ ℚ̄` for `n ≥ 2`. -/
theorem serreBaseP_coeff_ne_zero (n : ℕ) (hn : 2 ≤ n) :
    (n : AlgebraicClosure ℚ) / ((n : AlgebraicClosure ℚ) - 1) ≠ 0 := by
  have hne : (n : AlgebraicClosure ℚ) ≠ 1 := by
    have : (n : ℕ) ≠ 1 := by omega
    exact_mod_cast this
  have hn1 : ((n : AlgebraicClosure ℚ) - 1) ≠ 0 := sub_ne_zero.mpr hne
  have hn0 : (n : AlgebraicClosure ℚ) ≠ 0 := by
    have : (n : ℕ) ≠ 0 := by omega
    exact_mod_cast this
  exact div_ne_zero hn0 hn1

/-- Factorisation `serreBaseP n = X^{n-1} · (X − C (n/(n−1)))`. -/
theorem serreBaseP_factor (n : ℕ) (hn : 2 ≤ n) :
    serreBaseP n = X ^ (n - 1)
      * (X - C ((n : AlgebraicClosure ℚ) / ((n : AlgebraicClosure ℚ) - 1))) := by
  unfold serreBaseP
  have hpow : (X : (AlgebraicClosure ℚ)[X]) ^ n = X ^ (n - 1) * X := by
    rw [← pow_succ]; congr 1; omega
  rw [hpow]; ring

/-- `serreBaseP n` is monic for `n ≥ 2`. -/
theorem serreBaseP_monic (n : ℕ) (hn : 2 ≤ n) : (serreBaseP n).Monic := by
  unfold serreBaseP
  apply monic_X_pow_sub
  refine lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) ?_
  exact_mod_cast (by omega : n - 1 < n)

/-- `serreBaseP n` has degree `n` for `n ≥ 2`. -/
theorem serreBaseP_natDegree (n : ℕ) (hn : 2 ≤ n) : (serreBaseP n).natDegree = n := by
  unfold serreBaseP
  rw [natDegree_sub_eq_left_of_natDegree_lt, natDegree_X_pow]
  rw [natDegree_X_pow]
  refine lt_of_le_of_lt (natDegree_C_mul_le _ _) ?_
  rw [natDegree_X_pow]; omega

/-! ### Indecomposability of the base cover (B1) -/

/-- **Composition trailing-degree formula.**  Over a field, if `G(0) = 0` (equivalently
`X ∣ G`) and `H, G ≠ 0`, then the order of vanishing at `0` multiplies under composition:
`natTrailingDegree (H ∘ G) = natTrailingDegree H · natTrailingDegree G`.  This is the algebraic
core of the order-of-vanishing argument for `serreBaseP_indecomposable`. -/
theorem natTrailingDegree_comp_of_coeff_zero
    {H G : (AlgebraicClosure ℚ)[X]} (hH : H ≠ 0) (hG : G ≠ 0) (hG0 : G.coeff 0 = 0) :
    (H.comp G).natTrailingDegree = H.natTrailingDegree * G.natTrailingDegree := by
  -- Factor `H = X ^ m * H₁` with `X ∤ H₁`, `m = rootMultiplicity 0 H = natTrailingDegree H`.
  obtain ⟨H₁, hHfac, hHndvd⟩ :=
    H.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hH 0
  set m := H.rootMultiplicity 0 with hm
  have hm_eq : m = H.natTrailingDegree := by
    rw [hm, rootMultiplicity_eq_natTrailingDegree']
  simp only [map_zero, sub_zero] at hHfac hHndvd
  -- `H₁ (0) ≠ 0` since `X ∤ H₁`.
  have hH₁0 : H₁.coeff 0 ≠ 0 := fun hc => hHndvd (Polynomial.X_dvd_iff.mpr hc)
  have hH₁ne : H₁ ≠ 0 := by
    intro h; apply hH₁0; rw [h]; simp
  -- `H.comp G = G ^ m * (H₁.comp G)`.
  have hcomp : H.comp G = G ^ m * (H₁.comp G) := by
    conv_lhs => rw [hHfac]
    rw [mul_comp, pow_comp, X_comp]
  -- `natTrailingDegree (G ^ k) = k * natTrailingDegree G`.
  have hpow : ∀ k : ℕ, (G ^ k).natTrailingDegree = k * G.natTrailingDegree := by
    intro k
    induction k with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, natTrailingDegree_mul (pow_ne_zero j hG) hG, ih]; ring
  -- `natTrailingDegree (H₁.comp G) = 0` since its constant coefficient is `H₁(0) ≠ 0`.
  have hG0' : G.eval 0 = 0 := by rw [← coeff_zero_eq_eval_zero]; exact hG0
  have hcompconst : (H₁.comp G).coeff 0 ≠ 0 := by
    rw [coeff_zero_eq_eval_zero, eval_comp, hG0', ← coeff_zero_eq_eval_zero]; exact hH₁0
  have hcompne : H₁.comp G ≠ 0 := by
    intro h; apply hcompconst; rw [h]; simp
  have hzero : (H₁.comp G).natTrailingDegree = 0 := by
    rw [natTrailingDegree_eq_zero]; exact Or.inr hcompconst
  rw [hcomp, natTrailingDegree_mul (pow_ne_zero m hG) hcompne, hpow, hzero, add_zero, hm_eq]

/-- Arithmetic obstruction: there are no `u ∈ [1,a], v ∈ [1,b]` with `u·v = a·b − 1` when
`a, b ≥ 2`.  (`a·b − u·v = a(b−v) + v(a−u)`, forcing one factor `≥ 2 > 1`.) -/
theorem no_prod_eq_pred (a b u v : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (_hu1 : 1 ≤ u) (hua : u ≤ a) (_hv1 : 1 ≤ v) (hvb : v ≤ b)
    (h : u * v = a * b - 1) : False := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hua   -- `a = u + s`
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hvb   -- `b = v + t`
  -- `(u+s)*(v+t) = u*v + (u*t + s*v + s*t)`, and `(u+s)*(v+t) ≥ 1`, so `u*t + s*v + s*t = 1`.
  have hExpand : (u + s) * (v + t) = u * v + (u * t + s * v + s * t) := by ring
  have hpos : 1 ≤ (u + s) * (v + t) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  -- Set the products as atoms so `omega` can reason linearly.
  set P := (u + s) * (v + t) with hP
  set Q := u * v with hQ
  set p := u * t with hp
  set q := s * v with hq
  set r := s * t with hr
  -- `hExpand : P = Q + (p + q + r)`, `h : Q = P - 1`, `hpos : 1 ≤ P`.
  have h2 : p + q + r = 1 := by omega
  rcases Nat.eq_zero_or_pos s with hs | hs
  · -- `s = 0`: then `q = r = 0`, so `p = u*t = 1`, giving `u = 1`, contradicting `a = u ≥ 2`.
    have hq0 : q = 0 := by rw [hq, hs]; simp
    have hr0 : r = 0 := by rw [hr, hs]; simp
    have hp1 : u * t = 1 := by rw [← hp]; omega
    obtain ⟨hu', ht'⟩ := mul_eq_one.mp hp1
    omega
  · -- `s ≥ 1`: then `q = s*v ≥ 1`, forcing `q = 1`, `p = r = 0`.
    have hqpos : 1 ≤ q := by
      rw [hq]; exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have hq1 : s * v = 1 := by rw [← hq]; omega
    have hr0 : s * t = 0 := by rw [← hr]; omega
    obtain ⟨hs1, hv1'⟩ := mul_eq_one.mp hq1
    rw [hs1] at hr0
    simp at hr0
    omega

/-- **[B1 — Indecomposability of the base cover]** The Serre base cover `p(X)` admits no
decomposition `p = h ∘ g` with `deg h, deg g ≥ 2`.

Proof by order of vanishing: `p` vanishes to order exactly `n−1` at `X = 0`.  Writing
`p = h ∘ g`, `β = g(0)`, one gets `p = hβ ∘ G` with `G = g − β` and `hβ = h(· + β)` both
vanishing at `0`; multiplicativity of the vanishing order (`natTrailingDegree_comp_of_coeff_zero`)
gives `u·v = n−1` with `u = ord₀(hβ) ∈ [1,a]`, `v = ord₀(G) ∈ [1,b]`, `a·b = n`, contradicting
`no_prod_eq_pred`. -/
theorem serreBaseP_indecomposable (n : ℕ) (hn : 3 ≤ n)
    {h g : (AlgebraicClosure ℚ)[X]} (hh : 2 ≤ h.natDegree) (hg : 2 ≤ g.natDegree) :
    serreBaseP n ≠ h.comp g := by
  intro h_eq
  set a := h.natDegree with ha_def
  set b := g.natDegree with hb_def
  -- Degrees multiply: `a * b = n`.
  have hab : a * b = n := by
    have h2 := congrArg Polynomial.natDegree h_eq
    rw [serreBaseP_natDegree n (by omega), natDegree_comp] at h2
    rw [← ha_def, ← hb_def] at h2
    exact h2.symm
  set β := g.eval 0 with hβ_def
  set G := g - C β with hG_def
  set hβ := h.comp (X + C β) with hhβ_def
  -- `p = hβ ∘ G`.
  have hpG : serreBaseP n = hβ.comp G := by
    rw [h_eq, hhβ_def, hG_def]
    rw [comp_assoc]
    congr 1
    simp [add_comp, X_comp, C_comp, sub_add_cancel]
  -- `G(0) = 0` and `G ≠ 0`.
  have hGdeg : G.natDegree = b := by rw [hG_def, natDegree_sub_C]
  have hGne : G ≠ 0 := by
    intro h0; rw [h0, natDegree_zero] at hGdeg; omega
  have hG0 : G.coeff 0 = 0 := by
    rw [hG_def, coeff_sub, coeff_C_zero, coeff_zero_eq_eval_zero, ← hβ_def, sub_self]
  -- `hβ(0) = 0` (since `p(0) = 0`) and `hβ ≠ 0`.
  have hpeval0 : (serreBaseP n).eval 0 = 0 := by
    rw [serreBaseP_factor n (by omega)]; simp; left; omega
  have hβdeg : hβ.natDegree = a := by
    rw [hhβ_def, natDegree_comp, natDegree_X_add_C, mul_one, ← ha_def]
  have hβne : hβ ≠ 0 := by
    intro h0; rw [h0, natDegree_zero] at hβdeg; omega
  have hβ0 : hβ.coeff 0 = 0 := by
    have hev : hβ.eval (G.eval 0) = 0 := by
      have hcompeval : (hβ.comp G).eval 0 = hβ.eval (G.eval 0) := by rw [eval_comp]
      rw [← hcompeval, ← hpG, hpeval0]
    have hGeval0 : G.eval 0 = 0 := by rw [← coeff_zero_eq_eval_zero]; exact hG0
    rw [hGeval0] at hev
    rw [coeff_zero_eq_eval_zero]; exact hev
  -- The multiplicities.
  set u := hβ.natTrailingDegree with hu_def
  set v := G.natTrailingDegree with hv_def
  -- `ord₀(p) = u * v`.
  have hord : (serreBaseP n).natTrailingDegree = u * v := by
    rw [hpG, natTrailingDegree_comp_of_coeff_zero hβne hGne hG0]
  -- `ord₀(p) = n - 1`.
  have hordP : (serreBaseP n).natTrailingDegree = n - 1 := by
    rw [serreBaseP_factor n (by omega),
      natTrailingDegree_mul (pow_ne_zero _ (X_ne_zero (R := AlgebraicClosure ℚ)))
        (by
          intro h0
          have : (X - C ((n : AlgebraicClosure ℚ) / ((n : AlgebraicClosure ℚ) - 1))
              : (AlgebraicClosure ℚ)[X]).coeff 0 = 0 := by rw [h0]; simp
          rw [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, neg_eq_zero] at this
          exact serreBaseP_coeff_ne_zero n (by omega) this)]
    rw [natTrailingDegree_X_pow]
    have : (X - C ((n : AlgebraicClosure ℚ) / ((n : AlgebraicClosure ℚ) - 1))
        : (AlgebraicClosure ℚ)[X]).natTrailingDegree = 0 := by
      rw [natTrailingDegree_eq_zero]
      right
      rw [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, neg_ne_zero]
      exact serreBaseP_coeff_ne_zero n (by omega)
    rw [this, add_zero]
  -- So `u * v = n - 1 = a * b - 1`.
  have huv : u * v = a * b - 1 := by rw [hab, ← hordP, hord]
  -- Bounds.
  have hu_le : u ≤ a := by rw [hu_def, ← hβdeg]; exact natTrailingDegree_le_natDegree _
  have hv_le : v ≤ b := by rw [hv_def, ← hGdeg]; exact natTrailingDegree_le_natDegree _
  have hu_ge : 1 ≤ u := by
    rw [hu_def]
    rcases Nat.eq_zero_or_pos hβ.natTrailingDegree with h0 | h0
    · exfalso
      rcases (natTrailingDegree_eq_zero).mp h0 with hz | hc
      · exact hβne hz
      · exact hc hβ0
    · exact h0
  have hv_ge : 1 ≤ v := by
    rw [hv_def]
    rcases Nat.eq_zero_or_pos G.natTrailingDegree with h0 | h0
    · exfalso
      rcases (natTrailingDegree_eq_zero).mp h0 with hz | hc
      · exact hGne hz
      · exact hc hG0
    · exact h0
  exact no_prod_eq_pred a b u v hh hg hu_ge hu_le hv_ge hv_le huv

/-! ### Basic lemmas for the Serre base cover (A1) -/

/-- `serreBaseC n` is monic for `n ≥ 2`. -/
theorem serreBaseC_monic (n : ℕ) (hn : 2 ≤ n) : (serreBaseC n).Monic :=
  linearCoverC_monic (serreBaseP n) (serreBaseP_monic n hn)
    (by rw [serreBaseP_natDegree n hn]; omega)

/-- `serreBaseC n` is irreducible over `ℚ̄[T]`. -/
theorem serreBaseC_irreducible (n : ℕ) : Irreducible (serreBaseC n) :=
  linearCoverC_irreducible (serreBaseP n)

/-- `serreBaseC n` has degree `n` for `n ≥ 2`. -/
theorem serreBaseC_natDegree (n : ℕ) (hn : 2 ≤ n) : (serreBaseC n).natDegree = n := by
  rw [serreBaseC, linearCoverC_natDegree (serreBaseP n) (by rw [serreBaseP_natDegree n hn]; omega),
    serreBaseP_natDegree n hn]

/-- `serreBaseGeomPoly n` is monic for `n ≥ 2`. -/
theorem serreBaseGeomPoly_monic (n : ℕ) (hn : 2 ≤ n) : (serreBaseGeomPoly n).Monic :=
  linearCoverGeom_monic (serreBaseP n) (serreBaseP_monic n hn)
    (by rw [serreBaseP_natDegree n hn]; omega)

/-- `serreBaseGeomPoly n` is irreducible over `ℚ̄(T)` for `n ≥ 2`. -/
theorem serreBaseGeomPoly_irreducible (n : ℕ) (hn : 2 ≤ n) :
    Irreducible (serreBaseGeomPoly n) :=
  linearCoverGeom_irreducible (serreBaseP n) (serreBaseP_monic n hn)
    (by rw [serreBaseP_natDegree n hn]; omega)

/-- `serreBaseGeomPoly n` has degree `n` for `n ≥ 2`. -/
theorem serreBaseGeomPoly_natDegree (n : ℕ) (hn : 2 ≤ n) :
    (serreBaseGeomPoly n).natDegree = n := by
  rw [serreBaseGeomPoly, linearCoverGeom_natDegree (serreBaseP n)
    (by rw [serreBaseP_natDegree n hn]; omega), serreBaseP_natDegree n hn]

/-- `serreBaseGeomPoly n` is separable over `ℚ̄(T)` for `n ≥ 2`. -/
theorem serreBaseGeomPoly_separable (n : ℕ) (hn : 2 ≤ n) :
    (serreBaseGeomPoly n).Separable :=
  linearCoverGeom_separable (serreBaseP n) (serreBaseP_monic n hn)
    (by rw [serreBaseP_natDegree n hn]; omega)

/-- The root set of `serreBaseGeomPoly n` has exactly `n` elements for `n ≥ 2`. -/
theorem serreBaseGeomPoly_card_rootSet (n : ℕ) (hn : 2 ≤ n) :
    Fintype.card ((serreBaseGeomPoly n).rootSet (serreBaseGeomPoly n).SplittingField) = n := by
  rw [serreBaseGeomPoly, linearCoverGeom_card_rootSet (serreBaseP n) (serreBaseP_monic n hn)
    (by rw [serreBaseP_natDegree n hn]; omega), serreBaseP_natDegree n hn]

/-! ### Primitivity of the base cover (B2) -/

/-- **[B2 — the atom]** Every geometric root of `serreBaseGeomPoly n` generates an atom
intermediate field over `ℚ̄(T)`. -/
theorem serreBaseGeomPoly_adjoin_root_isAtom (n : ℕ) (hn : 3 ≤ n)
    (a : (serreBaseGeomPoly n).rootSet (serreBaseGeomPoly n).SplittingField) :
    IsAtom (IntermediateField.adjoin GeomBase
      {(↑a : (serreBaseGeomPoly n).SplittingField)}) :=
  linearCover_adjoin_root_isAtom (serreBaseP n) (serreBaseP_monic n (by omega))
    (by rw [serreBaseP_natDegree n (by omega)]; omega)
    (fun h g hh hg => serreBaseP_indecomposable n hn hh hg) a

/-- **[B2 — primitivity]** The geometric Galois group of the Serre base cover acts
**preprimitively** on the roots.  Assembled family-agnostically from
`InverseGalois.Primitivity.galActionHom_range_isPreprimitive_of_isAtom` fed separability,
irreducibility (transitivity), nontriviality, and the atom leaf. -/
theorem serreBaseGeomPoly_isPreprimitive (n : ℕ) (hn : 3 ≤ n) :
    MulAction.IsPreprimitive
      (Gal.galActionHom (serreBaseGeomPoly n) (serreBaseGeomPoly n).SplittingField).range
      ((serreBaseGeomPoly n).rootSet (serreBaseGeomPoly n).SplittingField) := by
  haveI hnt : Nontrivial
      ((serreBaseGeomPoly n).rootSet (serreBaseGeomPoly n).SplittingField) := by
    rw [← Fintype.one_lt_card_iff_nontrivial, serreBaseGeomPoly_card_rootSet n (by omega)]
    omega
  exact InverseGalois.Primitivity.galActionHom_range_isPreprimitive_of_isAtom
    (serreBaseGeomPoly n) (serreBaseGeomPoly_separable n (by omega))
    (serreBaseGeomPoly_irreducible n (by omega)) hnt
    (serreBaseGeomPoly_adjoin_root_isAtom n hn)

end SerreBaseCover

end

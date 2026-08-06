/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.GeometricIrreducibility

/-!
# Regularity ⟹ base-change is a field, over a general base field `k₀`

This file is a **base-field-generalised** port of the regularity core proved in
`InverseGalois.Rigidity.RET.GeometricIrreducibility` (`isField_baseChange_of_regular`, over `ℚ`).

For a field `k₀` of characteristic zero and a finite extension `L / k₀(T)` in which `k₀` is
relatively algebraically closed (`algebraicClosure k₀ L = ⊥`, "regular"), the base change of `L`
to the geometric base field `k₀‾(T) = FractionRing k₀‾[X]` (where `k₀‾ = AlgebraicClosure k₀`) is a
**field**.

The proof is a mechanical replay of the `ℚ`-argument with `k₀` in place of `ℚ`.  Every dependency
lemma of the `ℚ`-proof (`regular_ratFunc`, the colimit infrastructure `extract`, `geomPrim`,
`geomVar_mem`, `geomPoly_mem`, `geomElt_mem`, `toClosureFrac`, `isAlgebraic_ratFunc_geom`) is
field-agnostic and gets a `_gen` counterpart here.  The finite building blocks
(`irreducible_map_of_algClosure_eq_bot`, `isField_tensor_of_primitive_irreducible`,
`irreducible_map_minpoly_of_isField_baseChange`) are already generic over their field arguments and
are reused directly from `GeometricIrreducibility`.

## The one honest difference from the `ℚ`-proof

The `ℚ`-proof discharges the algebra-map compatibility `hcomp1`
(`(algebraMap (RatFunc ℚ) geom).comp (algebraMap ℚ (RatFunc ℚ)) = algebraMap ℚ geom`) by
`Subsingleton.elim`, using that ring homs out of `ℚ` are unique.  Over a general `k₀` this is not
available; instead we establish the honest scalar-tower `IsScalarTower k₀ (RatFunc k₀) geom`
(`instTowerBaseRatFuncGeom_gen`) and read the compatibility off it via `IsScalarTower.algebraMap_eq`.
No extra hypothesis beyond `[Field k₀] [CharZero k₀]` is needed: the ambient `Algebra k₀ geom`
comes for free (the `k₀ → k₀‾[X] → FractionRing` Ore/localisation path), and the tower with
`RatFunc k₀` is proved from the two localisation presentations agreeing on `k₀[X]`.
-/

open Polynomial

open scoped TensorProduct

namespace Rigidity.RET.Descent

noncomputable section

open scoped Polynomial

attribute [local instance] Polynomial.algebra

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1000000

variable {k₀ : Type*} [Field k₀]

/-! ## The geometric base field `k₀‾(T)` and the `RatFunc k₀`-algebra structure -/

/-- The base-change-then-localise ring hom `k₀[T] → k₀‾(T) = FractionRing k₀‾[T]`: map coefficients
along `k₀ → k₀‾`, then include `k₀‾[T]` into its fraction field.  (Port of `toClosureFrac`.) -/
noncomputable def toClosureFrac_gen :
    k₀[X] →+* FractionRing (Polynomial (AlgebraicClosure k₀)) :=
  (algebraMap (Polynomial (AlgebraicClosure k₀))
      (FractionRing (Polynomial (AlgebraicClosure k₀)))).comp
    (mapRingHom (algebraMap k₀ (AlgebraicClosure k₀)))

theorem toClosureFrac_gen_injective :
    Function.Injective (toClosureFrac_gen (k₀ := k₀)) :=
  (IsFractionRing.injective (Polynomial (AlgebraicClosure k₀))
      (FractionRing (Polynomial (AlgebraicClosure k₀)))).comp
    (Polynomial.map_injective _ (FaithfulSMul.algebraMap_injective k₀ (AlgebraicClosure k₀)))

/-- The geometric base field `k₀‾(T)` is a `k₀(T)`-algebra, via the fraction-field lift of
`toClosureFrac_gen`. -/
noncomputable instance instAlgRatFuncGeom_gen :
    Algebra (RatFunc k₀) (FractionRing (Polynomial (AlgebraicClosure k₀))) :=
  (IsFractionRing.lift (A := k₀[X]) toClosureFrac_gen_injective).toAlgebra

/-- The structure map `k₀(T) → k₀‾(T)` restricted to `k₀[T]` is exactly `toClosureFrac_gen`. -/
theorem algebraMap_ratFunc_geom_comp_gen (x : k₀[X]) :
    algebraMap (RatFunc k₀) (FractionRing (Polynomial (AlgebraicClosure k₀)))
        (algebraMap k₀[X] (RatFunc k₀) x) = toClosureFrac_gen x := by
  show IsFractionRing.lift (A := k₀[X]) toClosureFrac_gen_injective _ = _
  rw [IsFractionRing.lift_algebraMap]

/-- `k₀[T] → k₀(T) → k₀‾(T)` is a scalar tower. -/
instance instTowerRatFuncGeom_gen :
    IsScalarTower k₀[X] (RatFunc k₀) (FractionRing (Polynomial (AlgebraicClosure k₀))) := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  rw [algebraMap_ratFunc_geom_comp_gen,
    IsScalarTower.algebraMap_apply k₀[X] (Polynomial (AlgebraicClosure k₀))
      (FractionRing (Polynomial (AlgebraicClosure k₀)))]
  rfl

/-- `k₀ → k₀(T) → k₀‾(T)` is a scalar tower.  This is the honest replacement for the `ℚ`-proof's
`Subsingleton.elim` compatibility: the ambient `Algebra k₀ (FractionRing k₀‾[X])` runs
`k₀ → k₀‾[X] → FractionRing`, and this tower says it agrees with going through `RatFunc k₀`.  Both
sides reduce, on `x : k₀`, to `algebraMap k₀‾[X] geom (C (algebraMap k₀ k₀‾ x))`. -/
instance instTowerBaseRatFuncGeom_gen :
    IsScalarTower k₀ (RatFunc k₀) (FractionRing (Polynomial (AlgebraicClosure k₀))) := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  -- RHS: go k₀ → k₀[X] → RatFunc k₀ → geom, using `algebraMap_ratFunc_geom_comp_gen`.
  rw [IsScalarTower.algebraMap_apply k₀ k₀[X] (RatFunc k₀), algebraMap_ratFunc_geom_comp_gen,
    toClosureFrac_gen, RingHom.comp_apply]
  -- LHS: go k₀ → k₀‾[X] → geom (the ambient localisation algebra).
  rw [IsScalarTower.algebraMap_apply k₀ (Polynomial (AlgebraicClosure k₀))
      (FractionRing (Polynomial (AlgebraicClosure k₀)))]
  -- Both sides are `algebraMap k₀‾[X] geom` applied to the same polynomial.
  congr 1
  rw [Polynomial.coe_mapRingHom, IsScalarTower.algebraMap_apply k₀ (AlgebraicClosure k₀)
    (Polynomial (AlgebraicClosure k₀)), Polynomial.algebraMap_eq, Polynomial.algebraMap_eq,
    Polynomial.map_C]

/-- `k₀‾(T)` is algebraic over `k₀(T)`. -/
theorem isAlgebraic_ratFunc_geom_gen :
    Algebra.IsAlgebraic (RatFunc k₀)
      (FractionRing (Polynomial (AlgebraicClosure k₀))) :=
  isAlgebraic_of_isFractionRing (R := k₀[X]) (S := Polynomial (AlgebraicClosure k₀))
    (RatFunc k₀) (FractionRing (Polynomial (AlgebraicClosure k₀)))

/-- `k₀` is relatively algebraically closed in `k₀(T)` (port of `regular_ratFunc`).  Field-agnostic:
`k₀[T]` is integrally closed in `k₀(T)`, and an element integral over `k₀` has degree-`0` preimage
in `k₀[T]` by `natDegree_comp`. -/
theorem regular_ratFunc_gen : algebraicClosure k₀ (RatFunc k₀) = ⊥ := by
  refine bot_unique fun x hx => ?_
  rw [mem_algebraicClosure_iff'] at hx
  have hxT : IsIntegral (Polynomial k₀) x := hx.tower_top
  obtain ⟨p, hp⟩ := (IsIntegrallyClosed.isIntegral_iff (R := Polynomial k₀)
    (x := x)).mp hxT
  let φ : Polynomial k₀ →ₐ[k₀] RatFunc k₀ := IsScalarTower.toAlgHom k₀ (Polynomial k₀) (RatFunc k₀)
  have hφinj : Function.Injective φ := by
    show Function.Injective (algebraMap (Polynomial k₀) (RatFunc k₀))
    exact IsFractionRing.injective _ _
  have hpint : IsIntegral k₀ p := by
    have hh : IsIntegral k₀ (φ p) := (show φ p = x from hp) ▸ hx
    exact (isIntegral_algHom_iff φ hφinj).mp hh
  have key : Polynomial.aeval p (minpoly k₀ p) = (minpoly k₀ p).comp p := by
    rw [Polynomial.aeval_def]; rfl
  have hcomp : (minpoly k₀ p).comp p = 0 := key.symm.trans (minpoly.aeval k₀ p)
  have hdeg : (minpoly k₀ p).natDegree * p.natDegree = 0 := by
    have h := Polynomial.natDegree_comp (p := minpoly k₀ p) (q := p)
    rw [hcomp, Polynomial.natDegree_zero] at h
    exact h.symm
  have hqpos : 0 < (minpoly k₀ p).natDegree := minpoly.natDegree_pos hpint
  have hp0 : p.natDegree = 0 := by
    rcases Nat.mul_eq_zero.mp hdeg with h | h
    · omega
    · exact h
  obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hp0
  rw [IntermediateField.mem_bot]
  refine ⟨c, ?_⟩
  rw [← hp, ← hc, Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]

/-- The image of the variable `X` under `k₀‾[T] → k₀‾(T)` lies in `k₀(T)`. -/
theorem geomVar_mem_gen (T : Set (FractionRing (Polynomial (AlgebraicClosure k₀)))) :
    algebraMap (Polynomial (AlgebraicClosure k₀))
        (FractionRing (Polynomial (AlgebraicClosure k₀))) X ∈
      IntermediateField.adjoin (RatFunc k₀) T := by
  have hτ : algebraMap (Polynomial (AlgebraicClosure k₀))
        (FractionRing (Polynomial (AlgebraicClosure k₀))) X
      = algebraMap (RatFunc k₀) (FractionRing (Polynomial (AlgebraicClosure k₀)))
          (algebraMap k₀[X] (RatFunc k₀) X) := by
    rw [algebraMap_ratFunc_geom_comp_gen]
    show _ = toClosureFrac_gen X
    rw [toClosureFrac_gen, RingHom.comp_apply]
    simp [Polynomial.coe_mapRingHom]
  rw [hτ]
  exact IntermediateField.algebraMap_mem _ _

/-- The image in `k₀‾(T)` of any `q ∈ k₀‾[T]` lies in `k₀(T)` adjoined with the (images of the)
coefficients of `q`. -/
theorem geomPoly_mem_gen (q : Polynomial (AlgebraicClosure k₀)) :
    ∃ S : Finset (AlgebraicClosure k₀),
      algebraMap (Polynomial (AlgebraicClosure k₀))
          (FractionRing (Polynomial (AlgebraicClosure k₀))) q ∈
        IntermediateField.adjoin (RatFunc k₀)
          ((algebraMap (AlgebraicClosure k₀) (FractionRing (Polynomial (AlgebraicClosure k₀))))
            '' (↑S : Set (AlgebraicClosure k₀))) := by
  classical
  induction q using Polynomial.induction_on' with
  | add p r hp hr =>
    obtain ⟨S1, hS1⟩ := hp
    obtain ⟨S2, hS2⟩ := hr
    refine ⟨S1 ∪ S2, ?_⟩
    rw [map_add]
    have hmono : ∀ (S' : Finset (AlgebraicClosure k₀)), S' ⊆ S1 ∪ S2 →
        IntermediateField.adjoin (RatFunc k₀)
            ((algebraMap (AlgebraicClosure k₀) (FractionRing (Polynomial (AlgebraicClosure k₀))))
              '' (↑S' : Set (AlgebraicClosure k₀)))
          ≤ IntermediateField.adjoin (RatFunc k₀)
            ((algebraMap (AlgebraicClosure k₀) (FractionRing (Polynomial (AlgebraicClosure k₀))))
              '' (↑(S1 ∪ S2) : Set (AlgebraicClosure k₀))) :=
      fun S' hsub => IntermediateField.adjoin.mono _ _ _
        (Set.image_mono (by exact_mod_cast hsub))
    exact add_mem (hmono S1 Finset.subset_union_left hS1)
      (hmono S2 Finset.subset_union_right hS2)
  | monomial n a =>
    refine ⟨{a}, ?_⟩
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
    have hCa : algebraMap (Polynomial (AlgebraicClosure k₀))
          (FractionRing (Polynomial (AlgebraicClosure k₀))) (C a)
        = algebraMap (AlgebraicClosure k₀)
            (FractionRing (Polynomial (AlgebraicClosure k₀))) a := by
      rw [Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
    rw [hCa]
    apply mul_mem
    · apply IntermediateField.subset_adjoin
      exact ⟨a, by simp, rfl⟩
    · exact pow_mem (geomVar_mem_gen _) n

/-- Every element of `k₀‾(T)` lies in `k₀(T)` adjoined with a finite set of constants. -/
theorem geomElt_mem_gen (k : FractionRing (Polynomial (AlgebraicClosure k₀))) :
    ∃ S : Finset (AlgebraicClosure k₀),
      k ∈ IntermediateField.adjoin (RatFunc k₀)
        ((algebraMap (AlgebraicClosure k₀) (FractionRing (Polynomial (AlgebraicClosure k₀))))
          '' (↑S : Set (AlgebraicClosure k₀))) := by
  classical
  obtain ⟨num, den, hden, hk⟩ :=
    IsFractionRing.div_surjective (A := Polynomial (AlgebraicClosure k₀)) k
  obtain ⟨S1, hS1⟩ := geomPoly_mem_gen num
  obtain ⟨S2, hS2⟩ := geomPoly_mem_gen den
  refine ⟨S1 ∪ S2, ?_⟩
  have hmono : ∀ (S' : Finset (AlgebraicClosure k₀)), S' ⊆ S1 ∪ S2 →
      IntermediateField.adjoin (RatFunc k₀)
          ((algebraMap (AlgebraicClosure k₀) (FractionRing (Polynomial (AlgebraicClosure k₀))))
            '' (↑S' : Set (AlgebraicClosure k₀)))
        ≤ IntermediateField.adjoin (RatFunc k₀)
          ((algebraMap (AlgebraicClosure k₀) (FractionRing (Polynomial (AlgebraicClosure k₀))))
            '' (↑(S1 ∪ S2) : Set (AlgebraicClosure k₀))) :=
    fun S' hsub => IntermediateField.adjoin.mono _ _ _
      (Set.image_mono (by exact_mod_cast hsub))
  rw [← hk]
  exact div_mem (hmono S1 Finset.subset_union_left hS1)
    (hmono S2 Finset.subset_union_right hS2)

/-- Primitive element: a finite set of elements of `k₀‾` is contained in `k₀⟮γ⟯` for a single
`γ ∈ k₀‾` (finite separable extension of `k₀`; separability from `CharZero k₀`). -/
theorem geomPrim_gen [CharZero k₀] (S : Finset (AlgebraicClosure k₀)) :
    ∃ γ : AlgebraicClosure k₀, ∀ s ∈ S,
      s ∈ IntermediateField.adjoin k₀ ({γ} : Set (AlgebraicClosure k₀)) := by
  classical
  set M := IntermediateField.adjoin k₀ (↑S : Set (AlgebraicClosure k₀)) with hM
  haveI : FiniteDimensional k₀ M := IntermediateField.finiteDimensional_adjoin
    (fun s _ => (Algebra.IsAlgebraic.isAlgebraic s).isIntegral)
  obtain ⟨γ', hγ'⟩ := Field.exists_primitive_element k₀ M
  refine ⟨(γ' : AlgebraicClosure k₀), fun s hs => ?_⟩
  have hsM : s ∈ M := IntermediateField.subset_adjoin k₀ _ (by exact_mod_cast hs)
  have hmap : M =
      IntermediateField.adjoin k₀ ({(γ' : AlgebraicClosure k₀)} : Set (AlgebraicClosure k₀)) := by
    have hcong := congrArg (fun N => IntermediateField.map (M.val) N) hγ'
    simp only at hcong
    rw [IntermediateField.adjoin_map, Set.image_singleton] at hcong
    have h2 : IntermediateField.map M.val ⊤ = M := by
      rw [← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val]
    rw [h2] at hcong
    exact hcong.symm
  rw [hmap] at hsM
  exact hsM

/-- **Constant extraction** (port of `extract`).  Every finite family of elements of `k₀‾(T)` sits
inside a single constant-adjoin `k₀(T)⟮γ⟯`, `γ ∈ k₀‾`. -/
theorem extract_gen [CharZero k₀]
    (t : Finset (FractionRing (Polynomial (AlgebraicClosure k₀)))) :
    ∃ γ : AlgebraicClosure k₀, ∀ k ∈ t, k ∈ IntermediateField.adjoin (RatFunc k₀)
      {algebraMap (AlgebraicClosure k₀) (FractionRing (Polynomial (AlgebraicClosure k₀))) γ} := by
  classical
  choose Sf hSf using geomElt_mem_gen (k₀ := k₀)
  let Stot : Finset (AlgebraicClosure k₀) := t.biUnion Sf
  obtain ⟨γ, hγ⟩ := geomPrim_gen Stot
  refine ⟨γ, fun k hk => ?_⟩
  have hkmem := hSf k
  set ι := algebraMap (AlgebraicClosure k₀) (FractionRing (Polynomial (AlgebraicClosure k₀)))
    with hι
  let ιₐ : AlgebraicClosure k₀ →ₐ[k₀] FractionRing (Polynomial (AlgebraicClosure k₀)) :=
    IsScalarTower.toAlgHom k₀ (AlgebraicClosure k₀)
      (FractionRing (Polynomial (AlgebraicClosure k₀)))
  have hιₐ : ⇑ιₐ = ι := IsScalarTower.coe_toAlgHom' k₀ (AlgebraicClosure k₀)
    (FractionRing (Polynomial (AlgebraicClosure k₀)))
  have hcoeff_mem : ∀ s ∈ Stot, ι s ∈ IntermediateField.adjoin (RatFunc k₀) {ι γ} := by
    intro s hs
    have hsγ : s ∈ IntermediateField.adjoin k₀ ({γ} : Set (AlgebraicClosure k₀)) := hγ s hs
    have hmapped : ι s ∈ (IntermediateField.adjoin k₀ ({γ} : Set (AlgebraicClosure k₀))).map ιₐ := by
      have himg : ιₐ s ∈ ((IntermediateField.adjoin k₀ ({γ} : Set (AlgebraicClosure k₀))).map ιₐ :
          Set (FractionRing (Polynomial (AlgebraicClosure k₀)))) := by
        rw [IntermediateField.coe_map]
        exact Set.mem_image_of_mem ιₐ hsγ
      rw [hιₐ] at himg
      exact himg
    rw [IntermediateField.adjoin_map, Set.image_singleton, hιₐ] at hmapped
    have hle : IntermediateField.adjoin k₀ ({ι γ} :
          Set (FractionRing (Polynomial (AlgebraicClosure k₀))))
        ≤ (IntermediateField.adjoin (RatFunc k₀) ({ι γ} :
            Set (FractionRing (Polynomial (AlgebraicClosure k₀))))).restrictScalars k₀ := by
      rw [IntermediateField.adjoin_le_iff]
      intro y hy
      simp only [Set.mem_singleton_iff] at hy
      subst hy
      exact IntermediateField.subset_adjoin (RatFunc k₀) {ι γ} (Set.mem_singleton _)
    exact hle hmapped
  have hsub : IntermediateField.adjoin (RatFunc k₀)
        (ι '' (↑Stot : Set (AlgebraicClosure k₀)))
      ≤ IntermediateField.adjoin (RatFunc k₀) {ι γ} := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨s, hsStot, rfl⟩
    exact hcoeff_mem s hsStot
  have hsubk : IntermediateField.adjoin (RatFunc k₀)
        (ι '' (↑(Sf k) : Set (AlgebraicClosure k₀)))
      ≤ IntermediateField.adjoin (RatFunc k₀) (ι '' (↑Stot : Set (AlgebraicClosure k₀))) :=
    IntermediateField.adjoin.mono _ _ _
      (Set.image_mono (by
        intro x hx
        exact Finset.mem_biUnion.mpr ⟨k, hk, hx⟩))
  exact hsub (hsubk hkmem)

/-- **The regularity core, general base field** (port of `isField_baseChange_of_regular`).  For a
finite extension `L / k₀(T)` in which `k₀` is relatively algebraically closed
(`algebraicClosure k₀ L = ⊥`, "regular"), the base change of `L` to the geometric base field
`k₀‾(T) = FractionRing k₀‾[T]` is a **field**. -/
theorem isField_baseChange_of_regular_gen [CharZero k₀]
    {L : Type*} [Field L] [Algebra (RatFunc k₀) L] [FiniteDimensional (RatFunc k₀) L]
    [Algebra k₀ L] [IsScalarTower k₀ (RatFunc k₀) L]
    (hreg : algebraicClosure k₀ L = ⊥) :
    IsField (FractionRing (Polynomial (AlgebraicClosure k₀)) ⊗[RatFunc k₀] L) := by
  classical
  haveI algL : Algebra.IsAlgebraic (RatFunc k₀) L := Algebra.IsAlgebraic.of_finite _ _
  haveI algK : Algebra.IsAlgebraic (RatFunc k₀)
      (FractionRing (Polynomial (AlgebraicClosure k₀))) := isAlgebraic_ratFunc_geom_gen
  let S := AlgebraicClosure (RatFunc k₀)
  let fa : FractionRing (Polynomial (AlgebraicClosure k₀)) →ₐ[RatFunc k₀] S := IsAlgClosed.lift
  let fb : L →ₐ[RatFunc k₀] S := IsAlgClosed.lift
  have hfa : Function.Injective fa := fa.toRingHom.injective
  have hfb : Function.Injective fb := fb.toRingHom.injective
  have hFreg : algebraicClosure k₀ (RatFunc k₀) = ⊥ := regular_ratFunc_gen
  haveI hSint : Algebra.IsIntegral (RatFunc k₀) S := Algebra.IsAlgebraic.isIntegral
  haveI : Algebra.IsIntegral (RatFunc k₀) ↥fa.range := ⟨fun y =>
    (isIntegral_algHom_iff fa.range.val Subtype.val_injective).mp
      (Algebra.IsIntegral.isIntegral (y : S))⟩
  have hLD : fa.range.LinearDisjoint fb.range := by
    refine Subalgebra.LinearDisjoint.of_linearDisjoint_finite_left fa.range fb.range ?_
    intro A' hA' hFin
    haveI := hFin
    obtain ⟨g, hgspan⟩ := Module.finite_def.mp hFin
    have hmemrange : ∀ a : ↥A', (a : S) ∈ fa.range := fun a => hA' a.2
    choose φ hφ using fun a : ↥A' => (fa.mem_range).mp (hmemrange a)
    obtain ⟨γ, hγ⟩ := extract_gen (g.image φ)
    set c : S := fa (algebraMap (AlgebraicClosure k₀)
      (FractionRing (Polynomial (AlgebraicClosure k₀))) γ) with hcdef
    set C : IntermediateField (RatFunc k₀) S := IntermediateField.adjoin (RatFunc k₀) {c} with hCdef
    have hgen : ∀ i ∈ g, (fa (φ i)) ∈ C := by
      intro i hi
      have hmem : φ i ∈ IntermediateField.adjoin (RatFunc k₀)
          {algebraMap (AlgebraicClosure k₀)
            (FractionRing (Polynomial (AlgebraicClosure k₀))) γ} :=
        hγ (φ i) (Finset.mem_image_of_mem φ hi)
      have h2 : fa (φ i) ∈ (IntermediateField.adjoin (RatFunc k₀)
          {algebraMap (AlgebraicClosure k₀)
            (FractionRing (Polynomial (AlgebraicClosure k₀))) γ}).map fa := by
        have himg : fa (φ i) ∈ (fa '' (IntermediateField.adjoin (RatFunc k₀)
            {algebraMap (AlgebraicClosure k₀)
              (FractionRing (Polynomial (AlgebraicClosure k₀))) γ} : Set _)) :=
          Set.mem_image_of_mem fa hmem
        rwa [← IntermediateField.coe_map] at himg
      rw [IntermediateField.adjoin_map, Set.image_singleton] at h2
      exact h2
    have hAC : A' ≤ C.toSubalgebra := by
      intro x hx
      rw [IntermediateField.mem_toSubalgebra]
      have h1 : (⟨x, hx⟩ : ↥A') ∈ Submodule.span (RatFunc k₀) (g : Set ↥A') := by
        rw [hgspan]; exact Submodule.mem_top
      have h2 : x ∈ (Submodule.span (RatFunc k₀) (g : Set ↥A')).map A'.val.toLinearMap :=
        Submodule.mem_map_of_mem h1
      rw [Submodule.map_span] at h2
      have hsub : (A'.val.toLinearMap '' (g : Set ↥A')) ⊆ (C.toSubmodule : Set S) := by
        rintro _ ⟨i, hi, rfl⟩
        show (i : S) ∈ C
        rw [← hφ i]
        exact hgen i hi
      exact (Submodule.span_le.mpr hsub) h2
    have hγint : IsIntegral k₀ γ := Algebra.IsIntegral.isIntegral γ
    have hcF : IsIntegral (RatFunc k₀) c := Algebra.IsIntegral.isIntegral c
    haveI hCfin : FiniteDimensional (RatFunc k₀) ↥C :=
      IntermediateField.adjoin.finiteDimensional hcF
    have hminF : minpoly (RatFunc k₀) c
        = (minpoly k₀ γ).map (algebraMap k₀ (RatFunc k₀)) := by
      have hcomp1 : (algebraMap (RatFunc k₀)
            (FractionRing (Polynomial (AlgebraicClosure k₀)))).comp
          (algebraMap k₀ (RatFunc k₀))
          = algebraMap k₀ (FractionRing (Polynomial (AlgebraicClosure k₀))) :=
        (IsScalarTower.algebraMap_eq k₀ (RatFunc k₀)
          (FractionRing (Polynomial (AlgebraicClosure k₀)))).symm
      rw [hcdef, minpoly.algHom_eq fa hfa]
      set cK : FractionRing (Polynomial (AlgebraicClosure k₀)) :=
        algebraMap (AlgebraicClosure k₀) (FractionRing (Polynomial (AlgebraicClosure k₀))) γ
        with hcKdef
      have hqmonic : ((minpoly k₀ γ).map (algebraMap k₀ (RatFunc k₀))).Monic :=
        (minpoly.monic hγint).map _
      have hqirr : Irreducible ((minpoly k₀ γ).map (algebraMap k₀ (RatFunc k₀))) :=
        Rigidity.RET.irreducible_map_of_algClosure_eq_bot hFreg (minpoly.monic hγint)
          (minpoly.irreducible hγint)
      have hqeval : (Polynomial.aeval cK)
          ((minpoly k₀ γ).map (algebraMap k₀ (RatFunc k₀))) = 0 := by
        rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp1, ← Polynomial.aeval_def, hcKdef,
          Polynomial.aeval_algebraMap_apply, minpoly.aeval, map_zero]
      exact (minpoly.eq_of_irreducible_of_monic hqirr hqeval hqmonic).symm
    let γ' := IntermediateField.AdjoinSimple.gen (RatFunc k₀) c
    have hγ'top : IntermediateField.adjoin (RatFunc k₀) {γ'} = ⊤ := by
      apply IntermediateField.adjoin_eq_top_of_algebra
      exact (IntermediateField.adjoin.powerBasis hcF).adjoin_gen_eq_top
    have hirr : Irreducible ((minpoly (RatFunc k₀) γ').map (algebraMap (RatFunc k₀) L)) := by
      rw [IntermediateField.minpoly_gen, hminF, Polynomial.map_map,
        ← IsScalarTower.algebraMap_eq k₀ (RatFunc k₀) L]
      exact Rigidity.RET.irreducible_map_of_algClosure_eq_bot hreg (minpoly.monic hγint)
        (minpoly.irreducible hγint)
    have hfieldLC : IsField (L ⊗[RatFunc k₀] ↥C) :=
      Rigidity.RET.isField_tensor_of_primitive_irreducible (K := L) (↥C) γ' hγ'top hirr
    have hfieldCL : IsField (↥C ⊗[RatFunc k₀] L) :=
      (Algebra.TensorProduct.comm (RatFunc k₀) (↥C) L).toMulEquiv.isField hfieldLC
    have hLDC : C.toSubalgebra.LinearDisjoint fb.range := by
      have h := Subalgebra.LinearDisjoint.of_isField' hfieldCL C.val fb C.val.injective hfb
      rwa [IntermediateField.range_val] at h
    exact hLDC.of_le_left_of_flat hAC
  haveI : IsDomain (FractionRing (Polynomial (AlgebraicClosure k₀)) ⊗[RatFunc k₀] L) :=
    Subalgebra.LinearDisjoint.isDomain_of_injective hfa hfb hLD
  exact Algebra.TensorProduct.isField_of_isAlgebraic (RatFunc k₀)
    (FractionRing (Polynomial (AlgebraicClosure k₀))) L (Or.inr algL)

end

end Rigidity.RET.Descent

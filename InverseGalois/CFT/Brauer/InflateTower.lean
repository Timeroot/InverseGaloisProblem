/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.H2Brauer
import InverseGalois.CFT.Brauer.SmoothLevel
import InverseGalois.CFT.Compositum

/-!
# The Brauer class of a smooth two cohomology class

Let `K / k` be a Galois extension, possibly of infinite degree.  Every class of the second
cohomology of `Gal(K/k)` with coefficients in `Kˣ`, computed by smooth cochains, is inflated from
a two cocycle of a finite Galois intermediate field, and the crossed product of such a cocycle has
a class in the Brauer group of `k`.  This file shows that the resulting Brauer class does not
depend on the level chosen, and assembles the construction into a homomorphism from the smooth
second cohomology to the Brauer group of the base.

The comparison of two levels is made at their compositum, which is again a finite Galois level.
Inflating a cocycle twice along a tower of levels is the same as inflating it once to the top, and
inflation to a larger finite level leaves the Brauer class unchanged, so both levels contribute a
cocycle of the compositum with the same inflation to the whole extension and with the original
Brauer class.  Two cocycles of the compositum whose inflations are cohomologous are cohomologous
already at the compositum, because inflation from a finite Galois level is injective, and
cohomologous cocycles have crossed products of the same Brauer class.

The homomorphism obtained this way is injective: a cocycle of a level whose crossed product splits
is a coboundary at that level, and the coboundary of an inflated cochain inflates to the
coboundary of a smooth cochain.

## Main results

* `InverseGalois.CFT.inflateCocycle_trans`: **inflating twice along a tower of normal subfields is
  inflating once to the top.**
* `InverseGalois.CFT.exists_cocycle_of_le`: **a cocycle of a finite Galois level is inflated from
  a cocycle of any larger finite Galois level with the same Brauer class.**
* `InverseGalois.CFT.mk_csa_eq_mk_csa_of_smoothH2Mk_eq`: **two cocycles of finite Galois levels
  with the same smooth cohomology class have crossed products of the same Brauer class.**
* `InverseGalois.CFT.smoothBrauer`, `InverseGalois.CFT.smoothBrauerHom`: **the Brauer class of a
  smooth two cohomology class**, and the homomorphism it defines.
* `InverseGalois.CFT.smoothBrauerHom_injective`: **the homomorphism is injective.**

## Tags

Brauer group, crossed product, Galois cohomology, inflation, infinite Galois theory
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

universe u

namespace InverseGalois.CFT

open groupCohomology

/-! ### Inflation along a tower -/

section Tower

variable {k L L' K : Type u} [Field k] [Field L] [Field L'] [Field K]
  [Algebra k L] [Algebra k L'] [Algebra k K] [Algebra L L'] [Algebra L K] [Algebra L' K]
  [IsScalarTower k L L'] [IsScalarTower k L K] [IsScalarTower k L' K] [IsScalarTower L L' K]
  [Normal k L] [Normal k L']

/-- Restricting an automorphism to a normal subfield and then to a normal subfield of that is
restricting it to the smaller field. -/
theorem restrictNormal_restrictNormal (σ : Gal(K/k)) :
    (σ.restrictNormal L' : L' ≃ₐ[k] L').restrictNormal L = σ.restrictNormal L :=
  (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply L L' σ).symm

/-- **Inflating twice along a tower of normal subfields is inflating once to the top.** -/
theorem inflateCocycle_trans (w : Gal(L/k) × Gal(L/k) → Lˣ) :
    inflateCocycle (L := L') K (inflateCocycle (L := L) L' w) = inflateCocycle (L := L) K w := by
  refine funext fun p => Units.ext ?_
  obtain ⟨σ, τ⟩ := p
  rw [inflateCocycle_apply, inflateCocycle_apply, inflateCocycle_apply,
    restrictNormal_restrictNormal, restrictNormal_restrictNormal,
    ← IsScalarTower.algebraMap_apply]

end Tower

/-! ### The compositum of two levels -/

section Sup

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]

omit [IsGalois k K] in
/-- **A cocycle of a finite Galois level is inflated from a cocycle of any larger finite Galois
level with the same Brauer class.** -/
theorem exists_cocycle_of_le {E F : IntermediateField k K} (hEF : E ≤ F)
    [FiniteDimensional k E] [IsGalois k E] [FiniteDimensional k F] [IsGalois k F]
    {w : Gal(↥E/k) × Gal(↥E/k) → (↥E)ˣ} (hw : IsMulCocycle₂ w) :
    ∃ (v : Gal(↥F/k) × Gal(↥F/k) → (↥F)ˣ) (hv : IsMulCocycle₂ v),
      inflateCocycle (L := ↥F) K v = inflateCocycle (L := ↥E) K w ∧
        (⟦CrossedProduct.csa hv⟧ : BrauerGroup k) = ⟦CrossedProduct.csa hw⟧ := by
  letI : Algebra ↥E ↥F := ((IntermediateField.inclusion hEF).toRingHom).toAlgebra
  haveI : IsScalarTower k ↥E ↥F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ↥E ↥F K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ⟨inflateCocycle (L := ↥E) ↥F w, isMulCocycle₂_inflateCocycle hw, inflateCocycle_trans w,
    CrossedProduct.mk_csa_inflateCocycle hw⟩

end Sup

/-! ### The Brauer class attached to a smooth class -/

section Class

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]

/-- **Two cocycles of finite Galois levels with the same smooth cohomology class have crossed
products of the same Brauer class.** -/
theorem mk_csa_eq_mk_csa_of_smoothH2Mk_eq {E₁ E₂ : IntermediateField k K}
    [FiniteDimensional k E₁] [IsGalois k E₁] [FiniteDimensional k E₂] [IsGalois k E₂]
    {w₁ : Gal(↥E₁/k) × Gal(↥E₁/k) → (↥E₁)ˣ} (hw₁ : IsMulCocycle₂ w₁)
    {w₂ : Gal(↥E₂/k) × Gal(↥E₂/k) → (↥E₂)ˣ} (hw₂ : IsMulCocycle₂ w₂)
    (h : smoothH2Mk (inflateCocycle (L := ↥E₁) K w₁) (isMulCocycle₂_inflateCocycle hw₁)
          (isSmooth₂_inflateCocycle E₁ w₁)
        = smoothH2Mk (inflateCocycle (L := ↥E₂) K w₂) (isMulCocycle₂_inflateCocycle hw₂)
          (isSmooth₂_inflateCocycle E₂ w₂)) :
    (⟦CrossedProduct.csa hw₁⟧ : BrauerGroup k) = ⟦CrossedProduct.csa hw₂⟧ := by
  haveI := isGalois_sup E₁ E₂
  obtain ⟨v₁, hv₁, hi₁, hb₁⟩ := exists_cocycle_of_le (le_sup_left : E₁ ≤ E₁ ⊔ E₂) hw₁
  obtain ⟨v₂, hv₂, hi₂, hb₂⟩ := exists_cocycle_of_le (le_sup_right : E₂ ≤ E₁ ⊔ E₂) hw₂
  obtain ⟨u, hus, hu⟩ := (smoothH2Mk_eq_iff _ _ _ _).1 h
  have hd : inflateCocycle (L := ↥(E₁ ⊔ E₂)) K (fun p => v₁ p / v₂ p)
      = fun q => inflateCocycle (L := ↥E₁) K w₁ q / inflateCocycle (L := ↥E₂) K w₂ q := by
    rw [← hi₁, ← hi₂]
    exact funext fun _ =>
      map_div (Units.map (algebraMap ↥(E₁ ⊔ E₂) K : ↥(E₁ ⊔ E₂) →* K)) _ _
  rw [← hb₁, ← hb₂, CrossedProduct.mk_csa_eq_mk_csa_iff hv₁ hv₂]
  refine isMulCoboundary₂_of_coboundary₂_inflateCocycle (E₁ ⊔ E₂) hus ?_
  rw [hd]
  exact hu

/-- **The Brauer class attached to a smooth two cohomology class is well defined**: there is
exactly one class of the Brauer group of the base which is the class of the crossed product of
every cocycle of a finite Galois level inflating to the given cohomology class. -/
theorem existsUnique_mk_csa (z : SmoothH2 Gal(K/k) Kˣ) :
    ∃! b : BrauerGroup k, ∀ (E : IntermediateField k K) [FiniteDimensional k E] [IsGalois k E]
      (w : Gal(↥E/k) × Gal(↥E/k) → (↥E)ˣ) (hw : IsMulCocycle₂ w),
      smoothH2Mk (inflateCocycle (L := ↥E) K w) (isMulCocycle₂_inflateCocycle hw)
          (isSmooth₂_inflateCocycle E w) = z →
        (⟦CrossedProduct.csa hw⟧ : BrauerGroup k) = b := by
  obtain ⟨E₀, hfd₀, hg₀, w₀, hw₀, hz₀⟩ := exists_isGalois_levelCocycle₂ z
  haveI := hfd₀
  haveI := hg₀
  refine ⟨⟦CrossedProduct.csa hw₀⟧, fun E _ _ w hw hz => ?_, fun b hb => ?_⟩
  · exact mk_csa_eq_mk_csa_of_smoothH2Mk_eq hw hw₀ (hz.trans hz₀.symm)
  · exact (hb E₀ w₀ hw₀ hz₀).symm

/-- **The Brauer class of a smooth two cohomology class.** -/
noncomputable def smoothBrauer (z : SmoothH2 Gal(K/k) Kˣ) : BrauerGroup k :=
  (existsUnique_mk_csa z).choose

/-- **The Brauer class of a smooth two cohomology class is computed at any finite Galois level the
class is inflated from.** -/
theorem mk_csa_eq_smoothBrauer {z : SmoothH2 Gal(K/k) Kˣ} (E : IntermediateField k K)
    [FiniteDimensional k E] [IsGalois k E] {w : Gal(↥E/k) × Gal(↥E/k) → (↥E)ˣ}
    (hw : IsMulCocycle₂ w)
    (hz : smoothH2Mk (inflateCocycle (L := ↥E) K w) (isMulCocycle₂_inflateCocycle hw)
      (isSmooth₂_inflateCocycle E w) = z) :
    (⟦CrossedProduct.csa hw⟧ : BrauerGroup k) = smoothBrauer z :=
  (existsUnique_mk_csa z).choose_spec.1 E w hw hz

/-- **The Brauer class of a product of smooth two cohomology classes is the product of the
classes**, both being computed at the compositum of levels for the two factors. -/
theorem smoothBrauer_mul (z₁ z₂ : SmoothH2 Gal(K/k) Kˣ) :
    smoothBrauer (z₁ * z₂) = smoothBrauer z₁ * smoothBrauer z₂ := by
  obtain ⟨E₁, hfd₁, hg₁, w₁, hw₁, hz₁⟩ := exists_isGalois_levelCocycle₂ z₁
  obtain ⟨E₂, hfd₂, hg₂, w₂, hw₂, hz₂⟩ := exists_isGalois_levelCocycle₂ z₂
  haveI := hfd₁
  haveI := hg₁
  haveI := hfd₂
  haveI := hg₂
  haveI := isGalois_sup E₁ E₂
  obtain ⟨v₁, hv₁, hi₁, hb₁⟩ := exists_cocycle_of_le (le_sup_left : E₁ ≤ E₁ ⊔ E₂) hw₁
  obtain ⟨v₂, hv₂, hi₂, hb₂⟩ := exists_cocycle_of_le (le_sup_right : E₂ ≤ E₁ ⊔ E₂) hw₂
  have hm : inflateCocycle (L := ↥(E₁ ⊔ E₂)) K (fun p => v₁ p * v₂ p)
      = inflateCocycle (L := ↥(E₁ ⊔ E₂)) K v₁ * inflateCocycle (L := ↥(E₁ ⊔ E₂)) K v₂ :=
    funext fun _ => map_mul (Units.map (algebraMap ↥(E₁ ⊔ E₂) K : ↥(E₁ ⊔ E₂) →* K)) _ _
  have h1 := (smoothH2Mk_congr (isMulCocycle₂_inflateCocycle hv₁)
    (isSmooth₂_inflateCocycle (E₁ ⊔ E₂) v₁) (isMulCocycle₂_inflateCocycle hw₁)
    (isSmooth₂_inflateCocycle E₁ w₁) hi₁).trans hz₁
  have h2 := (smoothH2Mk_congr (isMulCocycle₂_inflateCocycle hv₂)
    (isSmooth₂_inflateCocycle (E₁ ⊔ E₂) v₂) (isMulCocycle₂_inflateCocycle hw₂)
    (isSmooth₂_inflateCocycle E₂ w₂) hi₂).trans hz₂
  have hz : smoothH2Mk (inflateCocycle (L := ↥(E₁ ⊔ E₂)) K (fun p => v₁ p * v₂ p))
      (isMulCocycle₂_inflateCocycle (isMulCocycle₂_mul hv₁ hv₂))
      (isSmooth₂_inflateCocycle (E₁ ⊔ E₂) _) = z₁ * z₂ := by
    rw [smoothH2Mk_eq_mul (isMulCocycle₂_inflateCocycle hv₁)
      (isSmooth₂_inflateCocycle (E₁ ⊔ E₂) v₁) (isMulCocycle₂_inflateCocycle hv₂)
      (isSmooth₂_inflateCocycle (E₁ ⊔ E₂) v₂) _ _ hm, h1, h2]
  rw [← mk_csa_eq_smoothBrauer (E₁ ⊔ E₂) (isMulCocycle₂_mul hv₁ hv₂) hz,
    CrossedProduct.mk_csa_mul hv₁ hv₂, hb₁, hb₂, mk_csa_eq_smoothBrauer E₁ hw₁ hz₁,
    mk_csa_eq_smoothBrauer E₂ hw₂ hz₂]

/-- **The Brauer class of a smooth two cohomology class, as a homomorphism** from the second
cohomology of the Galois group with coefficients in the units of the extension to the Brauer group
of the base. -/
noncomputable def smoothBrauerHom : SmoothH2 Gal(K/k) Kˣ →* BrauerGroup k :=
  MonoidHom.mk' smoothBrauer smoothBrauer_mul

@[simp]
theorem smoothBrauerHom_apply (z : SmoothH2 Gal(K/k) Kˣ) :
    smoothBrauerHom z = smoothBrauer z := rfl

end Class

/-! ### Injectivity -/

section Injective

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
  (E : IntermediateField k K) [FiniteDimensional k E] [IsGalois k E]

omit [IsGalois k K] in
/-- The inflation of a cochain of a finite Galois level is smooth. -/
theorem isSmooth₁_units_map_restrictNormalHom (t : Gal(↥E/k) → (↥E)ˣ) :
    IsSmooth₁ fun σ : Gal(K/k) =>
      Units.map (algebraMap ↥E K : ↥E →* K) (t (AlgEquiv.restrictNormalHom E σ)) := by
  refine ⟨E.fixingSubgroup, isOpenNormal_fixingSubgroup E, fun x n hn => ?_⟩
  show Units.map (algebraMap ↥E K : ↥E →* K)
      (t (AlgEquiv.restrictNormalHom (F := k) (K₁ := K) E (x * n)))
    = Units.map (algebraMap ↥E K : ↥E →* K) (t (AlgEquiv.restrictNormalHom E x))
  rw [map_mul, restrictNormalHom_eq_one_of_mem_fixingSubgroup E hn, mul_one]

omit [IsGalois k K] [FiniteDimensional k ↥E] in
/-- The inflation of a coboundary of a finite Galois level is the coboundary of the inflated
cochain. -/
theorem coboundary₂_units_map_restrictNormalHom (t : Gal(↥E/k) → (↥E)ˣ) :
    coboundary₂ (fun σ : Gal(K/k) =>
        Units.map (algebraMap ↥E K : ↥E →* K) (t (AlgEquiv.restrictNormalHom E σ)))
      = inflateCocycle (L := ↥E) K (coboundary₂ t) := by
  refine funext fun p => ?_
  obtain ⟨g, h⟩ := p
  show g • Units.map (algebraMap ↥E K : ↥E →* K)
        (t (AlgEquiv.restrictNormalHom (F := k) (K₁ := K) E h))
      / Units.map (algebraMap ↥E K : ↥E →* K) (t (AlgEquiv.restrictNormalHom E (g * h)))
      * Units.map (algebraMap ↥E K : ↥E →* K) (t (AlgEquiv.restrictNormalHom E g))
    = Units.map (algebraMap ↥E K : ↥E →* K)
        (coboundary₂ t (AlgEquiv.restrictNormalHom E g, AlgEquiv.restrictNormalHom E h))
  rw [map_mul (AlgEquiv.restrictNormalHom (F := k) (K₁ := K) E) g h, coboundary₂_apply, map_mul,
    map_div, smul_units_map_algebraMap]

omit [IsGalois k K] in
/-- **A cocycle of a finite Galois level whose crossed product splits is trivial in the smooth
cohomology of the whole Galois group.** -/
theorem smoothH2Mk_eq_one_of_mk_csa_eq_one {w : Gal(↥E/k) × Gal(↥E/k) → (↥E)ˣ}
    (hw : IsMulCocycle₂ w) (h : (⟦CrossedProduct.csa hw⟧ : BrauerGroup k) = 1) :
    smoothH2Mk (inflateCocycle (L := ↥E) K w) (isMulCocycle₂_inflateCocycle hw)
      (isSmooth₂_inflateCocycle E w) = 1 := by
  obtain ⟨t, ht⟩ := isMulCoboundary₂_iff.1 ((CrossedProduct.mk_csa_eq_one_iff hw).1 h)
  refine (smoothH2Mk_eq_one_iff _ _).2 ⟨_, isSmooth₁_units_map_restrictNormalHom E t, ?_⟩
  rw [coboundary₂_units_map_restrictNormalHom E t, ht]

end Injective

section InjectiveHom

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]

/-- **The homomorphism from the smooth second cohomology to the Brauer group is injective.** -/
theorem smoothBrauerHom_injective :
    Function.Injective (smoothBrauerHom (k := k) (K := K)) := by
  refine (injective_iff_map_eq_one _).2 fun z hz => ?_
  obtain ⟨E, hfd, hg, w, hw, hzw⟩ := exists_isGalois_levelCocycle₂ z
  haveI := hfd
  haveI := hg
  have h1 : (⟦CrossedProduct.csa hw⟧ : BrauerGroup k) = 1 := by
    rw [mk_csa_eq_smoothBrauer E hw hzw]
    exact hz
  rw [← hzw]
  exact smoothH2Mk_eq_one_of_mk_csa_eq_one E hw h1

end InjectiveHom

end InverseGalois.CFT

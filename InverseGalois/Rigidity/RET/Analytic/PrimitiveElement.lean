/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.BaseField
import InverseGalois.Rigidity.RET.Analytic.CoverRational
import InverseGalois.Rigidity.RET.Analytic.AlgebraicModel
import InverseGalois.Rigidity.RET.Analytic.GenericSeparation
import InverseGalois.Rigidity.RET.Analytic.Combine

/-!
# A separating function generates the function field

A function of moderate growth that separates the fibres of a covering satisfies a monic equation
over the polynomials in the base coordinate, and the equation is the whole story: the function
field of the covering is generated over `ℂ(T)` by that one function, and the equation it satisfies
is its minimal polynomial.

The counting is what makes this work.  The equation has degree the order of the deck group, so the
minimal polynomial can only be smaller; but the deck group moves the function to that many distinct
elements of the function field, each of them a root of the minimal polynomial, so the minimal
polynomial can only be larger.  The two bounds meet, the equation *is* the minimal polynomial, and
in particular it is irreducible over `ℂ(T)`; the extension it cuts out has degree the order of the
deck group, which is also the degree of the function field, so the function generates.

## Main results

* `Rigidity.RET.algebraMap_ratFunc_baseHom` — a polynomial in the base coordinate, viewed in the
  function field, is the corresponding polynomial function on the covering.
* `Rigidity.RET.smul_algebraMap_coverRing` — the deck group acts on the function field through its
  action on the functions of the covering.
* `Rigidity.RET.exists_algebraic_model_primitive` — a connected covering whose functions of
  moderate growth see its deck group is, away from finitely many points of the base, the root
  variety of a monic polynomial of degree the order of the deck group which is irreducible over
  `ℂ(T)` and whose root generates the function field of the covering.
* `Rigidity.RET.exists_primitive_polynomial` — the field-theoretic half of that statement.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

open Analytic

section Primitive

variable {Y : Type*} [TopologicalSpace Y] [Nonempty Y] [PreconnectedSpace Y] {f : Y → ℂ}
variable {S : Finset ℂ}

attribute [local instance] FractionRing.liftAlgebra ratFuncAlgebra

set_option synthInstance.maxHeartbeats 1000000 in
/-- **A polynomial in the base coordinate, viewed in the function field of the covering, is the
polynomial function it defines on the covering.**  This is the compatibility of the two ways of
mapping `ℂ[T]` into the function field: through the rational functions of the base, or through the
functions of the covering. -/
theorem algebraMap_ratFunc_baseHom (hf : IsLocalHomeomorph f)
    (hrange : Set.range f = (↑S : Set ℂ)ᶜ) (p : ℂ[X]) :
    letI := baseAlgebra hf hrange
    haveI := isTorsionFree_coverRing hf hrange
    letI := coverRatFuncAlgebra hf hrange
    algebraMap (RatFunc ℂ) (FractionRing ↥(coverRing hf S)) (algebraMap ℂ[X] (RatFunc ℂ) p) =
      algebraMap ↥(coverRing hf S) (FractionRing ↥(coverRing hf S)) (baseHom hf S p) := by
  letI := baseAlgebra hf hrange
  haveI := isTorsionFree_coverRing hf hrange
  letI := coverRatFuncAlgebra hf hrange
  rw [algebraMap_algebraOfRingEquiv]
  rw [IsScalarTower.algebraMap_apply ℂ[X] (Localization.Away (punctPoly S)) (RatFunc ℂ)]
  rw [show (fractionRingAwayAlgEquivRatFunc S).symm.toRingEquiv
        ((algebraMap (Localization.Away (punctPoly S)) (RatFunc ℂ))
          ((algebraMap ℂ[X] (Localization.Away (punctPoly S))) p)) =
      algebraMap (Localization.Away (punctPoly S))
        (FractionRing (Localization.Away (punctPoly S)))
        ((algebraMap ℂ[X] (Localization.Away (punctPoly S))) p) from
      (fractionRingAwayAlgEquivRatFunc S).symm.commutes _]
  rw [← IsScalarTower.algebraMap_apply]
  rw [IsScalarTower.algebraMap_apply (Localization.Away (punctPoly S)) ↥(coverRing hf S)
    (FractionRing ↥(coverRing hf S))]
  exact congrArg _ (baseAwayHom_algebraMap hf hrange p)

section Action

variable {H : Type*} [Group H] [Finite H] [MulAction H Y] [ContinuousConstSMul H Y]

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The deck group acts on the function field through its action on the functions of the
covering**: the action extended to the fraction field agrees with the original one on the
functions themselves. -/
theorem smul_algebraMap_coverRing (hf : IsLocalHomeomorph f)
    (hrange : Set.range f = (↑S : Set ℂ)ᶜ) [IsOverBase H f]
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y)
    (hsep : ∀ a : H, a ≠ 1 → ∃ F ∈ coverRing hf S, ∃ y : Y, F (a • y) ≠ F y)
    (a : H) (r : ↥(coverRing hf S)) :
    letI := baseAlgebra hf hrange
    haveI := isGaloisGroup_coverRing hf hrange htrans hsep
    haveI := isTorsionFree_coverRing hf hrange
    letI := FractionRing.mulSemiringAction_of_isGaloisGroup H
      (Localization.Away (punctPoly S)) ↥(coverRing hf S)
    a • (algebraMap ↥(coverRing hf S) (FractionRing ↥(coverRing hf S)) r) =
      algebraMap ↥(coverRing hf S) (FractionRing ↥(coverRing hf S)) (a • r) := by
  letI := baseAlgebra hf hrange
  haveI := isGaloisGroup_coverRing hf hrange htrans hsep
  haveI := isTorsionFree_coverRing hf hrange
  letI := FractionRing.mulSemiringAction_of_isGaloisGroup H
    (Localization.Away (punctPoly S)) ↥(coverRing hf S)
  exact IsFractionRing.fieldEquivOfAlgEquiv_algebraMap _ _ _ _ r

end Action

section Equation

omit [Nonempty Y] [PreconnectedSpace Y] in
/-- **Evaluating the monic polynomial assembled from a family of coefficients** at a function of
the covering gives the leading power plus the sum of the lower terms. -/
theorem eval₂_baseHom_monicPoly (hf : IsLocalHomeomorph f) (S : Finset ℂ) (b : ℕ → ℂ[X]) (n : ℕ)
    (w : ↥(coverRing hf S)) :
    Polynomial.eval₂ (baseHom hf S) w (monicPoly b n)
      = w ^ n + ∑ k ∈ Finset.range n, baseHom hf S (b k) * w ^ k := by
  simp [monicPoly, eval₂_finset_sum]

end Equation

end Primitive

section Main

universe u

variable {Y : Type u} [TopologicalSpace Y] [Nonempty Y] [PreconnectedSpace Y] {f : Y → ℂ}
variable {S : Finset ℂ}
variable {H : Type*} [Group H] [Finite H] [MulAction H Y] [ContinuousConstSMul H Y]

attribute [local instance] FractionRing.liftAlgebra ratFuncAlgebra

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **The function field of a connected covering whose functions of moderate growth see its deck
group is generated by one root of a monic irreducible polynomial of degree the order of the deck
group.**

The functions moving the deck transformations one at a time combine into a single function
separating the points of a fibre; multiplied by the leading coefficient of the equation it
satisfies, it becomes a function `w` satisfying a *monic* equation `P` of degree the order `n` of
the deck group, still separating a fibre.  Over the rational functions of the base, the minimal
polynomial of `w` divides `P`, so has degree at most `n`; and the `n` translates of `w` under the
deck group are distinct elements of the function field, each a root of that minimal polynomial, so
its degree is at least `n`.  Hence the minimal polynomial is `P`, which is therefore irreducible,
and `w` generates a subextension of degree `n` — all of the function field, whose degree over the
base is the order of the deck group. -/
theorem exists_algebraic_model_primitive (hf : IsLocalHomeomorph f)
    (hrange : Set.range f = (↑S : Set ℂ)ᶜ) [IsOverBase H f]
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y)
    (hne : ∀ a : H, a ≠ 1 → ∃ F ∈ coverRing hf S, ∃ y : Y, F (a • y) ≠ F y) :
    ∃ (P : Polynomial ℂ[X]) (S' : Finset ℂ), S ⊆ S' ∧ P.Monic ∧ P.natDegree = Nat.card H ∧
      (∀ z ∉ (S' : Set ℂ), (spec P z).Separable) ∧
      (∃ Φ : ↥(f ⁻¹' ((S' : Set ℂ)ᶜ)) ≃ₜ RootTotal P S',
        ∀ y, rootBase P S' (Φ y) = f (y : Y)) ∧
      Irreducible (P.map (algebraMap ℂ[X] (RatFunc ℂ))) ∧
      ∃ (L : Type u) (_ : Field L) (_ : Algebra (RatFunc ℂ) L), IsGalois (RatFunc ℂ) L ∧
        Nonempty (H ≃* (L ≃ₐ[RatFunc ℂ] L)) ∧
        ∃ α : L, aeval α (P.map (algebraMap ℂ[X] (RatFunc ℂ))) = 0 ∧
          IntermediateField.adjoin (RatFunc ℂ) {α} = ⊤ := by
  classical
  haveI : Fintype H := Fintype.ofFinite H
  -- a function of moderate growth separating the fibres over the complement of a finite set
  obtain ⟨F, hF, y₁, hinj₁⟩ := hasSeparatingFunction_of_forall_ne (H := H) hf hne
  have hne' : ∀ c : H, c ≠ 1 → ∃ y : Y, F (c • y) ≠ F y := fun c hc =>
    ⟨y₁, fun h => hc (hinj₁ c 1 (by simpa using h))⟩
  obtain ⟨S₁, hS₁, hsepF⟩ := exists_finset_separating (H := H) hf htrans hrange hF hne'
  -- the monic equation it satisfies after clearing the denominator
  obtain ⟨A, R₀, mgr, hA, hinf⟩ := hF.2.infty
  obtain ⟨bc, d, hd, heq⟩ := exists_integral_of_growth (H := H) hf
    (fun a y => IsOverBase.smul_eq (f := f) a y) htrans hF.1 S hrange hF.2.punct hA hinf
  set n := Fintype.card H with hn
  set W : Y → ℂ := fun y => d.eval (f y) * F y with hWdef
  have hWmem : W ∈ coverRing hf S :=
    Subring.mul_mem _ (polynomial_mem_coverRing hf S d) hF
  set w : ↥(coverRing hf S) := ⟨W, hWmem⟩ with hw
  -- a fibre on which it separates
  set S' : Finset ℂ := S₁ ∪ d.roots.toFinset with hS'
  have hdne : ∀ z ∉ (S' : Set ℂ), d.eval z ≠ 0 := by
    intro z hz hzero
    exact hz (by
      simp only [hS', Finset.coe_union, Set.mem_union, Finset.mem_coe, Multiset.mem_toFinset]
      exact Or.inr ((mem_roots hd.ne_zero).2 hzero))
  have hmem₁ : ∀ z ∉ (S' : Set ℂ), z ∉ (S₁ : Set ℂ) := by
    intro z hz hmem
    exact hz (by
      simp only [hS', Finset.coe_union, Set.mem_union]
      exact Or.inl hmem)
  have hsepW : ∀ y : Y, f y ∉ (S' : Set ℂ) → ∀ c : H, c ≠ 1 → W (c • y) ≠ W y := by
    intro y hy c hc
    simp only [hWdef, IsOverBase.smul_eq (f := f)]
    exact fun h => hsepF y (hmem₁ _ hy) c hc (mul_left_cancel₀ (hdne _ hy) h)
  have hsurj : ∀ z ∉ (S' : Set ℂ), ∃ y : Y, f y = z := by
    intro z hz
    have hzS : z ∈ ((S : Set ℂ))ᶜ := fun hmem => hmem₁ z hz (hS₁ hmem)
    rw [← hrange] at hzS
    exact hzS
  -- the equation, read along the fibres
  have hroot : ∀ y : Y, (spec (monicPoly bc n) (f y)).eval (W y) = 0 := by
    intro y
    rw [eval_spec_monicPoly, hWdef]
    exact heq y
  have hWc : Continuous W := by
    rw [hWdef]
    exact (d.continuous.comp hf.continuous).mul (hF.1.continuous hf)
  have hsepz : ∀ z ∉ (S' : Set ℂ), (spec (monicPoly bc n) z).Separable := by
    intro z hz
    obtain ⟨y₂, rfl⟩ := hsurj z hz
    exact separable_spec_of_separating (H := H) (W := W) (monicPoly_monic _ _)
      (natDegree_monicPoly _ _) hroot hsepW hz
  have hmodel := exists_homeo_rootTotal_of_separating (H := H) hf hWc (monicPoly_monic bc n)
    (natDegree_monicPoly bc n) hroot htrans hsepW hsurj
  obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset S'
  have hzc : z ∉ (S' : Set ℂ) := by exact_mod_cast hz
  obtain ⟨y₀, hy₀⟩ := hsurj z hzc
  have hy₀' : f y₀ ∉ (S' : Set ℂ) := by rw [hy₀]; exact hzc
  have hinjW : Function.Injective fun a : H => W (a • y₀) :=
    injective_smul_of_separating (H := H) (W := W) hsepW hy₀'
  -- the translates of the coordinate are pairwise distinct
  have hsmulne : ∀ a b : H, a ≠ b → a • w ≠ b • w := by
    intro a b hab hcon
    refine hab (inv_injective (hinjW ?_))
    have hval := congrFun (congrArg Subtype.val hcon) y₀
    rw [coverRing_smul_coe, coverRing_smul_coe] at hval
    exact hval
  -- the equation, read in the ring of functions of the covering
  have hReq : Polynomial.eval₂ (baseHom hf S) w (monicPoly bc n) = 0 := by
    rw [eval₂_baseHom_monicPoly]
    refine Subtype.ext (funext fun y => ?_)
    push_cast
    simp only [Finset.sum_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.zero_apply,
      baseHom_apply_coe, hw]
    exact heq y
  -- the function field of the covering
  letI := baseAlgebra hf hrange
  haveI := isGaloisGroup_coverRing hf hrange htrans hne
  haveI := isTorsionFree_coverRing hf hrange
  letI := FractionRing.mulSemiringAction_of_isGaloisGroup H
    (Localization.Away (punctPoly S)) ↥(coverRing hf S)
  letI := coverRatFuncAlgebra hf hrange
  haveI := isGaloisGroup_ratFunc_coverRing hf hrange htrans hne
  haveI : FiniteDimensional (RatFunc ℂ) (FractionRing ↥(coverRing hf S)) :=
    IsGaloisGroup.finiteDimensional H _ _
  set L := FractionRing ↥(coverRing hf S) with hL
  set α : L := algebraMap ↥(coverRing hf S) L w with hα
  set Q : Polynomial (RatFunc ℂ) := (monicPoly bc n).map (algebraMap ℂ[X] (RatFunc ℂ)) with hQ
  have hQmonic : Q.Monic := (monicPoly_monic bc n).map _
  have hQdeg : Q.natDegree = n := by
    rw [hQ, (monicPoly_monic bc n).natDegree_map, natDegree_monicPoly]
  have hQα : (aeval α) Q = 0 := by
    rw [hQ, aeval_def, eval₂_map]
    have hcomp : (algebraMap (RatFunc ℂ) L).comp (algebraMap ℂ[X] (RatFunc ℂ))
        = (algebraMap ↥(coverRing hf S) L).comp (baseHom hf S) :=
      RingHom.ext fun p => algebraMap_ratFunc_baseHom hf hrange p
    rw [hcomp, ← Polynomial.hom_eval₂, hReq, map_zero]
  have hint : IsIntegral (RatFunc ℂ) α := ⟨Q, hQmonic, hQα⟩
  set mp := minpoly (RatFunc ℂ) α with hmp
  have hmpne : mp ≠ 0 := minpoly.ne_zero hint
  have hmdvd : mp ∣ Q := minpoly.dvd _ _ hQα
  -- the translates of the coordinate are distinct roots of the minimal polynomial
  have hsmulα : ∀ a : H, a • α = algebraMap ↥(coverRing hf S) L (a • w) := fun a =>
    smul_algebraMap_coverRing hf hrange htrans hne a w
  have hαinj : Function.Injective fun a : H => a • α := by
    intro a b hab
    by_contra hne2
    refine hsmulne a b hne2 (IsFractionRing.injective ↥(coverRing hf S) L ?_)
    rw [← hsmulα a, ← hsmulα b]
    exact hab
  have hconj : ∀ a : H, (aeval (a • α)) mp = 0 := by
    intro a
    have hap : (aeval ((MulSemiringAction.toAlgHom (RatFunc ℂ) L a) α)) mp
        = (MulSemiringAction.toAlgHom (RatFunc ℂ) L a) ((aeval α) mp) :=
      Polynomial.aeval_algHom_apply _ α mp
    simpa [hmp, minpoly.aeval] using hap
  set mL := mp.map (algebraMap (RatFunc ℂ) L) with hmL
  have hmLne : mL ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap (RatFunc ℂ) L).injective).2 hmpne
  have hrootmem : ∀ a : H, (a • α) ∈ mL.roots := by
    intro a
    refine (mem_roots hmLne).2 ?_
    rw [IsRoot, hmL, Polynomial.eval_map, ← aeval_def]
    exact hconj a
  have hcard : n ≤ mp.natDegree := by
    have hsub : (Finset.univ.image fun a : H => a • α) ⊆ mL.roots.toFinset := by
      intro x hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
      exact Multiset.mem_toFinset.2 (hrootmem a)
    calc n = (Finset.univ.image fun a : H => a • α).card := by
            rw [Finset.card_image_of_injective _ hαinj, Finset.card_univ]
      _ ≤ mL.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card mL.roots := mL.roots.toFinset_card_le
      _ ≤ mL.natDegree := Polynomial.card_roots' mL
      _ = mp.natDegree := natDegree_map_eq_of_injective (algebraMap (RatFunc ℂ) L).injective mp
  have hle : mp.natDegree ≤ n := hQdeg ▸ Polynomial.natDegree_le_of_dvd hmdvd hQmonic.ne_zero
  have hdeg : mp.natDegree = n := le_antisymm hle hcard
  have hmQ : mp = Q := by
    obtain ⟨c, hc⟩ := hmdvd
    have hcm : c.Monic := (minpoly.monic hint).of_mul_monic_left (hc ▸ hQmonic)
    have hc0 : c.natDegree = 0 := by
      have := hQdeg
      rw [hc, Polynomial.natDegree_mul hmpne hcm.ne_zero, hdeg] at this
      omega
    rw [hc, hcm.natDegree_eq_zero.1 hc0, mul_one]
  have hfr : Module.finrank (RatFunc ℂ) L = Nat.card H :=
    finrank_ratFunc_coverRing hf hrange htrans hne
  have hirr : Irreducible ((monicPoly bc n).map (algebraMap ℂ[X] (RatFunc ℂ))) := by
    rw [← hQ, ← hmQ]; exact minpoly.irreducible hint
  refine ⟨monicPoly bc n, S', hS₁.trans Finset.subset_union_left, monicPoly_monic bc n, ?_,
    hsepz, hmodel, hirr,
    L, inferInstance, inferInstance, isGalois_ratFunc_coverRing hf hrange htrans hne,
    ⟨mulEquivAlgEquiv_ratFunc_coverRing hf hrange htrans hne⟩, α, hQα, ?_⟩
  · rw [natDegree_monicPoly, hn, Nat.card_eq_fintype_card]
  · exact (Field.primitive_element_iff_minpoly_natDegree_eq (RatFunc ℂ) α).2
      (by rw [← hmp, hdeg, hfr, Nat.card_eq_fintype_card])

/-- **The function field of a connected covering whose functions of moderate growth see its deck
group is generated by one root of a monic irreducible polynomial of degree the order of the deck
group.**  This is the field-theoretic half of the statement above. -/
theorem exists_primitive_polynomial (hf : IsLocalHomeomorph f)
    (hrange : Set.range f = (↑S : Set ℂ)ᶜ) [IsOverBase H f]
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y)
    (hne : ∀ a : H, a ≠ 1 → ∃ F ∈ coverRing hf S, ∃ y : Y, F (a • y) ≠ F y) :
    ∃ P : Polynomial ℂ[X], P.Monic ∧ P.natDegree = Nat.card H ∧
      Irreducible (P.map (algebraMap ℂ[X] (RatFunc ℂ))) ∧
      ∃ (L : Type u) (_ : Field L) (_ : Algebra (RatFunc ℂ) L), IsGalois (RatFunc ℂ) L ∧
        Nonempty (H ≃* (L ≃ₐ[RatFunc ℂ] L)) ∧
        ∃ α : L, aeval α (P.map (algebraMap ℂ[X] (RatFunc ℂ))) = 0 ∧
          IntermediateField.adjoin (RatFunc ℂ) {α} = ⊤ := by
  obtain ⟨P, -, -, hP, hdeg, -, -, hirr, rest⟩ :=
    exists_algebraic_model_primitive (H := H) hf hrange htrans hne
  exact ⟨P, hP, hdeg, hirr, rest⟩

end Main

end Rigidity.RET

end

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.CoverRing

/-!
# The regular functions on a punctured plane, and the covering over them

The functions on the punctured plane which are quotients of a polynomial by a power of the product
of the distances to the punctures form a localization of the polynomial ring, and they are exactly
the functions on a covering of moderate growth which the deck group leaves fixed.  That is the last
piece of the Galois correspondence for a covering: it identifies the invariants concretely, instead
of naming them as a ring of fixed points.

## Main definitions

* `Rigidity.RET.punctPoly` — the monic polynomial whose roots are the punctures.
* `Rigidity.RET.baseHom` — the polynomials of the base coordinate, read as functions of moderate
  growth on the total space.
* `Rigidity.RET.baseAwayHom` — the same for the regular functions on the punctured plane.

## Main results

* `Rigidity.RET.isModerate_inv_punctPoly` — the reciprocal of the product of the distances to the
  punctures is of moderate growth.
* `Rigidity.RET.isUnit_punctPoly_coverRing` — hence that product is invertible in the ring of
  functions of the covering.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

/-! ### The polynomial vanishing at the punctures -/

section Punct

variable {Y : Type*} {f : Y → ℂ} {S : Finset ℂ}

/-- **The monic polynomial whose roots are the punctures.** -/
def punctPoly (S : Finset ℂ) : ℂ[X] := ∏ s ∈ S, (X - C s)

theorem punctPoly_monic (S : Finset ℂ) : (punctPoly S).Monic :=
  monic_prod_of_monic _ _ fun s _ => monic_X_sub_C s

theorem eval_punctPoly (S : Finset ℂ) (z : ℂ) :
    (punctPoly S).eval z = ∏ s ∈ S, (z - s) := by
  simp [punctPoly, eval_prod]

theorem eval_punctPoly_ne_zero {z : ℂ} (hz : z ∉ S) : (punctPoly S).eval z ≠ 0 := by
  rw [eval_punctPoly]
  exact Finset.prod_ne_zero_iff.2 fun s hs => sub_ne_zero.2 fun h => hz (h ▸ hs)

/-- A point of the total space lies over no puncture. -/
theorem notMem_of_range_eq (hrange : Set.range f = (↑S : Set ℂ)ᶜ) (y : Y) : f y ∉ S := by
  have : f y ∈ (↑S : Set ℂ)ᶜ := hrange ▸ Set.mem_range_self y
  exact this

theorem eval_punctPoly_comp_ne_zero (hrange : Set.range f = (↑S : Set ℂ)ᶜ) (y : Y) :
    (punctPoly S).eval (f y) ≠ 0 :=
  eval_punctPoly_ne_zero (notMem_of_range_eq hrange y)

/-- Near a puncture the other punctures stay at a distance. -/
theorem exists_pos_le_norm_sub_of_mem_erase (S : Finset ℂ) (s : ℂ) :
    ∃ ρ > (0 : ℝ), ∀ s' ∈ S.erase s, 2 * ρ ≤ ‖s - s'‖ := by
  rcases (S.erase s).eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  · refine ⟨(S.erase s).inf' h fun s' => ‖s - s'‖ / 2, ?_, fun s' hs' => ?_⟩
    · rw [gt_iff_lt, Finset.lt_inf'_iff]
      intro s' hs'
      have hne : s - s' ≠ 0 := sub_ne_zero.2 fun hc => (Finset.ne_of_mem_erase hs') hc.symm
      have : 0 < ‖s - s'‖ := norm_pos_iff.2 hne
      linarith
    · have := Finset.inf'_le (fun s' => ‖s - s'‖ / 2) hs'
      linarith

/-- **The reciprocal of the product of the distances to the punctures is of moderate growth**: at a
puncture it blows up like the first power of the distance to it, and at infinity it is bounded. -/
theorem isModerate_inv_punctPoly (f : Y → ℂ) (S : Finset ℂ) :
    IsModerate f S fun y => ((punctPoly S).eval (f y))⁻¹ where
  punct := by
    intro s hs
    obtain ⟨ρ, hρ, hsep⟩ := exists_pos_le_norm_sub_of_mem_erase S s
    refine ⟨ρ, hρ, (ρ ^ (S.erase s).card)⁻¹, by positivity, 1, fun y hy => ?_⟩
    have hne : f y - s ≠ 0 := sub_ne_zero.2 (by simpa using hy.2)
    have hlt : ‖f y - s‖ < ρ := by
      have := hy.1
      rwa [Metric.mem_ball, Complex.dist_eq] at this
    have hfac : ∀ s' ∈ S.erase s, ρ ≤ ‖f y - s'‖ := by
      intro s' hs'
      have h1 : 2 * ρ ≤ ‖s - s'‖ := hsep s' hs'
      have h2 : ‖s - s'‖ ≤ ‖f y - s'‖ + ‖f y - s‖ := by
        have : s - s' = (f y - s') - (f y - s) := by ring
        rw [this]
        exact norm_sub_le _ _
      linarith
    have hprod : ρ ^ (S.erase s).card ≤ ∏ s' ∈ S.erase s, ‖f y - s'‖ := by
      calc ρ ^ (S.erase s).card = ∏ _s' ∈ S.erase s, ρ := by rw [Finset.prod_const]
        _ ≤ ∏ s' ∈ S.erase s, ‖f y - s'‖ :=
            Finset.prod_le_prod (fun _ _ => le_of_lt hρ) hfac
    have hsplit : ‖(punctPoly S).eval (f y)‖ = ‖f y - s‖ * ∏ s' ∈ S.erase s, ‖f y - s'‖ := by
      rw [eval_punctPoly, ← Finset.mul_prod_erase S _ hs, norm_mul, norm_prod]
    have hpos : (0 : ℝ) < ‖f y - s‖ := norm_pos_iff.2 hne
    have hppos : (0 : ℝ) < ρ ^ (S.erase s).card := pow_pos hρ _
    have hkey : ‖f y - s‖ / (‖f y - s‖ * ∏ s' ∈ S.erase s, ‖f y - s'‖)
        = (∏ s' ∈ S.erase s, ‖f y - s'‖)⁻¹ := by
      field_simp
    have hle := one_div_le_one_div_of_le hppos hprod
    rw [one_div, one_div] at hle
    rw [norm_inv, hsplit, pow_one, inv_mul_eq_div, hkey]
    exact hle
  infty := by
    refine ⟨1, 1 + 2 * ∑ s ∈ S, ‖s‖, 0, zero_le_one, fun y hy => ?_⟩
    have hone : ∀ s ∈ S, (1 : ℝ) ≤ ‖f y - s‖ := by
      intro s hs
      have hle : ‖s‖ ≤ ∑ s' ∈ S, ‖s'‖ :=
        Finset.single_le_sum (f := fun s' : ℂ => ‖s'‖) (fun _ _ => norm_nonneg _) hs
      have h2 : ‖f y‖ - ‖s‖ ≤ ‖f y - s‖ := norm_sub_norm_le _ _
      have hsum : (0 : ℝ) ≤ ∑ s' ∈ S, ‖s'‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
      linarith
    have hprod : (1 : ℝ) ≤ ‖(punctPoly S).eval (f y)‖ := by
      rw [eval_punctPoly, norm_prod]
      calc (1 : ℝ) = ∏ _s ∈ S, (1 : ℝ) := by rw [Finset.prod_const_one]
        _ ≤ ∏ s ∈ S, ‖f y - s‖ := Finset.prod_le_prod (fun _ _ => zero_le_one) hone
    rw [norm_inv, pow_zero, mul_one]
    exact inv_le_one_of_one_le₀ hprod

end Punct

/-! ### The base ring inside the ring of the covering -/

section Base

variable {Y : Type*} [TopologicalSpace Y] {f : Y → ℂ} {S : Finset ℂ}

/-- A polynomial of the base coordinate is a function of moderate growth on the total space. -/
theorem polynomial_mem_coverRing (hf : IsLocalHomeomorph f) (S : Finset ℂ) (p : ℂ[X]) :
    (fun y => p.eval (f y)) ∈ coverRing hf S := by
  refine ⟨fun y => isHoloAt_comp_of_analyticAt (g₀ := fun z : ℂ => p.eval z) hf ?_,
    isModerate_polynomial f S p⟩
  simpa using (analyticAt_id (𝕜 := ℂ) (z := f y)).aeval_polynomial p

/-- **The polynomials of the base coordinate, as functions on the total space.** -/
def baseHom (hf : IsLocalHomeomorph f) (S : Finset ℂ) : ℂ[X] →+* ↥(coverRing hf S) :=
  (baseEvalHom f).codRestrict (coverRing hf S) (polynomial_mem_coverRing hf S)

@[simp]
theorem baseHom_apply_coe (hf : IsLocalHomeomorph f) (S : Finset ℂ) (p : ℂ[X]) (y : Y) :
    ((baseHom hf S p : ↥(coverRing hf S)) : Y → ℂ) y = p.eval (f y) := rfl

/-- The reciprocal of the product of the distances to the punctures is a function of moderate
growth on the total space. -/
theorem inv_punctPoly_mem_coverRing (hf : IsLocalHomeomorph f)
    (hrange : Set.range f = (↑S : Set ℂ)ᶜ) :
    (fun y => ((punctPoly S).eval (f y))⁻¹) ∈ coverRing hf S := by
  refine ⟨fun y => isHoloAt_comp_of_analyticAt
    (g₀ := fun z : ℂ => ((punctPoly S).eval z)⁻¹) hf ?_, isModerate_inv_punctPoly f S⟩
  have hana : AnalyticAt ℂ (fun z : ℂ => (punctPoly S).eval z) (f y) := by
    simpa using (analyticAt_id (𝕜 := ℂ) (z := f y)).aeval_polynomial (punctPoly S)
  exact hana.inv (eval_punctPoly_comp_ne_zero hrange y)

/-- **The product of the distances to the punctures is invertible in the ring of functions of the
covering.** -/
theorem isUnit_punctPoly_coverRing (hf : IsLocalHomeomorph f)
    (hrange : Set.range f = (↑S : Set ℂ)ᶜ) : IsUnit (baseHom hf S (punctPoly S)) := by
  refine isUnit_iff_exists_inv.2 ⟨⟨_, inv_punctPoly_mem_coverRing hf hrange⟩, ?_⟩
  refine Subtype.ext (funext fun y => ?_)
  show (punctPoly S).eval (f y) * ((punctPoly S).eval (f y))⁻¹ = 1
  exact mul_inv_cancel₀ (eval_punctPoly_comp_ne_zero hrange y)

/-- **The regular functions on the punctured plane, as functions on the total space.** -/
def baseAwayHom (hf : IsLocalHomeomorph f) (hrange : Set.range f = (↑S : Set ℂ)ᶜ) :
    Localization.Away (punctPoly S) →+* ↥(coverRing hf S) :=
  Localization.awayLift (baseHom hf S) (punctPoly S) (isUnit_punctPoly_coverRing hf hrange)

@[simp]
theorem baseAwayHom_algebraMap (hf : IsLocalHomeomorph f)
    (hrange : Set.range f = (↑S : Set ℂ)ᶜ) (p : ℂ[X]) :
    baseAwayHom hf hrange (algebraMap ℂ[X] (Localization.Away (punctPoly S)) p) =
      baseHom hf S p :=
  IsLocalization.Away.lift_eq _ (isUnit_punctPoly_coverRing hf hrange) p

end Base

/-! ### The covering over the regular functions on the punctured plane -/

section Galois

variable {Y : Type*} [TopologicalSpace Y] {f : Y → ℂ} {S : Finset ℂ}
variable {H : Type*} [Group H] [MulAction H Y] [ContinuousConstSMul H Y]

/-- **The ring of functions of the covering is an algebra over the regular functions on the
punctured plane.** -/
def baseAlgebra (hf : IsLocalHomeomorph f) (hrange : Set.range f = (↑S : Set ℂ)ᶜ) :
    Algebra (Localization.Away (punctPoly S)) ↥(coverRing hf S) :=
  (baseAwayHom hf hrange).toAlgebra

/-- **The deck group fixes the regular functions on the punctured plane**: they are functions of
the base coordinate, which the deck group does not move. -/
theorem smul_baseAwayHom (hf : IsLocalHomeomorph f) (hrange : Set.range f = (↑S : Set ℂ)ᶜ)
    [IsOverBase H f] (a : H) (x : Localization.Away (punctPoly S)) :
    a • baseAwayHom hf hrange x = baseAwayHom hf hrange x := by
  have hcomp : (MulSemiringAction.toRingHom H ↥(coverRing hf S) a).comp
      (baseAwayHom hf hrange) = baseAwayHom hf hrange := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (punctPoly S)) (RingHom.ext fun p => ?_)
    simp only [RingHom.comp_apply, baseAwayHom_algebraMap]
    refine Subtype.ext (funext fun y => ?_)
    show ((a • baseHom hf S p : ↥(coverRing hf S)) : Y → ℂ) y = p.eval (f y)
    rw [coverRing_smul_coe]
    simp [IsOverBase.smul_eq]
  exact DFunLike.congr_fun hcomp x

/-- **Every function of the covering which the deck group fixes is a regular function on the
punctured plane**: it is a polynomial in the base coordinate divided by a power of the product of
the distances to the punctures. -/
theorem isInvariant_coverRing (hf : IsLocalHomeomorph f)
    (hrange : Set.range f = (↑S : Set ℂ)ᶜ) [IsOverBase H f]
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y) :
    letI := baseAlgebra hf hrange
    Algebra.IsInvariant (Localization.Away (punctPoly S)) ↥(coverRing hf S) H := by
  letI := baseAlgebra hf hrange
  refine ⟨fun F hF => ?_⟩
  have hinv : ∀ (a : H) (y : Y), (F : Y → ℂ) (a • y) = (F : Y → ℂ) y := by
    intro a y
    have h := congrFun (congrArg Subtype.val (hF a⁻¹)) y
    rwa [coverRing_smul_coe, inv_inv] at h
  obtain ⟨p, e, hpe⟩ := exists_eq_div_prod_of_invariant_of_moderate (H := H) hf htrans
    (mem_coverRing.1 F.2).1 hinv hrange (mem_coverRing.1 F.2).2
  have hFmul : F * baseHom hf S (punctPoly S ^ e) = baseHom hf S p := by
    refine Subtype.ext (funext fun y => ?_)
    show (F : Y → ℂ) y * (punctPoly S ^ e).eval (f y) = p.eval (f y)
    rw [eval_pow, eval_punctPoly, ← hpe y]
    ring
  refine ⟨IsLocalization.mk' (Localization.Away (punctPoly S)) p
    (⟨punctPoly S ^ e, e, rfl⟩ : Submonoid.powers (punctPoly S)), ?_⟩
  have hspec := IsLocalization.mk'_spec (Localization.Away (punctPoly S)) p
    (⟨punctPoly S ^ e, e, rfl⟩ : Submonoid.powers (punctPoly S))
  have hmul := congrArg (baseAwayHom hf hrange) hspec
  rw [map_mul, baseAwayHom_algebraMap, baseAwayHom_algebraMap] at hmul
  have hunit : IsUnit (baseHom hf S (punctPoly S ^ e)) := by
    rw [map_pow]
    exact (isUnit_punctPoly_coverRing hf hrange).pow e
  show baseAwayHom hf hrange _ = F
  exact (hunit.mul_left_inj.1 (hmul.trans hFmul.symm))

/-- **The deck group of a connected covering is a Galois group for its ring of functions over the
regular functions on the punctured plane**, as soon as every nontrivial deck transformation moves
one of those functions. -/
theorem isGaloisGroup_coverRing [Finite H] (hf : IsLocalHomeomorph f)
    (hrange : Set.range f = (↑S : Set ℂ)ᶜ) [IsOverBase H f]
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y)
    (hsep : ∀ a : H, a ≠ 1 → ∃ F ∈ coverRing hf S, ∃ y : Y, F (a • y) ≠ F y) :
    letI := baseAlgebra hf hrange
    IsGaloisGroup H (Localization.Away (punctPoly S)) ↥(coverRing hf S) := by
  letI := baseAlgebra hf hrange
  refine ⟨faithfulSMul_coverRing hf S hsep, ⟨fun a x F => ?_⟩,
    isInvariant_coverRing hf hrange htrans⟩
  show a • (x • F) = x • (a • F)
  rw [Algebra.smul_def, Algebra.smul_def, smul_mul']
  congr 1
  exact smul_baseAwayHom hf hrange a x

end Galois

/-! ### The function field of the covering -/

section Fraction

variable {Y : Type*} [TopologicalSpace Y] [Nonempty Y] [PreconnectedSpace Y] {f : Y → ℂ}
variable {S : Finset ℂ}
variable {H : Type*} [Group H] [Finite H] [MulAction H Y] [ContinuousConstSMul H Y]

attribute [local instance] FractionRing.liftAlgebra

theorem punctPoly_ne_zero (S : Finset ℂ) : punctPoly S ≠ 0 := (punctPoly_monic S).ne_zero

theorem powers_punctPoly_le_nonZeroDivisors (S : Finset ℂ) :
    Submonoid.powers (punctPoly S) ≤ nonZeroDivisors ℂ[X] :=
  powers_le_nonZeroDivisors_of_noZeroDivisors (punctPoly_ne_zero S)

instance isDomain_localizationAway_punctPoly (S : Finset ℂ) :
    IsDomain (Localization.Away (punctPoly S)) :=
  IsLocalization.isDomain_localization (powers_punctPoly_le_nonZeroDivisors S)

omit [Nonempty Y] [PreconnectedSpace Y] in
/-- **A polynomial of the base coordinate vanishing on the whole total space is zero**: the base
coordinate takes every value off the punctures, and a polynomial with infinitely many roots is
zero. -/
theorem baseHom_injective (hf : IsLocalHomeomorph f) (hrange : Set.range f = (↑S : Set ℂ)ᶜ) :
    Function.Injective (baseHom hf S) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  refine Polynomial.eq_zero_of_infinite_isRoot p ?_
  refine (Set.Finite.infinite_compl (S.finite_toSet)).mono fun z hz => ?_
  rw [← hrange] at hz
  obtain ⟨y, rfl⟩ := hz
  exact congrFun (congrArg Subtype.val hp) y

omit [Nonempty Y] [PreconnectedSpace Y] in
/-- **The regular functions on the punctured plane are distinct as functions on the covering.** -/
theorem baseAwayHom_injective (hf : IsLocalHomeomorph f)
    (hrange : Set.range f = (↑S : Set ℂ)ᶜ) : Function.Injective (baseAwayHom hf hrange) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨p, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (punctPoly S)) x
  have hspec := congrArg (baseAwayHom hf hrange)
    (IsLocalization.mk'_spec (Localization.Away (punctPoly S)) p s)
  rw [map_mul, baseAwayHom_algebraMap, baseAwayHom_algebraMap, hx, zero_mul] at hspec
  have hp : p = 0 :=
    (injective_iff_map_eq_zero (baseHom hf S)).1 (baseHom_injective hf hrange) p hspec.symm
  rw [hp]
  simp

theorem isTorsionFree_coverRing (hf : IsLocalHomeomorph f)
    (hrange : Set.range f = (↑S : Set ℂ)ᶜ) :
    letI := baseAlgebra hf hrange
    Module.IsTorsionFree (Localization.Away (punctPoly S)) ↥(coverRing hf S) := by
  letI := baseAlgebra hf hrange
  exact Module.isTorsionFree_iff_algebraMap_injective.2 (baseAwayHom_injective hf hrange)

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The deck group of a connected covering is a Galois group for its field of functions over the
field of rational functions of the base coordinate.** -/
theorem isGaloisGroup_fractionRing_coverRing (hf : IsLocalHomeomorph f)
    (hrange : Set.range f = (↑S : Set ℂ)ᶜ) [IsOverBase H f]
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y)
    (hsep : ∀ a : H, a ≠ 1 → ∃ F ∈ coverRing hf S, ∃ y : Y, F (a • y) ≠ F y) :
    letI := baseAlgebra hf hrange
    haveI := isGaloisGroup_coverRing hf hrange htrans hsep
    haveI := isTorsionFree_coverRing hf hrange
    letI := FractionRing.mulSemiringAction_of_isGaloisGroup H
      (Localization.Away (punctPoly S)) ↥(coverRing hf S)
    IsGaloisGroup H (FractionRing (Localization.Away (punctPoly S)))
      (FractionRing ↥(coverRing hf S)) := by
  letI := baseAlgebra hf hrange
  haveI := isGaloisGroup_coverRing hf hrange htrans hsep
  haveI := isTorsionFree_coverRing hf hrange
  exact IsGaloisGroup.toFractionRing H _ _

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The function field of a connected covering is a Galois extension of the field of rational
functions of the base coordinate.** -/
theorem isGalois_fractionRing_coverRing (hf : IsLocalHomeomorph f)
    (hrange : Set.range f = (↑S : Set ℂ)ᶜ) [IsOverBase H f]
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y)
    (hsep : ∀ a : H, a ≠ 1 → ∃ F ∈ coverRing hf S, ∃ y : Y, F (a • y) ≠ F y) :
    letI := baseAlgebra hf hrange
    haveI := isTorsionFree_coverRing hf hrange
    IsGalois (FractionRing (Localization.Away (punctPoly S)))
      (FractionRing ↥(coverRing hf S)) := by
  letI := baseAlgebra hf hrange
  haveI := isGaloisGroup_coverRing hf hrange htrans hsep
  haveI := isTorsionFree_coverRing hf hrange
  letI := FractionRing.mulSemiringAction_of_isGaloisGroup H
    (Localization.Away (punctPoly S)) ↥(coverRing hf S)
  haveI := isGaloisGroup_fractionRing_coverRing hf hrange htrans hsep
  exact IsGaloisGroup.isGalois H _ _

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The degree of the function field of a connected covering over the field of rational functions
of the base coordinate is the order of the deck group.** -/
theorem finrank_fractionRing_coverRing (hf : IsLocalHomeomorph f)
    (hrange : Set.range f = (↑S : Set ℂ)ᶜ) [IsOverBase H f]
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y)
    (hsep : ∀ a : H, a ≠ 1 → ∃ F ∈ coverRing hf S, ∃ y : Y, F (a • y) ≠ F y) :
    letI := baseAlgebra hf hrange
    haveI := isTorsionFree_coverRing hf hrange
    Module.finrank (FractionRing (Localization.Away (punctPoly S)))
      (FractionRing ↥(coverRing hf S)) = Nat.card H := by
  letI := baseAlgebra hf hrange
  haveI := isGaloisGroup_coverRing hf hrange htrans hsep
  haveI := isTorsionFree_coverRing hf hrange
  letI := FractionRing.mulSemiringAction_of_isGaloisGroup H
    (Localization.Away (punctPoly S)) ↥(coverRing hf S)
  haveI := isGaloisGroup_fractionRing_coverRing hf hrange htrans hsep
  exact (IsGaloisGroup.card_eq_finrank H _ _).symm

/-! ### The base field is the field of rational functions -/

/-- The rational functions of the base coordinate are an algebra over the regular functions on the
punctured plane. -/
def ratFuncAlgebra (S : Finset ℂ) : Algebra (Localization.Away (punctPoly S)) (RatFunc ℂ) :=
  IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers (punctPoly S))
    (nonZeroDivisors ℂ[X]) (powers_punctPoly_le_nonZeroDivisors S)

attribute [local instance] ratFuncAlgebra

set_option synthInstance.maxHeartbeats 1000000 in
instance isScalarTower_ratFunc (S : Finset ℂ) :
    IsScalarTower ℂ[X] (Localization.Away (punctPoly S)) (RatFunc ℂ) :=
  IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _
    (powers_punctPoly_le_nonZeroDivisors S)

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The rational functions of the base coordinate are the fraction field of the regular functions
on the punctured plane.** -/
instance isFractionRing_ratFunc (S : Finset ℂ) :
    IsFractionRing (Localization.Away (punctPoly S)) (RatFunc ℂ) :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers (punctPoly S)) _ _

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The base field of the extension is the field of rational functions of the base
coordinate.** -/
def fractionRingAwayAlgEquivRatFunc (S : Finset ℂ) :
    FractionRing (Localization.Away (punctPoly S)) ≃ₐ[Localization.Away (punctPoly S)]
      RatFunc ℂ :=
  IsLocalization.algEquiv (nonZeroDivisors (Localization.Away (punctPoly S))) _ _

end Fraction

end Rigidity.RET

end

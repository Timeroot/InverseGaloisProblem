/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Wreath.ConjSep
import InverseGalois.Rigidity.RET.Wreath.GeomDegree
import InverseGalois.Rigidity.RET.Wreath.ParamFinite
import InverseGalois.Rigidity.RET.Wreath.PrivatePlace

/-!
# Choosing the intercept of the substitution

The wreath construction pulls one cyclic cover of the line back along the family of substitutions
`T ↦ h(θ) + c`, one for each conjugate of a primitive element `θ` of the base extension.  For the
degrees to multiply, the radicands of the pulled-back covers must be independent modulo `n`-th
powers, and that is arranged by choosing the intercept `c` outside a finite exceptional set.

The exceptional set is produced by the place-counting argument of `exists_indep_radicands`, which
asks for three things about the conjugates: that each is transcendental over the constants, that
each presents the whole field as a finite extension of the line it spans, and that no two of them
differ by a constant.  All three hold in the geometric closure of a regular extension, the last one
because regularity forces an algebraic difference of conjugates to be a rational one.

The exceptional set lives in the algebraically closed constant field, but the intercept has to be
rational: the substitution `T ↦ h(θ) + c` is required to take its values in the regular extension
`E`, which meets the algebraic numbers only in the rationals.  Since the rationals inject into the
constants, only finitely many rational intercepts are excluded.

## Main results

* `Rigidity.RET.Wreath.geomConj` — the conjugates of the primitive element, read in the geometric
  closure of the base extension.
* `Rigidity.RET.Wreath.transcendental_geomConj` — they are transcendental over the constants.
* `Rigidity.RET.Wreath.sub_geomConj_ne_const` — no two of them differ by a constant.
* `Rigidity.RET.Wreath.exists_good_intercept` — a rational intercept for which the conjugate
  radicands are nonzero and independent modulo `n`-th powers.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET.Wreath

open GeomAKLB

variable {H : Type*} [Group H]

/-! ## The geometric closure as an algebra over the constants -/

/-- **The inclusion of the geometric closure into `ℚ̄(T)‾`, read over the constants.** -/
def geomVal (V : IntermediateField QT QTbar) : ↥(geomClosure V) →ₐ[k] QTbar :=
  (IntermediateField.val (geomClosure V)).restrictScalars k

@[simp] theorem geomVal_apply (V : IntermediateField QT QTbar) (x : ↥(geomClosure V)) :
    geomVal V x = (x : QTbar) := rfl

theorem geomVal_injective (V : IntermediateField QT QTbar) :
    Function.Injective (geomVal V) := Subtype.val_injective

/-! ## The conjugates -/

/-- **The conjugates of a primitive element of the base extension**, read in the geometric closure
of that extension. -/
def geomConj (E : IntermediateField QT QTbar) (galH : (↥E ≃ₐ[QT] ↥E) ≃* H) (θ : ↥E) (h : H) :
    ↥(geomClosure E) :=
  ⟨((galH.symm h θ : ↥E) : QTbar), le_geomClosure E _ (SetLike.coe_mem _)⟩

@[simp] theorem coe_geomConj (E : IntermediateField QT QTbar) (galH : (↥E ≃ₐ[QT] ↥E) ≃* H)
    (θ : ↥E) (h : H) :
    ((geomConj E galH θ h : ↥(geomClosure E)) : QTbar) = ((galH.symm h θ : ↥E) : QTbar) := rfl

/-- **A conjugate of a transcendental primitive element is transcendental over the constants.**
Conjugation is a field isomorphism, so it preserves transcendence over the rationals, and
transcendence over the rationals upgrades to transcendence over the algebraic numbers. -/
theorem transcendental_geomConj (E : IntermediateField QT QTbar)
    (galH : (↥E ≃ₐ[QT] ↥E) ≃* H) {θ : ↥E} (hθ : Transcendental ℚ θ) (h : H) :
    Transcendental k (geomConj E galH θ h) := by
  have h1 : Transcendental ℚ ((galH.symm h) θ) :=
    transcendental_ringHom (galH.symm h).toAlgHom.toRingHom hθ
  have h2 : Transcendental ℚ (((galH.symm h) θ : ↥E) : QTbar) :=
    transcendental_ringHom (IntermediateField.val E).toRingHom h1
  have h3 : Transcendental k (((galH.symm h) θ : ↥E) : QTbar) := transcendental_const_of_rat h2
  exact fun hx => h3 ((isAlgebraic_algHom_iff (geomVal E) (geomVal_injective E)).mpr hx)

/-- **Two distinct conjugates of a primitive element of a regular extension never differ by a
constant.** -/
theorem sub_geomConj_ne_const (E : IntermediateField QT QTbar) [FiniteDimensional QT ↥E]
    (hregE : algebraicClosure ℚ ↥E = ⊥) (galH : (↥E ≃ₐ[QT] ↥E) ≃* H) {θ : ↥E}
    (hprim : IntermediateField.adjoin QT {θ} = ⊤) {j j' : H} (hne : j ≠ j') (a : k) :
    geomConj E galH θ j' - geomConj E galH θ j - algebraMap k ↥(geomClosure E) a ≠ 0 := by
  intro hzero
  have hgh : galH.symm j' ≠ galH.symm j := by
    intro heq
    have h1 : j' = j := by simpa using congrArg galH heq
    exact hne h1.symm
  refine sub_conj_sub_const_ne_zero_geom (E := E) hregE hprim
    (g := galH.symm j') (h := galH.symm j) hgh a ?_
  have := congrArg (geomVal E) hzero
  rwa [map_sub, map_sub, map_zero, AlgHom.commutes, geomVal_apply, geomVal_apply, coe_geomConj,
    coe_geomConj] at this

/-! ## The exceptional set of intercepts -/

/-- **A rational intercept for which the conjugate radicands are independent.**  The place-counting
argument bounds the bad intercepts by a finite subset of the constants, and the rationals inject
into the constants, so only finitely many rational intercepts are excluded. -/
theorem exists_good_intercept (E : IntermediateField QT QTbar) [FiniteDimensional QT ↥E]
    (hregE : algebraicClosure ℚ ↥E = ⊥) (galH : (↥E ≃ₐ[QT] ↥E) ≃* H) {θ : ↥E}
    (hprim : IntermediateField.adjoin QT {θ} = ⊤) (hθ : Transcendental ℚ θ)
    [Fintype H] [DecidableEq H]
    {r : ℕ} (t : Fin r → k) (hinj : Function.Injective t) (e : Fin r → ℕ)
    {n : ℕ} (hgcd : Nat.gcd n (Finset.univ.gcd e) = 1) :
    ∃ c : ℚ,
      (∀ (h : H) (i : Fin r), geomConj E galH θ h
          + algebraMap k ↥(geomClosure E) (algebraMap ℚ k c)
          - algebraMap k ↥(geomClosure E) (t i) ≠ 0) ∧
        ∀ (m : H → ℤ) (y : ↥(geomClosure E)), y ≠ 0 →
          y ^ n = ∏ h, conjRadicand (geomConj E galH θ) t e (algebraMap ℚ k c) h ^ m h →
          ∀ h, (n : ℤ) ∣ m h := by
  obtain ⟨S, hSfin, hS⟩ := exists_indep_radicands (F := ↥(geomClosure E))
    (geomConj E galH θ) (fun h => transcendental_geomConj E galH hθ h)
    (fun h => finiteDimensional_paramHom (transcendental_geomConj E galH hθ h))
    (fun j j' hjj' a => sub_geomConj_ne_const E hregE galH hprim hjj' a) t hinj e hgcd
  have hTfin : ((algebraMap ℚ k) ⁻¹' S).Finite :=
    hSfin.preimage (Set.injOn_of_injective (algebraMap ℚ k).injective)
  obtain ⟨c, -, hc⟩ := ((Set.infinite_univ (α := ℚ)).diff hTfin).nonempty
  exact ⟨c, hS _ hc⟩

end Rigidity.RET.Wreath

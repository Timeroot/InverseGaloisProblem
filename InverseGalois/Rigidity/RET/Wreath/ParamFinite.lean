/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.LineParam
import InverseGalois.Rigidity.RET.RatFuncGen

/-!
# A second coordinate presents the same finite extension

A finite extension `M / k(T)` is a covering surface of the line, addressed through the coordinate
`T`.  Any other non-constant function `θ ∈ M` addresses the same surface through a different
coordinate: it embeds the line into `M` by `T ↦ θ`, and `M` is again a finite extension of that
copy `k(θ)` of the line.

The reason is that the two coordinates are algebraically dependent.  Clearing denominators in the
algebraic relation satisfied by `θ` over `k(T)` produces a two-variable polynomial killing the pair
`(θ, T)`; reading it as a polynomial in the second slot with coefficients in `k(θ)` — the reading
is nonzero precisely because `θ` is transcendental over `k` — exhibits `T` as algebraic over
`k(θ)`.  Hence `k(θ)(T)` is finite over `k(θ)`, while `M` is finite over `k(θ)(T)` because it is
already finite over the smaller field `k(T)`.

## Main results

* `Rigidity.RET.Wreath.finiteDimensional_of_transcendental_mem` — a subfield of `M` containing the
  constants and a transcendental element has `M` as a finite extension, in the form of the algebra
  structure attached to an embedding of the line.
* `Rigidity.RET.Wreath.finiteDimensional_paramHom` — the line through a transcendental element of
  `M` presents `M` as a finite extension.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET.Wreath

open GeomAKLB (k)

/-! ## Changing the base field of a finite extension -/

section Transfer

variable {K E M : Type*} [Field K] [Field E] [Field M] [Algebra K M] [Algebra E M]

/-- **A finite extension stays finite over a larger base**: if `M` is finite over `K` and every
scalar coming from `K` also comes from `E`, then `M` is finite over `E` as well, since a spanning
family over `K` spans over `E`. -/
theorem finiteDimensional_of_forall_exists [FiniteDimensional K M]
    (h : ∀ c : K, ∃ a : E, algebraMap E M a = algebraMap K M c) : FiniteDimensional E M := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := K) (M := M)
  refine Module.Finite.of_fg_top ⟨s, le_antisymm le_top ?_⟩
  rintro x -
  have hx : x ∈ Submodule.span K (s : Set M) := by rw [hs]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul c a _ ha =>
    obtain ⟨d, hd⟩ := h c
    have hca : c • a = d • a := by rw [Algebra.smul_def, Algebra.smul_def, hd]
    rw [hca]
    exact Submodule.smul_mem _ _ ha

omit [Algebra K M] in
/-- **A finite extension read through an embedding**: if `M` is finite over `E` and every element
of `E` is hit by a ring morphism `ρ` from `K`, then `M` is finite over `K` for the algebra
structure that `ρ` puts on it. -/
theorem finiteDimensional_toAlgebra [FiniteDimensional E M] (ρ : K →+* M)
    (h : ∀ c : E, ∃ f : K, ρ f = algebraMap E M c) :
    @FiniteDimensional K M _ _ (@Algebra.toModule _ _ _ _ ρ.toAlgebra) := by
  letI : Algebra K M := ρ.toAlgebra
  refine finiteDimensional_of_forall_exists (K := E) (E := K) fun c => ?_
  obtain ⟨f, hf⟩ := h c
  exact ⟨f, by rw [RingHom.algebraMap_toAlgebra]; exact hf⟩

end Transfer

/-! ## Reading a two-variable relation through the other variable -/

section Swap

variable {F E : Type*} [Field F] [CommRing E] [Algebra F E]

/-- **The other reading of a two-variable relation is nonzero.**  Substituting a transcendental
element for the outer variable of a nonzero polynomial in two variables, and keeping the inner
variable, leaves a nonzero polynomial: each coefficient of the result is the value at the
transcendental element of a one-variable polynomial recording a row of coefficients. -/
theorem eval₂_mapRingHom_C_ne_zero {θ : E} (hθ : Transcendental F θ) {p : (Polynomial F)[X]}
    (hp : p ≠ 0) : eval₂ (mapRingHom (algebraMap F E)) (C θ) p ≠ 0 := by
  have hinj : Function.Injective (aeval θ : Polynomial F →ₐ[F] E) :=
    transcendental_iff_injective.mp hθ
  intro hzero
  obtain ⟨i, hi⟩ := support_nonempty.mpr hp
  refine mem_support_iff.mp hi (Polynomial.ext fun j => ?_)
  have hsum : eval₂ (mapRingHom (algebraMap F E)) (C θ) p
      = ∑ n ∈ p.support, (p.coeff n).map (algebraMap F E) * C θ ^ n := by
    rw [eval₂_eq_sum, Polynomial.sum_def]
    simp only [coe_mapRingHom]
  have hcoeff : ∑ n ∈ p.support, algebraMap F E ((p.coeff n).coeff j) * θ ^ n = 0 := by
    have h0 : (∑ n ∈ p.support, (p.coeff n).map (algebraMap F E) * C θ ^ n).coeff j = 0 := by
      rw [← hsum, hzero, coeff_zero]
    rw [finset_sum_coeff] at h0
    simpa only [← C_pow, coeff_mul_C, coeff_map] using h0
  have hr : (aeval θ) (∑ n ∈ p.support, C ((p.coeff n).coeff j) * (X : Polynomial F) ^ n)
      = (aeval θ) (0 : Polynomial F) := by
    rw [map_sum, map_zero]
    simpa using hcoeff
  have hr0 := hinj hr
  have hci := congrArg (fun r : Polynomial F => r.coeff i) hr0
  simpa only [finset_sum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, hi, if_true, coeff_zero] using hci

end Swap

/-! ## The line through a transcendental element -/

section Line

variable {F M : Type*} [Field F] [Field M] [Algebra F M] [Algebra (RatFunc F) M]
  [IsScalarTower F (RatFunc F) M] [FiniteDimensional (RatFunc F) M]

/-- **A transcendental element presents a finite extension of the line as a finite extension of
the line it spans.**  If a subfield of `M` given as the image of an embedding `ρ` of the line
contains the constants and a transcendental element, then `M` is a finite extension of the line
read through `ρ`. -/
theorem finiteDimensional_of_transcendental_mem (ρ : RatFunc F →+* M) {θ : M}
    (hθ : Transcendental F θ) (hconst : ∀ c : F, algebraMap F M c ∈ ρ.fieldRange)
    (hmem : θ ∈ ρ.fieldRange) :
    @FiniteDimensional (RatFunc F) M _ _ (@Algebra.toModule _ _ _ _ ρ.toAlgebra) := by
  letI : Algebra (Polynomial F) M :=
    ((algebraMap (RatFunc F) M).comp (algebraMap (Polynomial F) (RatFunc F))).toAlgebra
  haveI : IsScalarTower (Polynomial F) (RatFunc F) M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI := Algebra.IsAlgebraic.of_finite (RatFunc F) M
  -- the line spanned by `θ`, as an intermediate field
  set E : IntermediateField F M := ρ.fieldRange.toIntermediateField hconst with hE
  have hθE : θ ∈ E := hmem
  have htr : Transcendental F (⟨θ, hθE⟩ : E) := fun halg =>
    hθ (IntermediateField.isAlgebraic_iff.mp halg)
  -- the coordinate of the line `M` was presented on
  set t : M := algebraMap (RatFunc F) M RatFunc.X with ht
  -- an algebraic relation between `θ` and `t`, with coefficients in the constants
  obtain ⟨p, hp0, hp⟩ : IsAlgebraic (Polynomial F) θ :=
    (IsFractionRing.isAlgebraic_iff (Polynomial F) (RatFunc F) M).mpr
      (Algebra.IsAlgebraic.isAlgebraic θ)
  -- the same relation, read as a polynomial in `t` over the line spanned by `θ`
  have hcomp : (eval₂RingHom (algebraMap E M) t).comp (mapRingHom (algebraMap F E))
      = algebraMap (Polynomial F) M := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · have h1 : (mapRingHom (algebraMap F E)) (C a) = C (algebraMap F E a) := by simp
      rw [RingHom.comp_apply, h1, coe_eval₂RingHom, eval₂_C]
      show algebraMap E M (algebraMap F E a)
        = algebraMap (RatFunc F) M (algebraMap (Polynomial F) (RatFunc F) (C a))
      rw [← IsScalarTower.algebraMap_apply F E M,
        show algebraMap (Polynomial F) (RatFunc F) (C a) = algebraMap F (RatFunc F) a from by
          rw [IsScalarTower.algebraMap_apply F (Polynomial F) (RatFunc F)]; simp,
        ← IsScalarTower.algebraMap_apply F (RatFunc F) M]
    · have h2 : (mapRingHom (algebraMap F E)) (X : Polynomial F) = X := by simp
      rw [RingHom.comp_apply, h2, coe_eval₂RingHom, eval₂_X]
      show t = algebraMap (RatFunc F) M (algebraMap (Polynomial F) (RatFunc F) X)
      rw [ht]
      simp
  have hqt : aeval t (eval₂ (mapRingHom (algebraMap F E)) (C (⟨θ, hθE⟩ : E)) p) = 0 := by
    show eval₂RingHom (algebraMap E M) t (eval₂ (mapRingHom (algebraMap F E)) _ p) = 0
    rw [Polynomial.hom_eval₂, hcomp]
    show eval₂ (algebraMap (Polynomial F) M) (eval₂ (algebraMap E M) t (C _)) p = 0
    rw [eval₂_C]
    exact hp
  have hint : IsIntegral E t :=
    IsAlgebraic.isIntegral ⟨_, eval₂_mapRingHom_C_ne_zero htr hp0, hqt⟩
  -- `M` is finite over `k(θ)(t)`, which is finite over `k(θ)`
  haveI : FiniteDimensional E (IntermediateField.adjoin E {t}) :=
    IntermediateField.adjoin.finiteDimensional hint
  haveI : FiniteDimensional (IntermediateField.adjoin E {t}) M := by
    refine finiteDimensional_of_forall_exists (K := RatFunc F) fun c => ?_
    have hmemc : algebraMap (RatFunc F) M c ∈ (IntermediateField.adjoin E {t}).toSubfield := by
      refine ratFunc_mem_subfield (algebraMap (RatFunc F) M) _ (fun a => ?_) ?_ c
      · rw [← IsScalarTower.algebraMap_apply F (RatFunc F) M,
          IsScalarTower.algebraMap_apply F E M]
        exact (IntermediateField.adjoin E {t}).algebraMap_mem _
      · exact IntermediateField.subset_adjoin E {t} rfl
    exact ⟨⟨_, hmemc⟩, rfl⟩
  haveI : FiniteDimensional E M := Module.Finite.trans (IntermediateField.adjoin E {t}) M
  refine finiteDimensional_toAlgebra (E := E) ρ fun c => ?_
  obtain ⟨f, hf⟩ := RingHom.mem_fieldRange.mp c.2
  exact ⟨f, hf⟩

end Line

/-- **A transcendental element presents its field as a finite extension of the line it spans**:
`M` is finite over the copy of the line embedded by sending the parameter to `θ`. -/
theorem finiteDimensional_paramHom {M : Type} [Field M] [Algebra k M] [Algebra (RatFunc k) M]
    [IsScalarTower k (RatFunc k) M] [FiniteDimensional (RatFunc k) M] {θ : M}
    (hθ : Transcendental k θ) :
    @FiniteDimensional (RatFunc k) M _ _
      (@Algebra.toModule _ _ _ _ ((paramHom (M := M) θ hθ).toAlgebra)) :=
  finiteDimensional_of_transcendental_mem _ hθ
    (fun c => RingHom.mem_fieldRange.mpr ⟨algebraMap k (RatFunc k) c, paramHom_const hθ c⟩)
    (RingHom.mem_fieldRange.mpr ⟨RatFunc.X, paramHom_X hθ⟩)

end Rigidity.RET.Wreath

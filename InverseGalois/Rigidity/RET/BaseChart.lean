/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.RatFuncGen
import InverseGalois.Rigidity.RET.TamePi1

/-!
# Reading a field over the line through a second parameter

A cover of the line is a finite Galois extension `M / ℚ̄(T)`.  A single field `M` can be an
extension of the line in several ways at once: an embedding `ρ : ℚ̄(T) → M` whose image contains
the original copy of `ℚ̄(T)` presents `M` as a cover of a *second* line, the one whose parameter is
`ρ T`.  The prototype is a Kummer parameter, `u` with `uᵐ = T`.

The second presentation is realized by a type synonym `Chart M ρ`, carrying the same field with the
base acting through `ρ`, exactly as `Rigidity.RET.Twist` does for a change of coordinate.  What is
new here is that `ρ` is only an embedding, not an automorphism, so the two presentations differ:
the image `ρ(ℚ̄(T))` is an intermediate field of `M` over the original base, finite over it, and the
chart is the cover of the line obtained by reading that intermediate field as the base.  All the
data of a cover therefore transfers: the extension stays finite (the intermediate field is finite
over the original base, and `M` is finite over the intermediate field) and stays Galois (an
intermediate field of a Galois extension has the same top).

## Main definitions

* `Rigidity.RET.Chart` — `M` with the base acting through `ρ`.
* `Rigidity.RET.Chart.base` — the image of the second line inside `M`.
* `Rigidity.RET.Chart.deckHom` — a deck transformation of the chart is one of `M`.

## Main results

* `Rigidity.RET.module_finite_of_ringHom_range` — finiteness passes to a larger ring of scalars.
* `Rigidity.RET.Chart.finiteDimensional`, `Rigidity.RET.Chart.isGalois` — the chart is again a
  finite Galois extension of the line.
* `Rigidity.RET.Chart.exists_deckHom_eq` — an automorphism of `M` fixing the chart parameter is a
  deck transformation of the chart.
-/

open Polynomial

noncomputable section


namespace Rigidity.RET

open GeomAKLB

/-! ## Finiteness over a larger ring of scalars -/

/-- **Finiteness passes to a larger ring of scalars**: a finite spanning family over `A` is a
finite spanning family over any `B` acting through a map whose image contains the `A`-scalars. -/
theorem module_finite_of_ringHom_range {A B M : Type*} [CommSemiring A] [CommSemiring B]
    [CommSemiring M] [Algebra A M] [Module.Finite A M] (ψ : B →+* M)
    (h : ∀ a : A, ∃ b : B, ψ b = algebraMap A M a) :
    letI := ψ.toAlgebra; Module.Finite B M := by
  letI := ψ.toAlgebra
  classical
  obtain ⟨s, hsfin, hspan⟩ := Submodule.fg_def.mp (Module.finite_def.mp ‹Module.Finite A M›)
  refine Module.finite_def.mpr (Submodule.fg_def.mpr ⟨s, hsfin, ?_⟩)
  refine eq_top_iff.mpr fun x hxtop => ?_
  clear hxtop
  have hx : x ∈ Submodule.span A s := by rw [hspan]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul a y _ hy =>
      obtain ⟨b, hb⟩ := h a
      have hay : a • y = b • y := by
        rw [Algebra.smul_def, Algebra.smul_def, ← hb]; rfl
      rw [hay]
      exact Submodule.smul_mem _ b hy

/-! ## The subfield of `ℚ̄(T)` on which two maps agree -/

/-- The subfield of `ℚ̄(T)` on which two ring homomorphisms agree. -/
def eqSubfield {M : Type} [Field M] (f g : RatFunc k →+* M) : Subfield (RatFunc k) where
  carrier := {x | f x = g x}
  mul_mem' hx hy := by simp only [Set.mem_setOf_eq, map_mul] at *; rw [hx, hy]
  one_mem' := by simp
  add_mem' hx hy := by simp only [Set.mem_setOf_eq, map_add] at *; rw [hx, hy]
  zero_mem' := by simp
  neg_mem' hx := by simp only [Set.mem_setOf_eq, map_neg] at *; rw [hx]
  inv_mem' x hx := by simp only [Set.mem_setOf_eq, map_inv₀] at *; rw [hx]

/-- **Two ring homomorphisms out of `ℚ̄(T)` agreeing on the constants and on `T` are equal.** -/
theorem ringHom_ext_ratFunc {M : Type} [Field M] {f g : RatFunc k →+* M}
    (hC : ∀ c : k, f (algebraMap k (RatFunc k) c) = g (algebraMap k (RatFunc k) c))
    (hX : f RatFunc.X = g RatFunc.X) (x : RatFunc k) : f x = g x := by
  have h : eqSubfield f g = ⊤ := ratFunc_subfield_eq_top (S := eqSubfield f g) hC hX
  have hx : x ∈ eqSubfield f g := by rw [h]; trivial
  exact hx

/-! ## The chart -/

/-- The field `M`, regarded as an extension of the line through the parameter `ρ T`. -/
def Chart (M : Type) [Field M] (_ρ : RatFunc k →+* M) : Type := M

namespace Chart

variable {M : Type} [Field M] (ρ : RatFunc k →+* M)

instance instField : Field (Chart M ρ) := inferInstanceAs (Field M)

instance instAlgebra : Algebra (RatFunc k) (Chart M ρ) := ρ.toAlgebra

instance instAlgebraPoly : Algebra (Polynomial k) (Chart M ρ) :=
  ((algebraMap (RatFunc k) (Chart M ρ)).comp
    (algebraMap (Polynomial k) (RatFunc k))).toAlgebra

instance instTower : IsScalarTower (Polynomial k) (RatFunc k) (Chart M ρ) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- Scalars act on the chart through `ρ`. -/
theorem algebraMap_apply (f : RatFunc k) :
    (algebraMap (RatFunc k) (Chart M ρ) f : M) = ρ f := rfl

variable [Algebra (RatFunc k) M]

/-- The image of the chart's line inside `M`. -/
def base (hρ : ∀ f : RatFunc k, algebraMap (RatFunc k) M f ∈ ρ.fieldRange) :
    IntermediateField (RatFunc k) M :=
  ρ.fieldRange.toIntermediateField hρ

variable {ρ}

theorem mem_base {hρ : ∀ f : RatFunc k, algebraMap (RatFunc k) M f ∈ ρ.fieldRange} {x : M} :
    x ∈ base ρ hρ ↔ ∃ f : RatFunc k, ρ f = x := Iff.rfl

variable (ρ)

/-- The chart's line is isomorphic to its image in `M`. -/
def baseEquiv (hρ : ∀ f : RatFunc k, algebraMap (RatFunc k) M f ∈ ρ.fieldRange) :
    RatFunc k ≃+* (base ρ hρ) :=
  RingEquiv.ofBijective (ρ.codRestrict (base ρ hρ).toSubfield fun f => ⟨f, rfl⟩)
    ⟨fun x y hxy => ρ.injective (congrArg Subtype.val hxy), fun ⟨x, hx⟩ => by
      obtain ⟨f, hf⟩ := hx
      exact ⟨f, Subtype.ext hf⟩⟩

@[simp] theorem baseEquiv_apply
    (hρ : ∀ f : RatFunc k, algebraMap (RatFunc k) M f ∈ ρ.fieldRange) (f : RatFunc k) :
    ((baseEquiv ρ hρ f : (base ρ hρ)) : M) = ρ f := rfl

section Instances

variable [FiniteDimensional (RatFunc k) M] [IsGalois (RatFunc k) M]
  (hρ : ∀ f : RatFunc k, algebraMap (RatFunc k) M f ∈ ρ.fieldRange)

omit [IsGalois (RatFunc k) M] in
/-- `M` is finite over the chart's line inside it. -/
theorem finite_base : Module.Finite (base ρ hρ) M :=
  Module.Finite.of_restrictScalars_finite (RatFunc k) (base ρ hρ) M

omit [FiniteDimensional (RatFunc k) M] in
/-- `M` is Galois over the chart's line inside it. -/
theorem isGalois_base : IsGalois (base ρ hρ) M :=
  IsGalois.tower_top_of_isGalois (RatFunc k) (base ρ hρ) M

omit [IsGalois (RatFunc k) M] in
/-- **The chart is again a finite extension of the line.** -/
theorem finiteDimensional
    (hρ : ∀ f : RatFunc k, algebraMap (RatFunc k) M f ∈ ρ.fieldRange) :
    FiniteDimensional (RatFunc k) (Chart M ρ) := by
  haveI := finite_base ρ hρ
  exact module_finite_of_ringHom_range (A := (base ρ hρ)) (B := RatFunc k) (M := M) ρ
    fun a => ⟨(baseEquiv ρ hρ).symm a, congrArg (fun y : (base ρ hρ) => (y : M))
      ((baseEquiv ρ hρ).apply_symm_apply a)⟩

/-- **The chart is again a Galois extension of the line.** -/
theorem isGalois (hρ : ∀ f : RatFunc k, algebraMap (RatFunc k) M f ∈ ρ.fieldRange) :
    IsGalois (RatFunc k) (Chart M ρ) := by
  haveI := finite_base ρ hρ
  haveI := isGalois_base ρ hρ
  haveI : Algebra.IsAlgebraic (base ρ hρ) M := Algebra.IsAlgebraic.of_finite _ _
  refine IsGalois.of_equiv_equiv (F := (base ρ hρ)) (E := M) (M := RatFunc k)
    (N := Chart M ρ) (f := (baseEquiv ρ hρ).symm) (g := RingEquiv.refl M) ?_
  ext x
  obtain ⟨f, rfl⟩ := (baseEquiv ρ hρ).surjective x
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom,
    RingEquiv.symm_apply_apply]
  rfl

end Instances

/-! ## Deck transformations of the chart -/

section Deck

variable (hρ : ∀ f : RatFunc k, algebraMap (RatFunc k) M f ∈ ρ.fieldRange)

/-- **A deck transformation of the chart is one of `M`**: it is a ring automorphism of `M` fixing
the chart's line, which contains the original line. -/
def deckHom : (Chart M ρ ≃ₐ[RatFunc k] Chart M ρ) →* (M ≃ₐ[RatFunc k] M) where
  toFun τ :=
    { (τ.toRingEquiv : M ≃+* M) with
      commutes' := fun f => by
        obtain ⟨g, hg⟩ := hρ f
        show τ.toRingEquiv (algebraMap (RatFunc k) M f) = algebraMap (RatFunc k) M f
        rw [← hg]
        exact τ.commutes g }
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

@[simp] theorem deckHom_apply (τ : Chart M ρ ≃ₐ[RatFunc k] Chart M ρ) (x : M) :
    deckHom ρ hρ τ x = τ x := rfl

theorem deckHom_injective : Function.Injective (deckHom ρ hρ) := fun _ _ h =>
  AlgEquiv.ext fun x => congrArg (fun e : M ≃ₐ[RatFunc k] M => e x) h

/-- **An automorphism of `M` fixing the chart parameter is a deck transformation of the chart**:
the elements it fixes form a subfield, and a subfield of `ℚ̄(T)` containing the constants and the
parameter is everything. -/
theorem exists_deckHom_eq (hC : ∀ c : k, ρ (algebraMap k (RatFunc k) c)
      = algebraMap (RatFunc k) M (algebraMap k (RatFunc k) c))
    (τ : M ≃ₐ[RatFunc k] M) (hu : τ (ρ RatFunc.X) = ρ RatFunc.X) :
    ∃ τ' : Chart M ρ ≃ₐ[RatFunc k] Chart M ρ, deckHom ρ hρ τ' = τ := by
  have hfix : ∀ f : RatFunc k, τ (ρ f) = ρ f := by
    refine ringHom_ext_ratFunc (f := (τ.toRingEquiv : M ≃+* M).toRingHom.comp ρ) (g := ρ) ?_ hu
    intro c
    show τ (ρ (algebraMap k (RatFunc k) c)) = ρ (algebraMap k (RatFunc k) c)
    rw [hC c]
    exact τ.commutes _
  refine ⟨{ (τ.toRingEquiv : Chart M ρ ≃+* Chart M ρ) with
    commutes' := fun f => hfix f }, ?_⟩
  ext x
  rfl

end Deck

end Chart

end Rigidity.RET

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.DeltaShift

/-!
# The connecting map of a split extension is a map out of the coshift

An extension whose quotient is a direct summand of its middle term, as a module, can be compared
with the sequence defining the coshift of the quotient: a section of the projection is summed over
the group after undoing the translation, which produces a map of the functions on the group with
values in the quotient into the middle term, compatible with the projections because the section
is one.  The map of the kernels of the two summations is then a map of the sub of the sequence
defining the coshift into the sub of the extension, and the comparison it assembles is the identity
on the quotient.

Since the connecting map of a map of short exact sequences commutes with the maps of the terms, and
since the connecting map of the sequence defining the coshift is by construction the identification
of the complete cohomology of the quotient with that of its coshift one degree higher, the
connecting map of such an extension is that identification followed by the map induced on the subs.
No connecting map is left in the expression, which is what makes it possible to compare it with any
operation already known to commute with the maps induced by a morphism.

The extension used to compare Tate with Nakayama is of this kind, its middle term being a product,
so its connecting map, and with it the whole comparison, is expressed this way.

## Main results

* `InverseGalois.CFT.Tate.tateδ_eq_tateCoshiftEquiv`: **the connecting map of an extension admitting
  a comparison from the sequence defining the coshift of its quotient which is the identity there is
  the identification of the coshift followed by the induced map.**
* `InverseGalois.CFT.Tate.traceSeqHom`: the comparison attached to a section of the projection.
* `InverseGalois.CFT.Tate.tateNakayamaMap_eq_coshift`: **the comparison of Tate and Nakayama
  expressed with the identification of the coshift and no connecting map.**

## Tags

Tate cohomology, connecting homomorphism, dimension shifting, Tate-Nakayama
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

open scoped TensorProduct

universe u

noncomputable section

/-! ### A comparison from the sequence defining the coshift -/

section General

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

/-- **The connecting map of an extension comparing with the sequence defining the coshift is the
identification of the coshift followed by the induced map.** -/
theorem tateδ_eq_tateCoshiftEquiv {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    (ψ : coshiftSeq X.X₃ ⟶ X) (hψ : ψ.τ₃ = 𝟙 X.X₃) (n : ℤ) (x : ↥(tateModule X.X₃ n)) :
    tateδ hX n x = tateMap ψ.τ₁ (n + 1) (tateCoshiftEquiv X.X₃ n x) := by
  have h := tateδ_naturality_apply (coshiftSeq_shortExact X.X₃) hX ψ n x
  rw [hψ] at h
  exact (h.trans (congrArg (fun y => tateδ hX n y) (tateMap_id_apply X.X₃ n x))).symm

end General

/-! ### The trace of a section -/

section Trace

variable {k G : Type u} [CommRing k] [Group G] [Finite G]
  {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (s : ↥X.X₃.V →ₗ[k] ↥X.X₂.V)
  (hs : ∀ v : ↥X.X₃.V, X.g.hom.hom (s v) = v)

/-- **The trace of a section of an extension**: the values of a function on the group are lifted
and summed after undoing the translation. -/
def traceMid : ↥(indObj X.X₃).V →ₗ[k] ↥X.X₂.V := augMap X.X₂.ρ ∘ₗ s.compLeft G

theorem traceMid_equivariant (g : G) :
    traceMid s ∘ₗ (indObj X.X₃).ρ g = X.X₂.ρ g ∘ₗ traceMid s := by
  refine LinearMap.ext fun f => ?_
  have h1 : (s.compLeft G) ((indObj X.X₃).ρ g f)
      = inducedRep k G ↥X.X₂.V g ((s.compLeft G) f) := rfl
  show augMap X.X₂.ρ ((s.compLeft G) ((indObj X.X₃).ρ g f))
    = X.X₂.ρ g (augMap X.X₂.ρ ((s.compLeft G) f))
  rw [h1]
  exact LinearMap.congr_fun (augMap_comp_inducedRep X.X₂.ρ g) ((s.compLeft G) f)

include hs in
/-- **The trace of a section is compatible with the two projections.** -/
theorem hom_traceMid (f : ↥(indObj X.X₃).V) :
    X.g.hom.hom (traceMid s f) = augMap X.X₃.ρ f := by
  letI := Fintype.ofFinite G
  show X.g.hom.hom (augMap X.X₂.ρ ((s.compLeft G) f)) = augMap X.X₃.ρ f
  rw [augMap_apply X.X₂.ρ, augMap_apply X.X₃.ρ, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine (LinearMap.congr_fun (hom_equivariant X.g x⁻¹) (s (f x))).trans ?_
  rw [LinearMap.comp_apply, hs]

include hX hs in
theorem traceMid_mem_range (w : ↥(coshiftObj X.X₃).V) :
    traceMid s ((LinearMap.ker (augMap X.X₃.ρ)).subtype w)
      ∈ LinearMap.range X.f.hom.hom := by
  rw [shortExact_range_eq_ker hX, LinearMap.mem_ker, hom_traceMid s hs]
  exact w.2

/-- **The trace of a section read on the two subs.** -/
def traceSub : ↥(coshiftObj X.X₃).V →ₗ[k] ↥X.X₁.V :=
  (LinearEquiv.ofInjective X.f.hom.hom (shortExact_injective hX)).symm.toLinearMap ∘ₗ
    (traceMid s ∘ₗ (LinearMap.ker (augMap X.X₃.ρ)).subtype).codRestrict
      (LinearMap.range X.f.hom.hom) (traceMid_mem_range hX s hs)

theorem f_traceSub (w : ↥(coshiftObj X.X₃).V) :
    X.f.hom.hom (traceSub hX s hs w)
      = traceMid s ((LinearMap.ker (augMap X.X₃.ρ)).subtype w) := by
  show X.f.hom.hom ((LinearEquiv.ofInjective X.f.hom.hom (shortExact_injective hX)).symm
    (⟨traceMid s ((LinearMap.ker (augMap X.X₃.ρ)).subtype w),
      traceMid_mem_range hX s hs w⟩ : LinearMap.range X.f.hom.hom)) = _
  exact LinearEquiv.ofInjective_symm_apply _ _

theorem traceSub_equivariant (g : G) :
    traceSub hX s hs ∘ₗ (coshiftObj X.X₃).ρ g = X.X₁.ρ g ∘ₗ traceSub hX s hs := by
  refine LinearMap.ext fun w => shortExact_injective hX ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  have h1 : X.f.hom.hom (traceSub hX s hs ((coshiftObj X.X₃).ρ g w))
      = traceMid s ((indObj X.X₃).ρ g ((LinearMap.ker (augMap X.X₃.ρ)).subtype w)) :=
    f_traceSub hX s hs _
  have h2 : X.f.hom.hom (X.X₁.ρ g (traceSub hX s hs w))
      = X.X₂.ρ g (traceMid s ((LinearMap.ker (augMap X.X₃.ρ)).subtype w)) :=
    (LinearMap.congr_fun (hom_equivariant X.f g) (traceSub hX s hs w)).trans
      (congrArg (X.X₂.ρ g) (f_traceSub hX s hs w))
  rw [h1, h2]
  exact LinearMap.congr_fun (traceMid_equivariant s g) _

/-- **The trace of a section as a map of the middle terms.** -/
def traceMidHom : indObj X.X₃ ⟶ X.X₂ := mkHom (traceMid s) (traceMid_equivariant s)

/-- **The trace of a section as a map of the subs.** -/
def traceSubHom : coshiftObj X.X₃ ⟶ X.X₁ :=
  mkHom (traceSub hX s hs) (traceSub_equivariant hX s hs)

/-- **The comparison of the sequence defining the coshift of the quotient with the extension**
attached to a section of the projection. -/
def traceSeqHom : coshiftSeq X.X₃ ⟶ X where
  τ₁ := traceSubHom hX s hs
  τ₂ := traceMidHom s
  τ₃ := 𝟙 X.X₃
  comm₁₂ := Action.hom_ext _ _ (ModuleCat.hom_ext (LinearMap.ext (f_traceSub hX s hs)))
  comm₂₃ := Action.hom_ext _ _ (ModuleCat.hom_ext (LinearMap.ext (hom_traceMid s hs)))

/-- **The connecting map of an extension whose projection has a section is the identification of the
coshift followed by the trace of the section.** -/
theorem tateδ_eq_traceSub (n : ℤ) (x : ↥(tateModule X.X₃ n)) :
    tateδ hX n x = tateMap (traceSubHom hX s hs) (n + 1) (tateCoshiftEquiv X.X₃ n x) :=
  tateδ_eq_tateCoshiftEquiv hX (traceSeqHom hX s hs) rfl n x

end Trace

/-! ### The tensored extension -/

section Cocycle

variable {k G : Type u} [CommRing k] [Group G] [Finite G]
  (A : Rep k G) (b : groupCohomology.cocycles₁ A) (M : Rep k G)

/-- **The section of the tensored extension.** -/
def cocycleTensorInr : ↥M.V →ₗ[k] ↥(cocycleTensorObj A b M).V :=
  LinearMap.inr k (↥A.V ⊗[k] ↥M.V) ↥M.V

omit [Finite G] in
theorem cocycleTensorSnd_inr (m : ↥M.V) :
    (cocycleTensorSeq A b M).g.hom.hom (cocycleTensorInr A b M m) = m := rfl

/-- **The trace of the section of the tensored extension.** -/
def cocycleCoshiftHom : coshiftObj M ⟶ tensorObj A M :=
  traceSubHom (X := cocycleTensorSeq A b M) (cocycleTensorSeq_shortExact A b M)
    (cocycleTensorInr A b M) (cocycleTensorSnd_inr A b M)

/-- **The connecting map of the tensored extension is the identification of the coshift followed by
the trace of the section.** -/
theorem tateδ_cocycleTensorSeq_eq_coshift (n : ℤ) (x : ↥(tateModule M n)) :
    tateδ (cocycleTensorSeq_shortExact A b M) n x
      = tateMap (cocycleCoshiftHom A b M) (n + 1) (tateCoshiftEquiv M n x) :=
  tateδ_eq_traceSub (cocycleTensorSeq_shortExact A b M) (cocycleTensorInr A b M)
    (cocycleTensorSnd_inr A b M) n x

end Cocycle

/-! ### The comparison of Tate and Nakayama -/

section Nakayama

variable {k G : Type u} [CommRing k] [Group G] [Finite G]
  (A : Rep k G) (b : groupCohomology.cocycles₁ (shiftObj A)) (M : Rep k G)

/-- **The first half of the comparison of Tate and Nakayama is the identification of the coshift
followed by an induced map.** -/
theorem tateNakayamaShiftMap_eq_coshift (n : ℤ) (x : ↥(tateModule M n)) :
    tateNakayamaShiftMap A b M n x
      = tateMap (cocycleCoshiftHom (shiftObj A) b M) (n + 1) (tateCoshiftEquiv M n x) :=
  tateδ_cocycleTensorSeq_eq_coshift (shiftObj A) b M n x

/-- **The comparison of Tate and Nakayama is a composite of induced maps and the two
identifications of degree, with no connecting map.** -/
theorem tateNakayamaMap_eq_coshift (n : ℤ) (x : ↥(tateModule M n)) :
    tateNakayamaMap A b M n x
      = tateShiftEquiv (tensorObj A M) (n + 1)
        (tateMap (shiftTensorIso A M).hom (n + 1)
          (tateMap (cocycleCoshiftHom (shiftObj A) b M) (n + 1) (tateCoshiftEquiv M n x))) := by
  show (tateShiftEquiv (tensorObj A M) (n + 1))
      ((tateMap (shiftTensorIso A M).hom (n + 1)).hom ((tateNakayamaShiftMap A b M n).hom x)) = _
  rw [tateNakayamaShiftMap_eq_coshift A b M n x]

end Nakayama

end

end InverseGalois.CFT.Tate

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.CohomTrivial
import InverseGalois.CFT.TateCohomology.TensorRight
import InverseGalois.CFT.TateCohomology.TensorTrivial

/-!
# The first derived tensor product and the correction to Tate and Nakayama

Tensoring a representation with a presentation of the coefficients is right exact but not exact:
the map from the sub of the presentation into the middle need no longer be injective, and its
kernel is **the first derived tensor product**.  Nothing else is lost, so the four terms

`0 → Tor → A ⊗ R → A ⊗ F → A ⊗ W → 0`

are exact, and cutting them at the image of the middle map gives two short exact sequences with
`A ⊗ R` and `A ⊗ F` in the middle.

When `A` has no complete cohomology after tensoring with a flat representation — which is what
cohomological triviality on every Sylow subgroup supplies, and `R` and `F` are flat because a
presentation may be taken by free modules — both middle terms are acyclic, so both connecting maps
are bijective.  Running them one after the other, **the complete cohomology of `A ⊗ W` in a degree
is the complete cohomology of the first derived tensor product two degrees higher.**

This is exactly the correction term in the theorem of Tate and Nakayama with coefficients that are
not flat: the theorem computes the cohomology of `A ⊗ W`, and the discrepancy between that and the
cohomology of `W` shifted by two is carried by `Tor`.  For a class formation and coefficients killed
by a prime, `Tor` is the group of elements of the formation killed by the prime, tensored with the
coefficients, and that group is computed place by place.

## Main definitions

* `InverseGalois.CFT.Tate.torCycleObj`: the vectors of the tensor product with the middle term of
  the presentation which die in the quotient.
* `InverseGalois.CFT.Tate.torObj`: **the first derived tensor product** of a representation with the
  quotient of a presentation.
* `InverseGalois.CFT.Tate.torSeq`, `InverseGalois.CFT.Tate.torCycleSeq`: the two short exact
  sequences into which the four term sequence is cut.

## Main results

* `InverseGalois.CFT.Tate.subsingleton_torObj`: the first derived tensor product of a flat
  representation vanishes.
* `InverseGalois.CFT.Tate.torCycleShiftEquiv`, `InverseGalois.CFT.Tate.torShiftEquiv`: **each of
  the two sequences shifts the degree by one** when the tensor products with the presentation have
  no complete cohomology.
* `InverseGalois.CFT.Tate.tensorTorEquiv`: **the complete cohomology of the tensor product with the
  quotient of a presentation is the complete cohomology of the first derived tensor product two
  degrees higher.**
* `InverseGalois.CFT.Tate.tensorTorEquivOfSylow`: the same statement over the integers, with the
  hypotheses supplied by cohomological triviality on every Sylow subgroup and flatness of the
  presentation.

## Tags

Tate cohomology, tensor product, derived tensor product, dimension shifting, Tate-Nakayama
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

open scoped TensorProduct

universe u

noncomputable section

/-! ### Cutting the four term sequence in two -/

section Objects

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G) (Y : ShortComplex (Rep k G))

/-- **The vectors of the tensor product with the middle term of a presentation which die in the
quotient.** -/
def torCycleObj : Rep k G := kerObj (tensorHomRight A Y.g)

/-- The image of the tensor product with the sub lands in the vectors dying in the quotient. -/
theorem tensorHomRight_apply_mem_ker (x : ↥(tensorObj A Y.X₁).V) :
    (tensorHomRight A Y.f).hom.hom x ∈ LinearMap.ker (tensorHomRight A Y.g).hom.hom :=
  LinearMap.mem_ker.mpr
    (congrArg (fun φ : tensorObj A Y.X₁ ⟶ tensorObj A Y.X₃ => φ.hom.hom x)
      (tensorSeqRight A Y).zero)

/-- The tensor product with the sub of a presentation, mapping into the vectors dying in the
quotient. -/
def torCorestrictLinear : ↥(tensorObj A Y.X₁).V →ₗ[k] ↥(torCycleObj A Y).V :=
  LinearMap.codRestrict _ (tensorHomRight A Y.f).hom.hom (tensorHomRight_apply_mem_ker A Y)

theorem torCorestrictLinear_equivariant (g : G) :
    torCorestrictLinear A Y ∘ₗ (tensorObj A Y.X₁).ρ g
      = (torCycleObj A Y).ρ g ∘ₗ torCorestrictLinear A Y :=
  LinearMap.ext fun x =>
    Subtype.ext (LinearMap.congr_fun (hom_equivariant (tensorHomRight A Y.f) g) x)

/-- **The tensor product with the sub of a presentation, corestricted to the vectors dying in the
quotient.** -/
def torCorestrict : tensorObj A Y.X₁ ⟶ torCycleObj A Y :=
  mkHom (torCorestrictLinear A Y) (torCorestrictLinear_equivariant A Y)

/-- **The first derived tensor product** of a representation with the quotient of a presentation:
what is lost when the tensor product is applied to the sub of the presentation. -/
def torObj : Rep k G := kerObj (torCorestrict A Y)

variable {Y}

/-- The corestriction is surjective, because the tensor product is right exact. -/
theorem torCorestrict_surjective (hY : Y.ShortExact) :
    Function.Surjective (torCorestrict A Y).hom.hom := by
  rintro ⟨x, hx⟩
  obtain ⟨y, hy⟩ := exists_tensorHomRight_eq A hY x (LinearMap.mem_ker.mp hx)
  exact ⟨y, Subtype.ext hy⟩

/-- **The first derived tensor product of a flat representation vanishes.** -/
theorem subsingleton_torObj [Module.Flat k ↥A.V] (hY : Y.ShortExact) :
    Subsingleton ↥(torObj A Y).V := by
  have hinj : Function.Injective (torCorestrict A Y).hom.hom := fun x y hxy =>
    Module.Flat.lTensor_preserves_injective_linearMap _ (shortExact_injective hY)
      (congrArg Subtype.val hxy)
  refine ⟨fun x y => Subtype.ext (hinj ?_)⟩
  rw [LinearMap.mem_ker.mp x.2, LinearMap.mem_ker.mp y.2]

end Objects

/-! ### The two short exact sequences -/

section Sequences

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G) {Y : ShortComplex (Rep k G)}

/-- **The vectors dying in the quotient, the tensor product with the middle term, and the tensor
product with the quotient.** -/
def torCycleSeq : ShortComplex (Rep k G) := kerSeq (tensorHomRight A Y.g)

/-- **The first derived tensor product, the tensor product with the sub, and the vectors dying in
the quotient.** -/
def torSeq : ShortComplex (Rep k G) := kerSeq (torCorestrict A Y)

theorem torCycleSeq_shortExact (hY : Y.ShortExact) : (torCycleSeq A (Y := Y)).ShortExact :=
  kerSeq_shortExact _ (tensorHomRight_surjective A hY)

theorem torSeq_shortExact (hY : Y.ShortExact) : (torSeq A (Y := Y)).ShortExact :=
  kerSeq_shortExact _ (torCorestrict_surjective A hY)

end Sequences

/-! ### The two shifts of the degree -/

section Shift

variable {k G : Type u} [CommRing k] [Group G] [Finite G] (A : Rep k G)
  {Y : ShortComplex (Rep k G)} (hY : Y.ShortExact)
  (h₁ : ∀ n : ℤ, Limits.IsZero (tateModule (tensorObj A Y.X₁) n))
  (h₂ : ∀ n : ℤ, Limits.IsZero (tateModule (tensorObj A Y.X₂) n))

include hY

include h₂ in
/-- **The complete cohomology of the tensor product with the quotient of a presentation in a degree
is the complete cohomology of the vectors dying in that quotient in the following degree**, when the
tensor product with the middle term of the presentation has none. -/
def torCycleShiftEquiv (n : ℤ) :
    ↥(tateModule (tensorObj A Y.X₃) n) ≃ₗ[k] ↥(tateModule (torCycleObj A Y) (n + 1)) :=
  LinearEquiv.ofBijective (tateδ (torCycleSeq_shortExact A hY) n).hom
    (bijective_tateδ (torCycleSeq_shortExact A hY) n (h₂ n) (h₂ (n + 1)))

include h₁ in
/-- **The complete cohomology of the vectors dying in the quotient of a presentation in a degree is
the complete cohomology of the first derived tensor product in the following degree**, when the
tensor product with the sub of the presentation has none. -/
def torShiftEquiv (n : ℤ) :
    ↥(tateModule (torCycleObj A Y) n) ≃ₗ[k] ↥(tateModule (torObj A Y) (n + 1)) :=
  LinearEquiv.ofBijective (tateδ (torSeq_shortExact A hY) n).hom
    (bijective_tateδ (torSeq_shortExact A hY) n (h₁ n) (h₁ (n + 1)))

include h₁ h₂ in
/-- **The complete cohomology of the tensor product with the quotient of a presentation in a degree
is the complete cohomology of the first derived tensor product two degrees higher**, when the tensor
products with the sub and with the middle term of the presentation have none. -/
def tensorTorEquiv (n : ℤ) :
    ↥(tateModule (tensorObj A Y.X₃) n) ≃ₗ[k] ↥(tateModule (torObj A Y) (n + 1 + 1)) :=
  (torCycleShiftEquiv A hY h₂ n).trans (torShiftEquiv A hY h₁ (n + 1))

include h₁ h₂ in
/-- **The tensor product with the quotient of a presentation has no complete cohomology in a degree
in which the first derived tensor product has none two degrees higher.** -/
theorem isZero_tateModule_tensorObj_X₃ (n : ℤ)
    (ht : Limits.IsZero (tateModule (torObj A Y) (n + 1 + 1))) :
    Limits.IsZero (tateModule (tensorObj A Y.X₃) n) :=
  isZero_of_forall_eq_zero fun x =>
    (tensorTorEquiv A hY h₁ h₂ n).injective
      (by rw [map_zero]; exact eq_zero_of_isZero ht _)

include h₁ h₂ in
/-- **The first derived tensor product has no complete cohomology two degrees above a degree in
which the tensor product with the quotient of the presentation has none.** -/
theorem isZero_tateModule_torObj (n : ℤ)
    (hq : Limits.IsZero (tateModule (tensorObj A Y.X₃) n)) :
    Limits.IsZero (tateModule (torObj A Y) (n + 1 + 1)) :=
  isZero_of_forall_eq_zero fun y => by
    obtain ⟨x, rfl⟩ := (tensorTorEquiv A hY h₁ h₂ n).surjective y
    rw [eq_zero_of_isZero hq x, map_zero]

end Shift

/-! ### Cohomological triviality on the Sylow subgroups -/

section Sylow

variable {G : Type} [Group G] [Finite G] (A : Rep ℤ G) {Y : ShortComplex (Rep ℤ G)}

/-- **The complete cohomology of the tensor product with the quotient of a flat presentation in a
degree is the complete cohomology of the first derived tensor product two degrees higher**, for a
representation over the integers whose restriction to a Sylow subgroup for every prime has no
complete cohomology in two consecutive degrees. -/
def tensorTorEquivOfSylow (hY : Y.ShortExact) (h₁ : Module.Flat ℤ ↥Y.X₁.V)
    (h₂ : Module.Flat ℤ ↥Y.X₂.V)
    (hA : ∀ q : ℕ, q.Prime → ∀ P : Sylow q G, ∃ i : ℤ,
      Limits.IsZero (tateModule (resObj (P : Subgroup G) A) i) ∧
        Limits.IsZero (tateModule (resObj (P : Subgroup G) A) (i + 1))) (n : ℤ) :
    ↥(tateModule (tensorObj A Y.X₃) n) ≃ₗ[ℤ] ↥(tateModule (torObj A Y) (n + 1 + 1)) :=
  tensorTorEquiv A hY (fun m => isZero_tateModule_tensorObj A Y.X₁ h₁ hA m)
    (fun m => isZero_tateModule_tensorObj A Y.X₂ h₂ hA m) n

end Sylow

end

end InverseGalois.CFT.Tate

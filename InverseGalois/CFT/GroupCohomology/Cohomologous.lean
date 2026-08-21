import Mathlib
import InverseGalois.CFT.GroupCohomology.Classification

/-!
# Cohomologous multiplicative `2`-cocycles

Let `G` be a group acting on an abelian group `M` by group automorphisms.  Mathlib records the
multiplicative `2`-cocycle and `2`-coboundary conditions as the predicates
`IsMulCocycle₂` and `IsMulCoboundary₂`, and turns a multiplicative cocycle into an element of
the additive submodule `groupCohomology.cocycles₂ (Rep.ofMulDistribMulAction G M)` via
`groupCohomology.cocyclesOfIsMulCocycle₂`.

This file provides the dictionary between equality of the resulting classes in
`groupCohomology.H2` and the elementary statement that the two cocycles are *cohomologous*,
i.e. that their pointwise quotient is a multiplicative `2`-coboundary.

## Main results

* `InverseGalois.CFT.Cohomologous.isMulCocycle₂_mul`,
  `InverseGalois.CFT.Cohomologous.isMulCocycle₂_inv` and
  `InverseGalois.CFT.Cohomologous.isMulCocycle₂_div`: the multiplicative `2`-cocycles form a
  subgroup of the group of functions `G × G → M`.
* `InverseGalois.CFT.Cohomologous.cocyclesOfIsMulCocycle₂_sub`: the difference of the additive
  cocycles attached to `f` and `f'` is the additive cocycle attached to the pointwise quotient
  `f / f'`.
* `InverseGalois.CFT.H2π_eq_zero_iff_isMulCoboundary₂`: the class of a multiplicative `2`-cocycle
  vanishes exactly when it is a multiplicative `2`-coboundary.
* `InverseGalois.CFT.H2π_eq_H2π_iff_isMulCoboundary₂_div`: two multiplicative `2`-cocycles have
  the same class in `H²` exactly when their pointwise quotient is a multiplicative
  `2`-coboundary.
* `InverseGalois.CFT.H2π_eq_H2π_iff_exists` and
  `InverseGalois.CFT.H2π_eq_H2π_iff_exists'`: the same criterion spelled out as the existence of
  an explicit `1`-cochain `c : G → M` rescaling one cocycle into the other, in either
  orientation.
-/

namespace InverseGalois.CFT

open groupCohomology

namespace Cohomologous

variable {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]

/-! ### The group of multiplicative `2`-cocycles -/

/-- The pointwise product of two multiplicative `2`-cocycles is a multiplicative `2`-cocycle. -/
theorem isMulCocycle₂_mul {f f' : G × G → M} (hf : IsMulCocycle₂ f) (hf' : IsMulCocycle₂ f') :
    IsMulCocycle₂ (fun p : G × G => f p * f' p) := by
  intro g h j
  simp only [smul_mul']
  rw [mul_mul_mul_comm (f (g * h, j)), hf g h j, hf' g h j, mul_mul_mul_comm (g • f (h, j))]

/-- The pointwise inverse of a multiplicative `2`-cocycle is a multiplicative `2`-cocycle. -/
theorem isMulCocycle₂_inv {f : G × G → M} (hf : IsMulCocycle₂ f) :
    IsMulCocycle₂ (fun p : G × G => (f p)⁻¹) := by
  intro g h j
  simp only [smul_inv']
  rw [← mul_inv, ← mul_inv, hf g h j]

/-- The pointwise quotient of two multiplicative `2`-cocycles is a multiplicative `2`-cocycle. -/
theorem isMulCocycle₂_div {f f' : G × G → M} (hf : IsMulCocycle₂ f) (hf' : IsMulCocycle₂ f') :
    IsMulCocycle₂ (fun p : G × G => f p / f' p) := by
  simpa only [div_eq_mul_inv] using isMulCocycle₂_mul hf (isMulCocycle₂_inv hf')

/-- The pointwise product of two multiplicative `2`-coboundaries is a multiplicative
`2`-coboundary. -/
theorem isMulCoboundary₂_mul {f f' : G × G → M} (hf : IsMulCoboundary₂ f)
    (hf' : IsMulCoboundary₂ f') : IsMulCoboundary₂ (fun p : G × G => f p * f' p) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨c', hc'⟩ := hf'
  refine ⟨fun g => c g * c' g, fun g h => ?_⟩
  show g • (c h * c' h) / (c (g * h) * c' (g * h)) * (c g * c' g) = f (g, h) * f' (g, h)
  rw [← hc g h, ← hc' g h, smul_mul', mul_div_mul_comm, mul_mul_mul_comm]

/-- The pointwise inverse of a multiplicative `2`-coboundary is a multiplicative
`2`-coboundary. -/
theorem isMulCoboundary₂_inv {f : G × G → M} (hf : IsMulCoboundary₂ f) :
    IsMulCoboundary₂ (fun p : G × G => (f p)⁻¹) := by
  obtain ⟨c, hc⟩ := hf
  refine ⟨fun g => (c g)⁻¹, fun g h => ?_⟩
  show g • (c h)⁻¹ / (c (g * h))⁻¹ * (c g)⁻¹ = (f (g, h))⁻¹
  rw [← hc g h, smul_inv']
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_inv]
  abel

/-- The pointwise quotient of two multiplicative `2`-coboundaries is a multiplicative
`2`-coboundary. -/
theorem isMulCoboundary₂_div {f f' : G × G → M} (hf : IsMulCoboundary₂ f)
    (hf' : IsMulCoboundary₂ f') : IsMulCoboundary₂ (fun p : G × G => f p / f' p) := by
  simpa only [div_eq_mul_inv] using isMulCoboundary₂_mul hf (isMulCoboundary₂_inv hf')

/-! ### Compatibility with the additive picture -/

/-- Subtraction of the additive `2`-cocycles attached to two multiplicative `2`-cocycles is the
additive `2`-cocycle attached to their pointwise quotient. -/
theorem cocyclesOfIsMulCocycle₂_sub {f f' : G × G → M} (hf : IsMulCocycle₂ f)
    (hf' : IsMulCocycle₂ f') :
    cocyclesOfIsMulCocycle₂ hf - cocyclesOfIsMulCocycle₂ hf'
      = cocyclesOfIsMulCocycle₂ (isMulCocycle₂_div hf hf') :=
  Subtype.ext rfl

end Cohomologous

open Cohomologous

variable {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]

/-! ### The dictionary -/

/-- The class in `H²` of a multiplicative `2`-cocycle vanishes if and only if the cocycle is a
multiplicative `2`-coboundary. -/
theorem H2π_eq_zero_iff_isMulCoboundary₂ {f : G × G → M} (hf : IsMulCocycle₂ f) :
    H2π (Rep.ofMulDistribMulAction G M) (cocyclesOfIsMulCocycle₂ hf) = 0 ↔
      IsMulCoboundary₂ f := by
  rw [H2π_eq_zero_iff]
  exact ⟨fun h => isMulCoboundary₂_of_mem_coboundaries₂ _ h,
    fun h => (coboundariesOfIsMulCoboundary₂ h).2⟩

/-- Two multiplicative `2`-cocycles define the same class in `H²` if and only if their pointwise
quotient is a multiplicative `2`-coboundary. -/
theorem H2π_eq_H2π_iff_isMulCoboundary₂_div {f f' : G × G → M}
    (hf : IsMulCocycle₂ f) (hf' : IsMulCocycle₂ f') :
    H2π (Rep.ofMulDistribMulAction G M) (cocyclesOfIsMulCocycle₂ hf) =
        H2π (Rep.ofMulDistribMulAction G M) (cocyclesOfIsMulCocycle₂ hf') ↔
      IsMulCoboundary₂ (fun p : G × G => f p / f' p) := by
  rw [← sub_eq_zero, ← map_sub, cocyclesOfIsMulCocycle₂_sub hf hf',
    H2π_eq_zero_iff_isMulCoboundary₂]

/-- Two multiplicative `2`-cocycles define the same class in `H²` if and only if there is a
`1`-cochain `c : G → M` whose coboundary rescales `f'` into `f`. -/
theorem H2π_eq_H2π_iff_exists {f f' : G × G → M}
    (hf : IsMulCocycle₂ f) (hf' : IsMulCocycle₂ f') :
    H2π (Rep.ofMulDistribMulAction G M) (cocyclesOfIsMulCocycle₂ hf) =
        H2π (Rep.ofMulDistribMulAction G M) (cocyclesOfIsMulCocycle₂ hf') ↔
      ∃ c : G → M, ∀ g h : G, f (g, h) = f' (g, h) * (g • c h / c (g * h) * c g) := by
  rw [H2π_eq_H2π_iff_isMulCoboundary₂_div hf hf']
  refine exists_congr fun c => forall₂_congr fun g h => ?_
  show g • c h / c (g * h) * c g = f (g, h) / f' (g, h) ↔
    f (g, h) = f' (g, h) * (g • c h / c (g * h) * c g)
  rw [eq_comm, div_eq_iff_eq_mul, mul_comm (f' (g, h))]

/-- Two multiplicative `2`-cocycles define the same class in `H²` if and only if there is a
`1`-cochain `c : G → M` whose coboundary rescales `f` into `f'`. -/
theorem H2π_eq_H2π_iff_exists' {f f' : G × G → M}
    (hf : IsMulCocycle₂ f) (hf' : IsMulCocycle₂ f') :
    H2π (Rep.ofMulDistribMulAction G M) (cocyclesOfIsMulCocycle₂ hf) =
        H2π (Rep.ofMulDistribMulAction G M) (cocyclesOfIsMulCocycle₂ hf') ↔
      ∃ c : G → M, ∀ g h : G, f' (g, h) = f (g, h) * (g • c h / c (g * h) * c g) :=
  (eq_comm.trans (H2π_eq_H2π_iff_exists hf' hf))

end InverseGalois.CFT

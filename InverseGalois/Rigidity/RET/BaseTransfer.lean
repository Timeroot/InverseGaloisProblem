/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Statement

/-!
# Changing the presentation of the base field

A regular Galois realization is stated over a base field `F` (the intended `F` being a rational
function field `k(T)`), but in the descent the base does not arrive as `RatFunc K`: it arrives as
an *intermediate field* `K(T)` of a fixed tower `Ω / ℚ(T)`.  The two are `K`-isomorphic, and this
file supplies the transfer along such an isomorphism.

The point is that changing the base along a ring isomorphism `e : F' ≃+* F` compatible with the
two structure maps into `L` changes nothing of substance: minimal polynomials transfer by
`e.symm` (`minpoly_of_ringEquiv`), so finiteness, normality and separability transfer with them,
and the two Galois groups have literally the same underlying automorphisms
(`algEquivCongrBase`) — an `F'`-automorphism of `L` fixes the image of `F'`, which is the image
of `F`.

## Main results

* `minpoly_of_ringEquiv` — `minpoly F' x = (minpoly F x).map e.symm`.
* `finiteDimensional_of_ringEquiv`, `normal_of_ringEquiv`, `isSeparable_of_ringEquiv`,
  `isGalois_of_ringEquiv` — the extension properties transfer.
* `algEquivCongrBase` — `(L ≃ₐ[F'] L) ≃* (L ≃ₐ[F] L)`.
* `IsRegularGaloisGroupOverBase.of_algEquiv` — the regular-realization predicate only depends on
  the base up to `k`-isomorphism.

The predicate's other invariance, under isomorphism of the group, lives with the definition in
`InverseGalois.Rigidity.RET.Statement`.
-/

open Polynomial

namespace Rigidity.RET

section BaseTransfer

variable {F F' L : Type*} [Field F] [Field F'] [Field L] [Algebra F L] [Algebra F' L]

/-- The two structure maps agree after `e.symm`: `F → F' → L` is the structure map `F → L`. -/
theorem algebraMap_comp_symm (e : F' ≃+* F)
    (he : ∀ x : F', algebraMap F' L x = algebraMap F L (e x)) :
    (algebraMap F' L).comp (e.symm : F →+* F') = algebraMap F L := by
  ext y
  simp [he]

/-- **Minimal polynomials transfer along a base isomorphism.**  If the structure map of `F'` is
the structure map of `F` precomposed with `e`, then the `F'`-minimal polynomial of `x` is the
`F`-minimal polynomial with its coefficients carried over by `e.symm`. -/
theorem minpoly_of_ringEquiv [FiniteDimensional F L] (e : F' ≃+* F)
    (he : ∀ x : F', algebraMap F' L x = algebraMap F L (e x)) (x : L) :
    minpoly F' x = (minpoly F x).map (e.symm : F →+* F') := by
  haveI : Algebra.IsIntegral F L := Algebra.IsIntegral.of_finite F L
  have hcomp : (algebraMap F' L).comp (e.symm : F →+* F')
      = ((RingEquiv.refl L : L ≃+* L) : L →+* L).comp (algebraMap F L) := by
    rw [algebraMap_comp_symm e he]
    ext y
    rfl
  exact (minpoly.map_eq_of_equiv_equiv (f := (e.symm : F ≃+* F')) (g := RingEquiv.refl L)
    hcomp x).symm

/-- Finiteness transfers along a base isomorphism: `F` is spanned by `1` over the isomorphic copy
`F'`, so the tower `F' ⊆ F ⊆ L` is finite at both steps. -/
theorem finiteDimensional_of_ringEquiv [FiniteDimensional F L] (e : F' ≃+* F)
    (he : ∀ x : F', algebraMap F' L x = algebraMap F L (e x)) :
    FiniteDimensional F' L := by
  letI : Algebra F' F := (e : F' →+* F).toAlgebra
  haveI : IsScalarTower F' F L := IsScalarTower.of_algebraMap_eq fun x => he x
  haveI : Module.Finite F' F := by
    refine ⟨⟨{1}, ?_⟩⟩
    rw [Finset.coe_singleton]
    refine top_unique fun y _ => ?_
    have hy : y = e.symm y • (1 : F) := by
      rw [Algebra.smul_def, mul_one]
      show y = e (e.symm y)
      rw [e.apply_symm_apply]
    rw [hy]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self 1)
  exact Module.Finite.trans (R := F') F L

/-- Normality transfers along a base isomorphism: the `F'`-minimal polynomial is the image of the
`F`-minimal polynomial, and splitting is invariant under that relabelling of the coefficients. -/
theorem normal_of_ringEquiv [FiniteDimensional F L] [Normal F L] (e : F' ≃+* F)
    (he : ∀ x : F', algebraMap F' L x = algebraMap F L (e x)) :
    Normal F' L := by
  haveI := finiteDimensional_of_ringEquiv (F := F) (F' := F') (L := L) e he
  rw [normal_iff]
  intro x
  refine ⟨Algebra.IsIntegral.isIntegral (R := F') x, ?_⟩
  rw [minpoly_of_ringEquiv e he x, Polynomial.map_map, algebraMap_comp_symm e he]
  exact Normal.splits' x

/-- Separability transfers along a base isomorphism. -/
theorem isSeparable_of_ringEquiv [FiniteDimensional F L] [Algebra.IsSeparable F L] (e : F' ≃+* F)
    (he : ∀ x : F', algebraMap F' L x = algebraMap F L (e x)) :
    Algebra.IsSeparable F' L := by
  haveI := finiteDimensional_of_ringEquiv (F := F) (F' := F') (L := L) e he
  refine ⟨fun x => ?_⟩
  show (minpoly F' x).Separable
  rw [minpoly_of_ringEquiv e he x]
  have hs : (minpoly F x).Separable := Algebra.IsSeparable.isSeparable F x
  exact hs.map

/-- Being Galois transfers along a base isomorphism. -/
theorem isGalois_of_ringEquiv [FiniteDimensional F L] [IsGalois F L] (e : F' ≃+* F)
    (he : ∀ x : F', algebraMap F' L x = algebraMap F L (e x)) :
    IsGalois F' L :=
  { to_isSeparable := isSeparable_of_ringEquiv e he
    to_normal := normal_of_ringEquiv e he }

/-- **The Galois groups coincide.**  An `F'`-automorphism of `L` is a ring automorphism fixing the
image of `F'` in `L`, which is the image of `F`; so the two automorphism groups have the same
underlying automorphisms. -/
def algEquivCongrBase (e : F' ≃+* F)
    (he : ∀ x : F', algebraMap F' L x = algebraMap F L (e x)) :
    (L ≃ₐ[F'] L) ≃* (L ≃ₐ[F] L) where
  toFun σ := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (R := F) fun y => by
    have h := σ.commutes (e.symm y)
    rwa [he, e.apply_symm_apply] at h
  invFun σ := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (R := F') fun x => by
    rw [he]
    exact σ.commutes (e x)
  left_inv σ := AlgEquiv.ext fun _ => rfl
  right_inv σ := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

end BaseTransfer

end Rigidity.RET

namespace IsRegularGaloisGroupOverBase

variable {k : Type*} [Field k] {F F' : Type*} [Field F] [Field F'] [Algebra k F] [Algebra k F']
variable {G : Type*} [Group G]

/-- **The base may be replaced by a `k`-isomorphic field.**  This is what lets a base that arrives
as an intermediate field `K(T)` of a tower be recognized as the rational function field
`RatFunc K`. -/
theorem of_algEquiv (hG : IsRegularGaloisGroupOverBase k F G) (e : F' ≃ₐ[k] F) :
    IsRegularGaloisGroupOverBase k F' G := by
  obtain ⟨L, hFL, algFL, hFD, hGal, algkL, hST, hreg, ⟨ψ⟩⟩ := hG
  letI := hFL
  letI := algFL
  letI := hFD
  letI := hGal
  letI := algkL
  letI := hST
  letI algF'L : Algebra F' L := ((algebraMap F L).comp (e : F' →+* F)).toAlgebra
  have he : ∀ x : F', algebraMap F' L x = algebraMap F L (e x) := fun _ => rfl
  haveI : FiniteDimensional F' L :=
    Rigidity.RET.finiteDimensional_of_ringEquiv (e : F' ≃+* F) he
  haveI : IsGalois F' L := Rigidity.RET.isGalois_of_ringEquiv (e : F' ≃+* F) he
  haveI : IsScalarTower k F' L := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    rw [he, e.commutes, ← IsScalarTower.algebraMap_apply]
  exact ⟨L, hFL, algF'L, inferInstance, inferInstance, algkL, inferInstance, hreg,
    ⟨(Rigidity.RET.algEquivCongrBase (e : F' ≃+* F) he).trans ψ⟩⟩

end IsRegularGaloisGroupOverBase

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.BaseChange
import InverseGalois.CFT.Brauer.DivisionCyclic
import InverseGalois.CFT.Brauer.MaximalSubfield

/-!
# Every Brauer class over a local field is split by an unramified cyclic extension

A Brauer class over a field is the class of a central simple algebra whose underlying ring is a
domain, and a finite-dimensional domain over a field is a division ring.  Over a nonarchimedean
local field such a division algebra has square dimension and is split by a cyclic subfield of
degree the square root of that dimension whose nonzero elements carry only the absolute values of
the base field.

The absolute value that a division algebra induces on a subfield is intrinsic to the subfield: it
is a multiplicative norm extending the absolute value of the base field, and over a complete
nonarchimedean base there is only one such, the spectral norm.  So the unramifiedness of the
splitting field can be stated without reference to the algebra it was carved out of.

## Main results

* `InverseGalois.CFT.divisionNorm_algHom_eq_spectralNorm`: **the absolute value of a division
  algebra restricted to a subfield is the spectral norm of that subfield.**
* `InverseGalois.CFT.exists_cyclic_unramified_mem_relative`: **every Brauer class over a
  nonarchimedean local field lies in the relative Brauer group of a cyclic extension whose nonzero
  elements have the absolute values of the nonzero scalars.**

## Tags

Brauer group, local field, division algebra, unramified extension, cyclic extension, spectral norm
-/

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

universe u

open Module

open scoped TensorProduct

namespace InverseGalois.CFT

/-! ### The absolute value of a subfield is the spectral norm -/

section Spectral

variable {K D : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
variable {L : Type u} [Field L] [Algebra K L]

omit [IsUltrametricDist K] [CompleteSpace K] [FiniteDimensional K D] in
/-- An algebra map out of a field into a nonzero ring is injective. -/
theorem algHom_injective (f : L →ₐ[K] D) : Function.Injective f := by
  intro a b hab
  by_contra hne
  have hsub : a - b ≠ 0 := sub_ne_zero.2 hne
  have h0 : f (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have : (1 : D) = 0 := by
    rw [← map_one f, ← mul_inv_cancel₀ hsub, map_mul, h0, zero_mul]
  exact one_ne_zero this

/-- The absolute value a division algebra induces on a subfield, bundled. -/
noncomputable def divisionAbsoluteValueComp (f : L →ₐ[K] D) : AbsoluteValue L ℝ where
  toFun y := divisionNorm K D (f y)
  map_mul' x y := by rw [map_mul, divisionNorm_mul]
  nonneg' _ := divisionNorm_nonneg _
  eq_zero' y := by
    rw [divisionNorm_eq_zero_iff]
    exact ⟨fun h => algHom_injective f (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩
  add_le' x y := by
    rw [map_add]
    exact (divisionNorm_isNonarchimedean _ _).trans
      (max_le_add_of_nonneg (divisionNorm_nonneg _) (divisionNorm_nonneg _))

@[simp]
theorem divisionAbsoluteValueComp_apply (f : L →ₐ[K] D) (y : L) :
    divisionAbsoluteValueComp f y = divisionNorm K D (f y) := rfl

/-- **The absolute value of a division algebra restricted to a subfield is the spectral norm of
that subfield.**  It is a multiplicative norm extending the absolute value of the base field, and
over a complete nonarchimedean base the spectral norm is the only one. -/
theorem divisionNorm_algHom_eq_spectralNorm [FiniteDimensional K L] (f : L →ₐ[K] D) (y : L) :
    divisionNorm K D (f y) = spectralNorm K L y := by
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  refine spectralNorm_unique_field_norm_ext (f := divisionAbsoluteValueComp f) (fun k => ?_) y
  rw [divisionAbsoluteValueComp_apply, AlgHom.commutes, divisionNorm_algebraMap]

end Spectral

/-! ### The unramified cyclic splitting field of a Brauer class -/

section Local

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]

/-- **Every Brauer class over a nonarchimedean local field lies in the relative Brauer group of a
cyclic extension whose nonzero elements have the absolute values of the nonzero scalars.**  The
class is the class of a division algebra, which is split by such a subfield of degree the square
root of its dimension; the absolute value the algebra induces on the subfield is the spectral norm
of the subfield, so the unramifiedness is a statement about the subfield alone. -/
theorem exists_cyclic_unramified_mem_relative (x : BrauerGroup.{u, u} K) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L), FiniteDimensional K L ∧ IsGalois K L ∧
      IsCyclic (L ≃ₐ[K] L) ∧
      (∀ z : L, z ≠ 0 → ∃ c : K, c ≠ 0 ∧ spectralNorm K L z = ‖c‖) ∧
      x ∈ BrauerGroup.relative K L := by
  obtain ⟨B, hBdom, rfl⟩ := BrauerGroup.exists_isDomain_mk_eq x
  haveI := hBdom
  letI : DivisionRing (B : Type u) := divisionRingOfFiniteDimensional K (B : Type u)
  obtain ⟨n, hn⟩ := exists_mul_self_eq_finrank K (B : Type u)
  obtain ⟨L, hLfield, hLalg, f, -, hgal, hcyc, hval, m, ⟨eqv⟩⟩ :=
    exists_cyclic_unramified_splitting K (B : Type u) hn
  letI : Field L := hLfield
  letI : Algebra K L := hLalg
  haveI hLfin : FiniteDimensional K L :=
    Module.Finite.of_injective f.toLinearMap (algHom_injective f)
  have hm : m ≠ 0 := by
    rintro rfl
    have h1 : finrank L (L ⊗[K] (B : Type u)) = finrank K (B : Type u) := Module.finrank_baseChange
    have h2 : finrank L (L ⊗[K] (B : Type u)) = 0 := by
      rw [eqv.toLinearEquiv.finrank_eq, Module.finrank_matrix]
      simp
    have h3 : 0 < finrank K (B : Type u) := Module.finrank_pos_iff.2 inferInstance
    omega
  refine ⟨L, hLfield, hLalg, hLfin, hgal, hcyc, fun z hz => ?_,
    BrauerGroup.mk_mem_relative_of_algEquiv_matrix _ hm eqv⟩
  obtain ⟨c, hc0, hc⟩ := hval z hz
  exact ⟨c, hc0, by rw [← divisionNorm_algHom_eq_spectralNorm f z, hc]⟩

end Local

end InverseGalois.CFT

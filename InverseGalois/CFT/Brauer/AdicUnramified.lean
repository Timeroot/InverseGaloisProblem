/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.LocalUnramified
import InverseGalois.CFT.Brauer.UnramifiedClassOrder
import InverseGalois.CFT.Local.AdicLocalField
import InverseGalois.CFT.Local.SpectralNorm

/-!
# A cyclic splitting field of full Brauer order over a complete discretely valued field

A rank one valuation makes a field into a nonarchimedean normed field, and the norm determines the
valuation because the comparison map of a rank one valuation is strictly monotone.  So the
unramifiedness of a finite extension, which the splitting theory of division algebras produces in
the shape "every nonzero element of the extension has the absolute value of a scalar", can be read
back as a statement about valuations: the value of a norm from the extension is the degree-th power
of a value of the base field.

That is exactly the hypothesis under which the units of the base field modulo the norms surject
onto the integers modulo the degree, so a Brauer class over a field which is complete, discretely
valued and locally compact always lies in the relative Brauer group of a cyclic extension, and that
relative Brauer group has an element of order the full degree.

## Main results

* `InverseGalois.CFT.hasUnramifiedNormValues_of_spectralNorm`: **the spectral-norm form of
  unramifiedness gives the valuation form.**
* `InverseGalois.CFT.exists_cyclic_relative_orderOf_eq_finrank`: **every Brauer class over a
  complete, discretely valued, locally compact field lies in the relative Brauer group of a cyclic
  extension whose relative Brauer group has an element of order the degree.**
* `InverseGalois.CFT.exists_cyclic_relative_orderOf_eq_finrank_adicCompletion`: the same for the
  completion of a number field at a finite place.

## Tags

Brauer group, local field, unramified extension, cyclic extension, spectral norm, valuation,
class field theory
-/

namespace InverseGalois.CFT

open Module

open scoped Valued WithZero

variable {K L : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K]

/-! ### The norm of a rank one valuation determines the valuation -/

omit [CompleteSpace K] in
/-- Two elements of the same absolute value have the same value: the comparison map of a rank one
valuation is strictly monotone, hence reflects the order. -/
theorem valued_eq_of_norm_eq {a b : K} (h : ‖a‖ = ‖b‖) : Valued.v a = Valued.v b :=
  le_antisymm (Valued.toNormedField.norm_le_iff.1 h.le)
    (Valued.toNormedField.norm_le_iff.1 h.ge)

/-! ### Unramifiedness in the two languages -/

variable [Field L] [Algebra K L] [FiniteDimensional K L]

/-- **The spectral-norm form of unramifiedness gives the valuation form.**  The norm of an element
is the degree-th power of its spectral norm, so if the spectral norm of an element is the absolute
value of a scalar then the value of its norm is the degree-th power of the value of that scalar. -/
theorem hasUnramifiedNormValues_of_spectralNorm
    (hval : ∀ z : L, z ≠ 0 → ∃ c : K, c ≠ 0 ∧ spectralNorm K L z = ‖c‖) :
    HasUnramifiedNormValues K L := by
  intro y
  obtain ⟨c, hc0, hc⟩ := hval (y : L) (Units.ne_zero y)
  refine ⟨Units.mk0 c hc0, ?_⟩
  have hn : ‖Algebra.norm K (y : L)‖ = ‖(Units.mk0 c hc0 : K) ^ finrank K L‖ := by
    rw [norm_algebraNorm_eq_spectralNorm_pow, hc, norm_pow]
    rfl
  rw [valued_eq_of_norm_eq hn, map_pow]

/-! ### The Brauer class of full order -/

variable (K) in
/-- **Every Brauer class over a complete, discretely valued, locally compact field lies in the
relative Brauer group of a cyclic extension whose relative Brauer group has an element of order the
degree.**  The class is split by a cyclic extension all of whose absolute values are absolute
values of scalars, and such an extension is unramified, so reading the value of a unit modulo the
degree exhibits a norm class of order the degree. -/
theorem exists_cyclic_relative_orderOf_eq_finrank [ProperSpace K] (x : BrauerGroup K) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L), FiniteDimensional K L ∧ IsGalois K L ∧
      IsCyclic (L ≃ₐ[K] L) ∧ x ∈ BrauerGroup.relative K L ∧
      ∃ y : ↥(BrauerGroup.relative K L), orderOf y = finrank K L := by
  obtain ⟨L, hLfield, hLalg, hLfin, hgal, hcyc, hval, hmem⟩ :=
    exists_cyclic_unramified_mem_relative K x
  letI : Field L := hLfield
  letI : Algebra K L := hLalg
  haveI : FiniteDimensional K L := hLfin
  haveI : IsGalois K L := hgal
  haveI : IsCyclic (L ≃ₐ[K] L) := hcyc
  obtain ⟨σ₀, hσ₀⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  obtain ⟨u, hu0, hu1⟩ := Valuation.RankOne.nontrivial (Valued.v : Valuation K ℤᵐ⁰)
  obtain ⟨m, hm⟩ := exists_isUnitValGen (A := K)
    ⟨Units.mk0 u fun h => hu0 (by rw [h, map_zero]), hu1⟩
  exact ⟨L, hLfield, hLalg, hLfin, hgal, hcyc, hmem,
    exists_orderOf_eq_finrank_relative hσ₀ (hasUnramifiedNormValues_of_spectralNorm hval) hm⟩

/-! ### The completion of a number field at a finite place -/

section NumberField

open NumberField IsDedekindDomain

variable (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))

/-- **Every Brauer class over the completion of a number field at a finite place lies in the
relative Brauer group of a cyclic extension whose relative Brauer group has an element of order the
degree.**  Such a completion is complete, discretely valued and locally compact. -/
theorem exists_cyclic_relative_orderOf_eq_finrank_adicCompletion
    (x : BrauerGroup (w.adicCompletion F)) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra (w.adicCompletion F) L),
      FiniteDimensional (w.adicCompletion F) L ∧ IsGalois (w.adicCompletion F) L ∧
        IsCyclic (L ≃ₐ[w.adicCompletion F] L) ∧
        x ∈ BrauerGroup.relative (w.adicCompletion F) L ∧
        ∃ y : ↥(BrauerGroup.relative (w.adicCompletion F) L),
          orderOf y = finrank (w.adicCompletion F) L :=
  exists_cyclic_relative_orderOf_eq_finrank _ x

end NumberField

end InverseGalois.CFT

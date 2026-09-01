/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.CompleteNormIndex
import InverseGalois.CFT.Local.NormValued

/-!
# The norm index of a cyclic extension of a local field

A finite extension of a complete, discretely valued, locally compact field is again complete,
discretely valued and locally compact, for the valuation carried by the field norm, and the
automorphisms over the base field preserve that valuation because they do not change the norm.
Nothing here asks the extension to be unramified: the field norm transports the valuation whatever
the ramification is.

Feeding that package into the Herbrand quotient computation gives the norm index of an arbitrary
cyclic extension of a local field, ramified or not.  The Herbrand quotient of the unit group of the
extension is the degree and Hilbert's theorem 90 makes its denominator one, so the units of the base
field modulo the norms have order the degree.  In particular a cyclic extension of degree bigger
than one always has a unit of the base field which is not a norm.

## Main results

* `InverseGalois.CFT.exists_valued_of_finite`: **a finite extension of a complete, discretely
  valued, locally compact field carries all the structure of a local field.**
* `InverseGalois.CFT.index_normSubgroup_eq_finrank_local`: **the norm index of a cyclic extension of
  a local field is the degree of the extension.**
* `InverseGalois.CFT.exists_notMem_normSubgroup`: **a cyclic extension of a local field of degree
  bigger than one has a unit of the base field which is not a norm.**

## Tags

local field, norm index, Herbrand quotient, cyclic extension, class field theory
-/

namespace InverseGalois.CFT

open Module

open scoped Valued WithZero

variable (K L : Type) [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K]
  [Field L] [Algebra K L] [FiniteDimensional K L] {p e : ℕ}

/-! ### The structure of a finite extension -/

/-- **A finite extension of a complete, discretely valued, locally compact field carries all the
structure of a local field**: a valuation extending that of the base field, completeness, a residue
characteristic, finite graded pieces, invariance under the automorphisms over the base field, a unit
of nontrivial value and a generator of the value group.  Unlike the unramified form, nothing is
assumed about the absolute values of the extension. -/
theorem exists_valued_of_finite (hres : HasResidueChar K p e)
    (hnt : ∃ x : Kˣ, Valued.v (x : K) ≠ 1) :
    ∃ (_ : Valued L ℤᵐ⁰) (_ : CompleteSpace L) (m : ℤ) (e' : ℕ),
      (∀ (σ : L ≃ₐ[K] L) (x : L), Valued.v (σ x) = Valued.v x) ∧
        HasResidueChar L p e' ∧ (∀ k : ℤ, Finite (gradedAdd L k)) ∧
          (∃ x : Lˣ, Valued.v (x : L) ≠ 1) ∧ IsUnitValGen L m := by
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : Valued L ℤᵐ⁰ := normValued K L
  have hvL : ∀ y : L, Valued.v y = Valued.v (Algebra.norm K y) := fun _ => rfl
  haveI : CompleteSpace L := spectralNorm.completeSpace K L
  letI : Valuation.RankOne (Valued.v : Valuation L ℤᵐ⁰) :=
    { hom := Valuation.RankOne.hom (Valued.v : Valuation K ℤᵐ⁰)
      strictMono' := Valuation.RankOne.strictMono (Valued.v : Valuation K ℤᵐ⁰)
      exists_val_nontrivial := by
        obtain ⟨x, hx⟩ := exists_units_val_ne_one_of_norm hvL hnt
        exact ⟨(x : L), valued_unit_ne_zero x, hx⟩ }
  haveI : WeaklyLocallyCompactSpace L := weaklyLocallyCompactSpace_spectral K L
  haveI : ProperSpace L :=
    ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace L
  obtain ⟨m, hm⟩ := exists_isUnitValGen (exists_units_val_ne_one_of_norm hvL hnt)
  exact ⟨inferInstance, inferInstance, m, finrank K L * e, valued_algEquiv_of_norm hvL,
    hasResidueChar_of_norm hvL hres, fun k => finite_gradedAdd_of_properSpace k,
    exists_units_val_ne_one_of_norm hvL hnt, hm⟩

/-! ### The norm index -/

/-- **The norm index of a cyclic extension of a local field is the degree of the extension.**  The
extension is again a local field for the valuation carried by the field norm, so the Herbrand
quotient of its unit group is the degree, and Hilbert's theorem 90 makes the denominator of that
quotient one. -/
theorem index_normSubgroup_eq_finrank_local [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (hres : HasResidueChar K p e) :
    (normSubgroup K L).index = finrank K L := by
  obtain ⟨u, hu0, hu1⟩ := Valuation.RankOne.nontrivial (Valued.v : Valuation K ℤᵐ⁰)
  have hnt : ∃ x : Kˣ, Valued.v (x : K) ≠ 1 :=
    ⟨Units.mk0 u fun h => hu0 (by rw [h, map_zero]), hu1⟩
  obtain ⟨instV, instC, -, e', hv, hres', hgr, hnt', -⟩ := exists_valued_of_finite K L hres hnt
  letI := instV
  haveI := instC
  exact index_normSubgroup_eq_finrank_of_complete hv hres' hgr hnt' ‹IsCyclic (L ≃ₐ[K] L)›

/-- **A cyclic extension of a local field of degree bigger than one has a unit of the base field
which is not a norm.**  If every unit were a norm the norm index would be one, but it is the
degree. -/
theorem exists_notMem_normSubgroup [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (hres : HasResidueChar K p e) (hd : 1 < finrank K L) :
    ∃ a : Kˣ, a ∉ normSubgroup K L := by
  by_contra hcon
  push_neg at hcon
  have hidx := index_normSubgroup_eq_finrank_local K L hres
  rw [(Subgroup.eq_top_iff' _).2 hcon, Subgroup.index_top] at hidx
  omega

end InverseGalois.CFT

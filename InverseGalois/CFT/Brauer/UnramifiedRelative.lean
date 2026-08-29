/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.CyclicNorm
import InverseGalois.CFT.Local.CompleteNormIndex
import InverseGalois.CFT.Local.UnramifiedNormValue

/-!
# The relative Brauer group of an unramified cyclic extension of local fields

The relative Brauer group of a cyclic extension is the units of the base field modulo the norms,
and for an unramified extension of complete discretely valued fields with finite residue field that
quotient is read off the valuation: it is the integers modulo the degree.  So the relative Brauer
group of an unramified cyclic extension of local fields is cyclic of order the degree, and its
generator is the class of the cyclic algebra of a uniformizer.

This is the local invariant map in the unramified case, transported to the Brauer group.

## Main results

* `InverseGalois.CFT.unramifiedRelativeBrauerEquiv`: **the relative Brauer group of an unramified
  cyclic extension of local fields is the integers modulo the degree.**
* `InverseGalois.CFT.card_relative_eq_finrank_of_unramified`: its order is the degree.
* `InverseGalois.CFT.exists_orderOf_eq_finrank_of_unramified`: it contains a class of order the
  degree.

## Tags

Brauer group, relative Brauer group, local field, unramified extension, invariant map,
class field theory
-/

namespace InverseGalois.CFT

open Module

open scoped WithZero

/-! ### A generator of the value group is a nontrivial value -/

section Generator

variable {A : Type*} [Field A] [Valued A ℤᵐ⁰] {m : ℤ}

/-- A field with a generator of its value group has a unit of nontrivial value. -/
theorem exists_units_val_ne_one_of_isUnitValGen (hm : IsUnitValGen A m) :
    ∃ x : Aˣ, Valued.v (x : A) ≠ 1 := by
  obtain ⟨x, hx⟩ := hm.exists_eq
  refine ⟨Additive.toMul x, fun h => hm.ne_zero ?_⟩
  rw [← hx]
  exact AddMonoidHom.mem_ker.mp (mem_ker_unitVal.mpr h)

end Generator

/-! ### The relative Brauer group of an unramified cyclic extension -/

section Unramified

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [Valued L ℤᵐ⁰] [CompleteSpace L] {m : ℤ} {p e : ℕ} {σ₀ : L ≃ₐ[K] L}

/-- **The relative Brauer group of an unramified cyclic extension of local fields is the integers
modulo the degree.**  The relative Brauer group of a cyclic extension is the units of the base
field modulo the norms, and for an unramified extension that quotient is read off the valuation. -/
noncomputable def unramifiedRelativeBrauerEquiv
    (hv : ∀ (σ : L ≃ₐ[K] L) (x : L), Valued.v (σ x) = Valued.v x)
    (hres : HasResidueChar L p e) (hgr : ∀ k : ℤ, Finite (gradedAdd L k))
    (hur : IsUnramifiedValued K L) (hm : IsUnitValGen L m)
    (hσ₀ : ∀ x : L ≃ₐ[K] L, x ∈ Subgroup.zpowers σ₀) :
    Multiplicative (ZMod (finrank K L)) ≃* BrauerGroup.relative K L :=
  (unramifiedNormEquiv hv hur hm
      (index_normSubgroup_eq_finrank_of_complete hv hres hgr
        (exists_units_val_ne_one_of_isUnitValGen hm) ⟨⟨σ₀, hσ₀⟩⟩)).symm.trans
    (cyclicBrauerEquiv hσ₀)

/-- **The relative Brauer group of an unramified cyclic extension of local fields has order the
degree.** -/
theorem card_relative_eq_finrank_of_unramified
    (hv : ∀ (σ : L ≃ₐ[K] L) (x : L), Valued.v (σ x) = Valued.v x)
    (hres : HasResidueChar L p e) (hgr : ∀ k : ℤ, Finite (gradedAdd L k))
    (hur : IsUnramifiedValued K L) (hm : IsUnitValGen L m)
    (hσ₀ : ∀ x : L ≃ₐ[K] L, x ∈ Subgroup.zpowers σ₀) :
    Nat.card ↥(BrauerGroup.relative K L) = finrank K L := by
  rw [← Nat.card_congr (unramifiedRelativeBrauerEquiv hv hres hgr hur hm hσ₀).toEquiv,
    ← Nat.card_congr (Multiplicative.ofAdd (α := ZMod (finrank K L))), Nat.card_zmod]

/-- **The relative Brauer group of an unramified cyclic extension of local fields is cyclic.** -/
theorem isCyclic_relative_of_unramified
    (hv : ∀ (σ : L ≃ₐ[K] L) (x : L), Valued.v (σ x) = Valued.v x)
    (hres : HasResidueChar L p e) (hgr : ∀ k : ℤ, Finite (gradedAdd L k))
    (hur : IsUnramifiedValued K L) (hm : IsUnitValGen L m)
    (hσ₀ : ∀ x : L ≃ₐ[K] L, x ∈ Subgroup.zpowers σ₀) :
    IsCyclic ↥(BrauerGroup.relative K L) :=
  let e := unramifiedRelativeBrauerEquiv hv hres hgr hur hm hσ₀
  isCyclic_of_surjective e e.surjective

/-- **An unramified cyclic extension of local fields carries a Brauer class of order its degree.**
This is the local ingredient of the fundamental class. -/
theorem exists_orderOf_eq_finrank_of_unramified
    (hv : ∀ (σ : L ≃ₐ[K] L) (x : L), Valued.v (σ x) = Valued.v x)
    (hres : HasResidueChar L p e) (hgr : ∀ k : ℤ, Finite (gradedAdd L k))
    (hur : IsUnramifiedValued K L) (hm : IsUnitValGen L m)
    (hσ₀ : ∀ x : L ≃ₐ[K] L, x ∈ Subgroup.zpowers σ₀) :
    ∃ x : ↥(BrauerGroup.relative K L), orderOf x = finrank K L := by
  haveI := isCyclic_relative_of_unramified hv hres hgr hur hm hσ₀
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥(BrauerGroup.relative K L))
  exact ⟨g, by rw [hg, card_relative_eq_finrank_of_unramified hv hres hgr hur hm hσ₀]⟩

end Unramified

end InverseGalois.CFT

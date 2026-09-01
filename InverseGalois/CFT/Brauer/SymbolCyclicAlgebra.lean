/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.CyclicNorm
import InverseGalois.CFT.Brauer.InflateTower
import InverseGalois.CFT.Profinite.SymbolCyclic

/-!
# The power residue symbol is the class of a cyclic algebra

The symbol of two units of a base containing a primitive `n`-th root of unity is the inverse of the
class of an explicit two cocycle, the one recording the carry in the Kummer character of the second
unit.  That cocycle only depends on the Kummer character of the second unit, so as soon as a finite
cyclic Galois level of the extension carries the character -- its discrete logarithm to a chosen
generator computing the character -- the cocycle is inflated from the level, where it is exactly the
defining cocycle of the cyclic algebra of the first unit.

Two consequences follow at once.  The Brauer class of the symbol is the class of that cyclic
algebra, so the symbol is computable by the local invariant of a cyclic algebra; and the symbol is
trivial exactly when the first unit is a norm from the level, because the Brauer class of a cyclic
algebra is trivial exactly then.

## Main results

* `InverseGalois.CFT.inflateCocycle_cyclicUnitCocycle_eq`: **the cyclic two cocycle of a pair of
  units is inflated from the cyclic algebra cocycle of a level carrying the Kummer character.**
* `InverseGalois.CFT.smoothBrauerHom_kummerSymbolUnits`: **the Brauer class of the power symbol is
  the inverse of the class of the cyclic algebra.**
* `InverseGalois.CFT.kummerSymbolUnits_eq_one_iff_exists_norm`: **the power symbol of two units is
  trivial exactly when the first is a norm from the level.**

## Tags

Hilbert symbol, norm residue symbol, cyclic algebra, crossed product, Brauer group, Kummer theory,
class field theory
-/

universe u

namespace InverseGalois.CFT

open groupCohomology

section SymbolCyclicAlgebra

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω] {n : ℕ} [NeZero n]
  {ζ : k} {hζ : IsPrimitiveRoot ζ n}

attribute [local instance] zmodTrivialAction isSmoothAction_zmod

variable (h : IsKummerData k Ω (Multiplicative (ZMod n)) (zmodRootHom hζ) n)
  (E : IntermediateField k Ω) [FiniteDimensional k ↥E] [IsGalois k ↥E] {σ₀ : Gal(↥E/k)}

/-! ### A level carrying the Kummer character -/

omit [FiniteDimensional k ↥E] in
/-- The carry condition of a level whose discrete logarithm computes the Kummer character of a unit
is the carry condition of that character. -/
theorem carry_iff_of_dlog_eq {b : kˣ} (hcard : Nat.card Gal(↥E/k) = n)
    (hdlog : ∀ g : Gal(Ω/k),
      (dlog σ₀ (AlgEquiv.restrictNormalHom ↥E g)).val = (kummerChar h b g).val)
    (g g' : Gal(Ω/k)) :
    (dlog σ₀ (AlgEquiv.restrictNormalHom ↥E g)).val
        + (dlog σ₀ (AlgEquiv.restrictNormalHom ↥E g')).val < Nat.card Gal(↥E/k) ↔
      (kummerChar h b g).val + (kummerChar h b g').val < n := by
  rw [hdlog g, hdlog g', hcard]

omit [FiniteDimensional k ↥E] in
/-- **The cyclic two cocycle of a pair of units is inflated from the cyclic algebra cocycle of a
level carrying the Kummer character of the second unit.** -/
theorem inflateCocycle_cyclicUnitCocycle_eq (a b : kˣ)
    (hcarry : ∀ g g' : Gal(Ω/k),
      (dlog σ₀ (AlgEquiv.restrictNormalHom ↥E g)).val
          + (dlog σ₀ (AlgEquiv.restrictNormalHom ↥E g')).val < Nat.card Gal(↥E/k) ↔
        (kummerChar h b g).val + (kummerChar h b g').val < n) :
    inflateCocycle (L := ↥E) Ω (cyclicUnitCocycle σ₀ a) = kummerCyclicCocycle h a b := by
  funext p
  obtain ⟨g, g'⟩ := p
  show Units.map (algebraMap ↥E Ω : ↥E →* Ω)
      (cyclicUnitCocycle σ₀ a
        (AlgEquiv.restrictNormalHom ↥E g, AlgEquiv.restrictNormalHom ↥E g'))
    = kummerCyclicCocycle h a b (g, g')
  rw [cyclicUnitCocycle, cyclicCocycle_apply, kummerCyclicCocycle_apply]
  by_cases hlt : (kummerChar h b g).val + (kummerChar h b g').val < n
  · rw [if_pos ((hcarry g g').2 hlt), if_pos hlt, map_one]
  · rw [if_neg fun hc => hlt ((hcarry g g').1 hc), if_neg hlt]
    refine Units.ext ?_
    show algebraMap ↥E Ω (algebraMap k ↥E (a : k)) = algebraMap k Ω (a : k)
    rw [← IsScalarTower.algebraMap_apply]

/-! ### The Brauer class of the symbol -/

/-- The class of the cyclic two cocycle of a pair of units is the class of the cyclic algebra
cocycle of a level carrying the Kummer character of the second unit. -/
theorem smoothH2Mk_kummerCyclicCocycle_eq (hσ₀ : ∀ x : Gal(↥E/k), x ∈ Subgroup.zpowers σ₀)
    (a b : kˣ)
    (hcarry : ∀ g g' : Gal(Ω/k),
      (dlog σ₀ (AlgEquiv.restrictNormalHom ↥E g)).val
          + (dlog σ₀ (AlgEquiv.restrictNormalHom ↥E g')).val < Nat.card Gal(↥E/k) ↔
        (kummerChar h b g).val + (kummerChar h b g').val < n) :
    smoothH2Mk (inflateCocycle (L := ↥E) Ω (cyclicUnitCocycle σ₀ a))
        (isMulCocycle₂_inflateCocycle (L' := Ω) (isMulCocycle₂_cyclicUnitCocycle hσ₀ a))
        (isSmooth₂_inflateCocycle E (cyclicUnitCocycle σ₀ a))
      = smoothH2Mk (kummerCyclicCocycle h a b) (isMulCocycle₂_kummerCyclicCocycle h a b)
          (isSmooth₂_kummerCyclicCocycle h a b) :=
  smoothH2Mk_congr _ _ _ _ (inflateCocycle_cyclicUnitCocycle_eq h E a b hcarry)

/-- The Brauer class of the cyclic two cocycle of a pair of units is the class of the cyclic
algebra of the first unit over a level carrying the Kummer character of the second. -/
theorem smoothBrauer_kummerCyclicCocycle (hσ₀ : ∀ x : Gal(↥E/k), x ∈ Subgroup.zpowers σ₀)
    (a b : kˣ)
    (hcarry : ∀ g g' : Gal(Ω/k),
      (dlog σ₀ (AlgEquiv.restrictNormalHom ↥E g)).val
          + (dlog σ₀ (AlgEquiv.restrictNormalHom ↥E g')).val < Nat.card Gal(↥E/k) ↔
        (kummerChar h b g).val + (kummerChar h b g').val < n) :
    smoothBrauer (smoothH2Mk (kummerCyclicCocycle h a b)
        (isMulCocycle₂_kummerCyclicCocycle h a b) (isSmooth₂_kummerCyclicCocycle h a b))
      = cyclicBrauerHom hσ₀ a :=
  (mk_csa_eq_smoothBrauer E (isMulCocycle₂_cyclicUnitCocycle hσ₀ a)
    (smoothH2Mk_kummerCyclicCocycle_eq h E hσ₀ a b hcarry)).symm

omit [FiniteDimensional k ↥E] [IsGalois k ↥E] in
/-- **The power symbol of two units is the inverse of the class of their cyclic two cocycle.** -/
theorem kummerSymbolUnits_eq_inv_smoothH2Mk (a b : kˣ) :
    kummerSymbolUnits h (mulZMod n) a b
      = (smoothH2Mk (kummerCyclicCocycle h a b) (isMulCocycle₂_kummerCyclicCocycle h a b)
          (isSmooth₂_kummerCyclicCocycle h a b))⁻¹ :=
  mul_eq_one_iff_eq_inv.mp (kummerSymbolUnits_mul_smoothH2Mk_eq_one h a b)

/-- **The Brauer class of the power symbol of two units is the inverse of the class of the cyclic
algebra** of the first unit over a level carrying the Kummer character of the second. -/
theorem smoothBrauerHom_kummerSymbolUnits (hσ₀ : ∀ x : Gal(↥E/k), x ∈ Subgroup.zpowers σ₀)
    (a b : kˣ)
    (hcarry : ∀ g g' : Gal(Ω/k),
      (dlog σ₀ (AlgEquiv.restrictNormalHom ↥E g)).val
          + (dlog σ₀ (AlgEquiv.restrictNormalHom ↥E g')).val < Nat.card Gal(↥E/k) ↔
        (kummerChar h b g).val + (kummerChar h b g').val < n) :
    smoothBrauerHom (kummerSymbolUnits h (mulZMod n) a b) = (cyclicBrauerHom hσ₀ a)⁻¹ := by
  rw [kummerSymbolUnits_eq_inv_smoothH2Mk, map_inv, smoothBrauerHom_apply,
    smoothBrauer_kummerCyclicCocycle h E hσ₀ a b hcarry]

/-! ### The norm criterion -/

/-- **The power symbol of two units of the base is trivial exactly when the first unit is a norm**
from a level carrying the Kummer character of the second. -/
theorem kummerSymbolUnits_eq_one_iff_exists_norm
    (hσ₀ : ∀ x : Gal(↥E/k), x ∈ Subgroup.zpowers σ₀) (a b : kˣ)
    (hcarry : ∀ g g' : Gal(Ω/k),
      (dlog σ₀ (AlgEquiv.restrictNormalHom ↥E g)).val
          + (dlog σ₀ (AlgEquiv.restrictNormalHom ↥E g')).val < Nat.card Gal(↥E/k) ↔
        (kummerChar h b g).val + (kummerChar h b g').val < n) :
    kummerSymbolUnits h (mulZMod n) a b = 1 ↔
      ∃ c : (↥E)ˣ, Algebra.norm k (c : ↥E) = (a : k) := by
  rw [← mem_ker_cyclicBrauerHom_iff hσ₀, MonoidHom.mem_ker]
  have hb := smoothBrauerHom_kummerSymbolUnits h E hσ₀ a b hcarry
  constructor
  · intro hs
    rw [hs, map_one, eq_comm, inv_eq_one] at hb
    exact hb
  · intro hc
    refine smoothBrauerHom_injective ?_
    rw [hb, hc, inv_one, map_one]

end SymbolCyclicAlgebra

end InverseGalois.CFT

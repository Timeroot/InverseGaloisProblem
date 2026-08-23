/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.ExpEquiv
import InverseGalois.CFT.Local.FiltrationAction
import InverseGalois.CFT.Tate.Congr

/-!
# The exponential commutes with an isometric action

A ring automorphism preserving the valuation is continuous, because the sets cut out by the
valuation form a basis of neighbourhoods of zero and are permuted by such an automorphism.  Being
continuous it commutes with infinite sums, and being a ring homomorphism it carries each term of
the exponential series to the corresponding term for the transformed argument.  So the exponential
is equivariant, and the isomorphism it induces between a step of the additive filtration and the
corresponding step of the unit filtration is an isomorphism of modules over the acting group.  The
two steps therefore have the same Herbrand quotient.

## Main results

* `InverseGalois.CFT.continuous_smul_of_valued`: an isometric ring automorphism is continuous.
* `InverseGalois.CFT.smul_padicExp`: **the exponential is equivariant.**
* `InverseGalois.CFT.padicExpEquiv_equivariant`: the induced isomorphism is equivariant.
* `InverseGalois.CFT.herbrand_unitFiltrationAut`: **a deep enough step of the unit filtration has
  the same Herbrand quotient as the corresponding step of the additive filtration.**

## Tags

valued field, exponential, isometry, unit filtration, Herbrand quotient
-/

namespace InverseGalois.CFT

open scoped WithZero

variable {G A : Type*} [Group G] [Field A] [Valued A ℤᵐ⁰] [MulSemiringAction G A]
  (hv : ∀ (σ : G) (x : A), Valued.v (σ • x) = Valued.v x)

include hv

/-! ### Continuity -/

/-- **A ring automorphism preserving the valuation is continuous.**  It suffices to check
continuity at zero, where the sets cut out by the valuation are a basis of neighbourhoods and are
preserved. -/
theorem continuous_smul_of_valued (σ : G) : Continuous (fun x : A => σ • x) := by
  have hcont : ContinuousAt (MulSemiringAction.toRingHom G A σ) 0 := by
    rw [ContinuousAt, map_zero, Filter.tendsto_def]
    intro U hU
    obtain ⟨γ, hγ⟩ := (Valued.is_topological_valuation U).mp hU
    refine (Valued.is_topological_valuation _).mpr ⟨γ, fun x hx => ?_⟩
    refine hγ ?_
    show Valued.v (σ • x) < (γ : ℤᵐ⁰)
    rw [hv]
    exact hx
  exact continuous_of_continuousAt_zero (MulSemiringAction.toRingHom G A σ) hcont

/-! ### Equivariance of the exponential -/

variable [CompleteSpace A] {p e : ℕ}

omit hv [Valued A ℤᵐ⁰] [CompleteSpace A] in
/-- A ring automorphism carries a term of the exponential series to the corresponding term for the
transformed argument. -/
theorem smul_expTerm (σ : G) (x : A) (k : ℕ) : σ • expTerm x k = expTerm (σ • x) k := by
  show MulSemiringAction.toRingHom G A σ (expTerm x k) = expTerm (σ • x) k
  rw [expTerm, expTerm, map_div₀, map_pow, map_natCast]
  rfl

omit [CompleteSpace A] in
/-- An isometric action preserves the steps of the additive filtration. -/
theorem valued_smul_le (σ : G) {x : A} {j : ℤ} (hx : Valued.v x ≤ WithZero.exp (-j)) :
    Valued.v (σ • x) ≤ WithZero.exp (-j) := by
  rw [hv]
  exact hx

/-- **The exponential is equivariant** under an isometric action. -/
theorem smul_padicExp (h : HasResidueChar A p e) {j : ℤ} (hj : (e : ℤ) < j * ((p : ℤ) - 1))
    {x : A} (hx : Valued.v x ≤ WithZero.exp (-j)) (σ : G) :
    σ • padicExp x = padicExp (σ • x) := by
  have hmap : HasSum (fun k => σ • expTerm x k) (σ • padicExp x) := by
    have := (hasSum_expTerm h hx hj).map (MulSemiringAction.toRingHom G A σ)
      (continuous_smul_of_valued hv σ)
    exact this
  have hmap' : HasSum (expTerm (σ • x)) (σ • padicExp x) := by
    simpa only [smul_expTerm] using hmap
  exact ((hasSum_expTerm h (valued_smul_le hv σ hx) hj).unique hmap').symm

/-! ### Equivariance of the isomorphism -/

/-- The isomorphism between a step of the additive filtration and the corresponding step of the
unit filtration is equivariant. -/
theorem padicExpEquiv_equivariant (h : HasResidueChar A p e) {i : ℕ}
    (hi : (e : ℤ) < ((i : ℤ) + 1) * ((p : ℤ) - 1)) (σ : G)
    (x : ↥(valAddSubgroup A ((i : ℤ) + 1))) :
    padicExpEquiv h hi (valAddSubgroupAut hv σ ((i : ℤ) + 1) x)
      = unitFiltrationAut hv σ i (padicExpEquiv h hi x) := by
  refine Subtype.ext (Additive.toMul.injective (Units.ext ?_))
  show padicExp ((valAddSubgroupAut hv σ ((i : ℤ) + 1) x : ↥(valAddSubgroup A ((i : ℤ) + 1))) : A)
    = ((Additive.toMul (smulUnitsAut σ (padicExpEquiv h hi x : Additive Aˣ)) : Aˣ) : A)
  rw [coe_valAddSubgroupAut, coe_smulUnitsAut_apply, coe_padicExpEquiv,
    smul_padicExp hv h hi (mem_valAddSubgroup.mp x.2) σ]

/-- **A deep enough step of the unit filtration has the same Herbrand quotient as the
corresponding step of the additive filtration.** -/
theorem herbrand_unitFiltrationAut (h : HasResidueChar A p e) {i : ℕ}
    (hi : (e : ℤ) < ((i : ℤ) + 1) * ((p : ℤ) - 1)) (σ : G) (n : ℕ) :
    herbrand (valAddSubgroupAut hv σ ((i : ℤ) + 1)) n = herbrand (unitFiltrationAut hv σ i) n :=
  herbrand_congr (padicExpEquiv h hi) (padicExpEquiv_equivariant hv h hi σ) n

end InverseGalois.CFT

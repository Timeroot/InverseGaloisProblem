/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.LocalReciprocity
import InverseGalois.CFT.Local.NormValued

/-!
# Local reciprocity for an arbitrary finite extension

The base change formula for the invariant map of a local field is stated for an extension carrying
an absolute value that restricts to the absolute value of the base.  A finite extension of a local
field carries a canonical valuation — the value of the field norm — but the absolute value read off
from it through the comparison map of the base is the degree-th power of the absolute value below,
so the formula does not apply to it as it stands.

The correction is a change of scale.  A comparison map of a rank one valuation may be composed with
the degree-th root, which is again a strictly monotone map into the nonnegative reals killing zero
and fixing one, so it is again a comparison map for the same valuation; and the absolute value it
defines restricts on the base to the absolute value of the base, because the value of the norm of a
scalar is the degree-th power of its value.  Every hypothesis of the base change formula is then
available, and none of them appears in its conclusion.

So the relative Brauer group of a finite Galois extension of a local field is the subgroup of
classes killed by the degree, and has exactly as many elements as the degree, **with no hypothesis
on the ramification, on the Galois group, or on the absolute value of the extension** — only on the
base field, which is asked to be complete, discretely valued and locally compact.

## Main definitions

* `InverseGalois.CFT.rankOneHomRoot`: the comparison map of a rank one valuation composed with a
  root.

## Main results

* `InverseGalois.CFT.brauerTorsion_le_relative_of_finrank`: **a class over a local field killed by
  the degree of a finite extension is split by that extension.**
* `InverseGalois.CFT.relative_eq_brauerTorsion_of_finrank`: **the relative Brauer group of a finite
  Galois extension of a local field is the subgroup of classes killed by the degree.**
* `InverseGalois.CFT.card_relative_eq_finrank`: **the relative Brauer group of a finite Galois
  extension of a local field has exactly as many elements as the degree.**

## Tags

Brauer group, relative Brauer group, local field, invariant map, local reciprocity,
spectral norm, class field theory
-/

namespace InverseGalois.CFT

open Module

open scoped NNReal Valued WithZero

/-! ### A generator of the value group of either sign -/

section Generator

variable {A : Type*} [Field A] [Valued A ℤᵐ⁰] {m : ℤ}

/-- **The opposite of a generator of the value group is again one.** -/
theorem IsUnitValGen.neg (h : IsUnitValGen A m) : IsUnitValGen A (-m) where
  ne_zero := neg_ne_zero.2 h.ne_zero
  dvd x := neg_dvd.2 (h.dvd x)
  exists_eq := by
    obtain ⟨x, hx⟩ := h.exists_eq
    exact ⟨-x, by rw [map_neg, hx]⟩

end Generator

/-! ### The comparison map corrected by a root -/

section Root

variable (K : Type) [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] {n : ℕ}

/-- **The comparison map of a rank one valuation composed with a root.**  Raising to a positive
real power is a strictly monotone map of the nonnegative reals killing zero, fixing one and
preserving products, so the composite is again a comparison map. -/
noncomputable def rankOneHomRoot (hn : n ≠ 0) : ℤᵐ⁰ →*₀ ℝ≥0 where
  toFun γ := Valuation.RankOne.hom (Valued.v : Valuation K ℤᵐ⁰) γ ^ ((n : ℝ)⁻¹)
  map_zero' := by
    rw [map_zero]
    exact NNReal.zero_rpow (inv_ne_zero (Nat.cast_ne_zero.2 hn))
  map_one' := by rw [map_one, NNReal.one_rpow]
  map_mul' x y := by
    rw [map_mul, NNReal.mul_rpow]

theorem rankOneHomRoot_apply (hn : n ≠ 0) (γ : ℤᵐ⁰) :
    rankOneHomRoot K hn γ
      = Valuation.RankOne.hom (Valued.v : Valuation K ℤᵐ⁰) γ ^ ((n : ℝ)⁻¹) := rfl

/-- **The corrected comparison map undoes a power.** -/
theorem rankOneHomRoot_pow (hn : n ≠ 0) (γ : ℤᵐ⁰) :
    rankOneHomRoot K hn (γ ^ n) = Valuation.RankOne.hom (Valued.v : Valuation K ℤᵐ⁰) γ := by
  rw [rankOneHomRoot_apply, map_pow, ← NNReal.rpow_natCast _ n, ← NNReal.rpow_mul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn), NNReal.rpow_one]

/-- The corrected comparison map is strictly monotone. -/
theorem strictMono_rankOneHomRoot (hn : n ≠ 0) : StrictMono (rankOneHomRoot K hn) := by
  intro x y hxy
  exact NNReal.rpow_lt_rpow (Valuation.RankOne.strictMono (Valued.v : Valuation K ℤᵐ⁰) hxy)
    (inv_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)))

end Root

/-! ### Local reciprocity with no hypothesis on the extension -/

section Reciprocity

variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K]
  {mK : ℤ} {p e : ℕ}

variable (M : Type) [Field M] [Algebra K M] [FiniteDimensional K M]

/-- **A finite extension of a local field is again a local field.**  It carries the valuation of
the field norm; the comparison map of the base corrected by the degree-th root turns that valuation
into an absolute value restricting to the absolute value of the base; the extension is complete and
locally compact for it; its residue field has the same characteristic as that of the base; and its
value group has a generator. -/
theorem exists_valued_of_finiteDimensional (hres : HasResidueChar K p e)
    (hmK : IsUnitValGen K mK) :
    ∃ (_ : Valued M ℤᵐ⁰) (_ : Valuation.RankOne (Valued.v : Valuation M ℤᵐ⁰))
      (_ : CompleteSpace M) (_ : ProperSpace M) (e' : ℕ) (mM : ℤ),
        (∀ x : K, ‖algebraMap K M x‖ = ‖x‖) ∧ HasResidueChar M p e' ∧ IsUnitValGen M mM := by
  haveI : Algebra.IsAlgebraic K M := Algebra.IsAlgebraic.of_finite K M
  have hn : finrank K M ≠ 0 := Module.finrank_pos.ne'
  have hnt : ∃ x : Kˣ, Valued.v (x : K) ≠ 1 := exists_units_val_ne_one_of_isUnitValGen hmK
  letI : Valued M ℤᵐ⁰ := normValued K M
  have hvM : ∀ y : M, Valued.v y = Valued.v (Algebra.norm K y) := fun _ => rfl
  haveI : CompleteSpace M := spectralNorm.completeSpace K M
  letI : Valuation.RankOne (Valued.v : Valuation M ℤᵐ⁰) :=
    { hom := rankOneHomRoot K hn
      strictMono' := strictMono_rankOneHomRoot K hn
      exists_val_nontrivial := by
        obtain ⟨x, hx⟩ := exists_units_val_ne_one_of_norm hvM hnt
        exact ⟨(x : M), valued_unit_ne_zero x, hx⟩ }
  haveI : WeaklyLocallyCompactSpace M := weaklyLocallyCompactSpace_spectral K M
  haveI : ProperSpace M := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace M
  have hnorm : ∀ x : K, ‖algebraMap K M x‖ = ‖x‖ := by
    intro x
    have h1 : (Valued.v (algebraMap K M x) : ℤᵐ⁰) = Valued.v x ^ finrank K M := by
      rw [hvM, Algebra.norm_algebraMap, map_pow]
    have h2 : ‖algebraMap K M x‖
        = ((Valuation.RankOne.hom (Valued.v : Valuation M ℤᵐ⁰)
            (Valued.v (algebraMap K M x)) : ℝ≥0) : ℝ) := rfl
    have h3 : ‖x‖
        = ((Valuation.RankOne.hom (Valued.v : Valuation K ℤᵐ⁰) (Valued.v x) : ℝ≥0) : ℝ) := rfl
    rw [h2, h3, h1]
    exact congrArg NNReal.toReal (rankOneHomRoot_pow K hn (Valued.v x))
  obtain ⟨e', hresM⟩ := exists_hasResidueChar_of_norm hnorm hres
  obtain ⟨mM, hmM⟩ := exists_isUnitValGen (exists_units_val_ne_one_of_norm hvM hnt)
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, e', mM, hnorm, hresM, hmM⟩

/-- **A class over a local field killed by the degree of a finite extension is split by that
extension.**  The extension is again a local field, with an absolute value restricting to the
absolute value of the base, so the base change formula for the invariant map applies: the invariant
of the class computed upstairs is the degree times its invariant downstairs, hence trivial, and a
class over a local field is determined by its invariant. -/
theorem brauerTorsion_le_relative_of_finrank (hres : HasResidueChar K p e)
    (hmK : IsUnitValGen K mK) :
    brauerTorsion K (finrank K M) ≤ BrauerGroup.relative K M := by
  obtain ⟨_, _, _, _, e', mM, hnorm, hresM, hmM⟩ := exists_valued_of_finiteDimensional M hres hmK
  rcases lt_or_gt_of_ne (mul_ne_zero hmK.ne_zero hmM.ne_zero) with hlt | hgt
  · refine brauerTorsion_le_relative M hnorm hresM hmK hmM.neg ?_
    rw [mul_neg]
    exact neg_pos.2 hlt
  · exact brauerTorsion_le_relative M hnorm hresM hmK hmM hgt

/-- **The relative Brauer group of a finite Galois extension of a local field is the subgroup of
classes killed by the degree.**  The classes it contains are killed by the degree because the
cohomology of a finite group is killed by its order, and every class killed by the degree is split
because the invariant map multiplies by the degree under base change. -/
theorem relative_eq_brauerTorsion_of_finrank [IsGalois K M] (hres : HasResidueChar K p e)
    (hmK : IsUnitValGen K mK) :
    BrauerGroup.relative K M = brauerTorsion K (finrank K M) :=
  le_antisymm (relative_le_brauerTorsion M) (brauerTorsion_le_relative_of_finrank M hres hmK)

/-- **The relative Brauer group of a finite Galois extension of a local field has exactly as many
elements as the degree.**  It is the subgroup of classes killed by the degree, and the classes of
the Brauer group of a local field killed by a number are that number in size. -/
theorem card_relative_eq_finrank [IsGalois K M] (hres : HasResidueChar K p e)
    (hmK : IsUnitValGen K mK) :
    Nat.card ↥(BrauerGroup.relative K M) = finrank K M := by
  haveI : NeZero (finrank K M) := ⟨Module.finrank_pos.ne'⟩
  rw [relative_eq_brauerTorsion_of_finrank M hres hmK,
    natCard_brauerTorsion K hres hmK (finrank K M)]

/-- **The invariant map of a local field is onto the classes killed by the degree of a finite
Galois extension**, and every value it takes there is the invariant of a class split by that
extension. -/
theorem exists_mem_relative_localInvariantHom_eq [IsGalois K M] (hres : HasResidueChar K p e)
    (hmK : IsUnitValGen K mK) (y : Multiplicative QModZ)
    (hy : y ^ finrank K M = 1) :
    ∃ x ∈ BrauerGroup.relative K M, localInvariantHom K hmK x = y := by
  obtain ⟨x, hx⟩ := localInvariantHom_surjective K hmK y
  refine ⟨x, ?_, hx⟩
  rw [relative_eq_brauerTorsion_of_finrank M hres hmK, mem_brauerTorsion]
  refine localInvariantHom_injective K hres hmK ?_
  rw [map_pow, hx, hy, map_one]

end Reciprocity

/-! ### Local reciprocity over an intermediate field -/

section Tower

variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K]
  {mK : ℤ} {p e : ℕ}

variable (M L : Type) [Field M] [Field L] [Algebra K M] [FiniteDimensional K M] [Algebra M L]
  [FiniteDimensional M L]

/-- **The relative Brauer group of a finite Galois extension of an intermediate field of a finite
extension of a local field has exactly as many elements as the degree.**  The intermediate field is
again a local field, so local reciprocity applies over it. -/
theorem card_relative_eq_finrank_tower [IsGalois M L] (hres : HasResidueChar K p e)
    (hmK : IsUnitValGen K mK) :
    Nat.card ↥(BrauerGroup.relative M L) = finrank M L := by
  obtain ⟨_, _, _, _, e', mM, _, hresM, hmM⟩ := exists_valued_of_finiteDimensional M hres hmK
  exact card_relative_eq_finrank L hresM hmM

/-- **The relative Brauer group of a finite Galois extension of an intermediate field of a finite
extension of a local field is finite.** -/
theorem finite_relative_tower [IsGalois M L] (hres : HasResidueChar K p e)
    (hmK : IsUnitValGen K mK) :
    Finite ↥(BrauerGroup.relative M L) := by
  obtain ⟨_, _, _, _, e', mM, _, hresM, hmM⟩ := exists_valued_of_finiteDimensional M hres hmK
  exact finite_relative_local L hresM hmM

end Tower

end InverseGalois.CFT

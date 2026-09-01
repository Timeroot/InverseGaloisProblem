/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.AdicUnramified
import InverseGalois.CFT.Brauer.CyclicInvariant
import InverseGalois.CFT.Brauer.FrobeniusTower

/-!
# The normalised invariant of a Brauer class split by an unramified extension

The invariant of a Brauer class split by an unramified cyclic extension depends on the choice of a
generator of the Galois group: replacing the generator by another one rescales the invariant.  An
unramified extension of a local field has a canonical generator, its Frobenius automorphism, and
the invariant taken with respect to it is the **normalised** invariant.

Because the Frobenius automorphism of a larger unramified extension restricts to the Frobenius
automorphism of a smaller one, the normalised invariant computed at two levels of an unramified
tower agrees.  So the normalisation is what turns the invariant of a cyclic algebra into an
invariant of the Brauer class alone.

## Main definitions

* `InverseGalois.CFT.localInvariant`: the invariant of a Brauer class split by an unramified
  extension of a local field, normalised by the Frobenius automorphism.

## Main results

* `InverseGalois.CFT.localInvariant_apply_cyclicBrauerHom`: the normalised invariant of the class
  of a cyclic algebra is the invariant of its scalar.
* `InverseGalois.CFT.exists_localInvariant_eq`: **the normalised invariant attains the reciprocal
  of the degree.**
* `InverseGalois.CFT.localInvariant_tower`: **the normalised invariant does not depend on the level
  of the unramified tower.**

## Tags

Brauer group, local field, unramified extension, Frobenius, invariant map, class field theory
-/

namespace InverseGalois.CFT

open Module

open scoped Valued WithZero

/-! ### Changing the generator -/

section Generator

variable {K L : Type} [Field K] [Valued K ℤᵐ⁰] [Field L] [Algebra K L] [FiniteDimensional K L]
  [IsGalois K L] {m : ℤ}

/-- The invariant of a Brauer class only depends on the generator of the Galois group, not on the
proof that it generates. -/
theorem brauerInvariant_congr_apply {σ₀ σ₁ : Gal(L/K)} (h : σ₀ = σ₁)
    (hσ₀ : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers σ₀)
    (hσ₁ : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers σ₁)
    (hur : HasUnramifiedNormValues K L) (hm : IsUnitValGen K m)
    (y : ↥(BrauerGroup.relative K L)) :
    brauerInvariant hσ₀ hur hm y = brauerInvariant hσ₁ hur hm y := by
  subst h
  rfl

end Generator

variable {K L : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K] {m : ℤ}
variable [Field L] [Algebra K L] [FiniteDimensional K L]

/-! ### Unramifiedness in the two languages -/

/-- The absolute-value form of unramifiedness gives the valuation form. -/
theorem hasUnramifiedNormValues_of_divisionNorm
    (hur : ∀ z : L, z ≠ 0 → ∃ c : K, c ≠ 0 ∧ divisionNorm K L z = ‖c‖) :
    HasUnramifiedNormValues K L :=
  hasUnramifiedNormValues_of_spectralNorm fun z hz => by
    obtain ⟨c, hc, hcz⟩ := hur z hz
    exact ⟨c, hc, by rw [← divisionNorm_eq_spectralNorm, hcz]⟩

/-! ### The normalised invariant -/

variable [IsGalois K L]

variable (K L) in
/-- **The normalised invariant of a Brauer class split by an unramified extension of a local
field**: the invariant taken with respect to the Frobenius automorphism. -/
noncomputable def localInvariant
    (hur : ∀ z : L, z ≠ 0 → ∃ c : K, c ≠ 0 ∧ divisionNorm K L z = ‖c‖) (hm : IsUnitValGen K m) :
    ↥(BrauerGroup.relative K L) →* Multiplicative QModZ :=
  brauerInvariant (forall_mem_zpowers_divisionFrobenius K L hur)
    (hasUnramifiedNormValues_of_divisionNorm hur) hm

/-- The normalised invariant of the class of a cyclic algebra for the Frobenius automorphism is the
invariant of its scalar. -/
theorem localInvariant_apply_cyclicBrauerHom
    (hur : ∀ z : L, z ≠ 0 → ∃ c : K, c ≠ 0 ∧ divisionNorm K L z = ‖c‖) (hm : IsUnitValGen K m)
    (a : Kˣ) :
    localInvariant K L hur hm
        ⟨cyclicBrauerHom (forall_mem_zpowers_divisionFrobenius K L hur) a,
          cyclicBrauerHom_mem_relative (forall_mem_zpowers_divisionFrobenius K L hur) a⟩
      = baseInvariant hm (finrank K L) a :=
  brauerInvariant_apply_cyclicBrauerHom _ _ hm a

/-- **The normalised invariant attains the reciprocal of the degree.** -/
theorem exists_localInvariant_eq
    (hur : ∀ z : L, z ≠ 0 → ∃ c : K, c ≠ 0 ∧ divisionNorm K L z = ‖c‖) (hm : IsUnitValGen K m) :
    ∃ y : ↥(BrauerGroup.relative K L), localInvariant K L hur hm y
      = Multiplicative.ofAdd (QuotientAddGroup.mk (1 / (finrank K L : ℚ)) : QModZ) := by
  obtain ⟨x, hx⟩ := exists_unitInvariant_eq hm (finrank K L)
  refine ⟨⟨cyclicBrauerHom (forall_mem_zpowers_divisionFrobenius K L hur) (Additive.toMul x),
    cyclicBrauerHom_mem_relative _ _⟩, ?_⟩
  rw [localInvariant_apply_cyclicBrauerHom, baseInvariant_apply]
  exact congrArg Multiplicative.ofAdd hx

/-! ### Independence of the level of the unramified tower -/

section Tower

variable {L' : Type} [Field L'] [Algebra K L'] [FiniteDimensional K L'] [IsGalois K L']
variable [Algebra L L'] [IsScalarTower K L L']

/-- **The normalised invariant does not depend on the level of the unramified tower.**  The
Frobenius automorphism of the larger extension restricts to the Frobenius automorphism of the
smaller one, so the two normalisations agree. -/
theorem localInvariant_tower
    (hur' : ∀ z : L', z ≠ 0 → ∃ c : K, c ≠ 0 ∧ divisionNorm K L' z = ‖c‖)
    (hm : IsUnitValGen K m) (x : ↥(BrauerGroup.relative K L)) :
    localInvariant K L' hur' hm
        ⟨(x : BrauerGroup K), BrauerGroup.relative_le_relative K L L' x.2⟩
      = localInvariant K L (unramified_of_unramified_tower hur') hm x := by
  refine (brauerInvariant_tower (forall_mem_zpowers_divisionFrobenius K L' hur')
    (hasUnramifiedNormValues_of_divisionNorm (unramified_of_unramified_tower hur'))
    (hasUnramifiedNormValues_of_divisionNorm hur') hm x).trans ?_
  exact brauerInvariant_congr_apply (restrictNormal_divisionFrobenius hur') _ _ _ hm x

end Tower

end InverseGalois.CFT

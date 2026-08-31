/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.CyclicNorm
import InverseGalois.CFT.Brauer.RelativeTorsion
import InverseGalois.CFT.Local.CyclicNormIndex

/-!
# The norm residue symbol of a cyclic extension of a local field

For a finite cyclic Galois extension `L / K` of a local field, with a chosen generator `σ₀` of the
Galois group, the invariant of the cyclic algebra `(L / K, σ₀, a)` is a homomorphism from the units
of `K` to the rationals modulo the integers.  This is the norm residue symbol of the extension: it
vanishes exactly on the norms from `L`, and it takes every value killed by the degree.

The two facts behind it are that the cyclic algebra construction identifies `Kˣ / N(Lˣ)` with the
relative Brauer group and that the norm index of a cyclic extension of a local field is the degree.
Together they compute the relative Brauer group of an *arbitrary* cyclic extension of a local field:
it has as many elements as the degree, and it is exactly the subgroup of classes killed by the
degree.  Neither statement asks the extension to be unramified.

## Main definitions

* `InverseGalois.CFT.cyclicNormResidue`: **the norm residue symbol of a cyclic extension of a local
  field**, the invariant of the cyclic algebra with the given scalar.

## Main results

* `InverseGalois.CFT.natCard_relative_eq_finrank_of_cyclic`: **the relative Brauer group of a cyclic
  extension of a local field has as many elements as the degree.**
* `InverseGalois.CFT.relative_eq_brauerTorsion_of_cyclic`: **the relative Brauer group of a cyclic
  extension of a local field is the subgroup of classes killed by the degree.**
* `InverseGalois.CFT.cyclicNormResidue_eq_one_iff`: **the norm residue symbol of a unit vanishes
  exactly when the unit is a norm.**
* `InverseGalois.CFT.exists_cyclicNormResidue_eq`: **the norm residue symbol attains the reciprocal
  of the degree**, so it is onto the classes killed by the degree.

## Tags

Brauer group, local field, cyclic extension, norm residue symbol, invariant map,
class field theory
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open Module

open scoped Valued WithZero

section CyclicNormResidue

variable {K L : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  {σ₀ : Gal(L/K)} {m : ℤ} {p e : ℕ}

/-! ### The relative Brauer group of a cyclic extension -/

/-- **The relative Brauer group of a cyclic extension of a local field has as many elements as the
degree.**  The cyclic algebra construction identifies it with the units of the base field modulo the
norms, and that quotient has the order of the degree. -/
theorem natCard_relative_eq_finrank_of_cyclic
    (hsigma : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers σ₀) (hres : HasResidueChar K p e) :
    Nat.card ↥(BrauerGroup.relative K L) = finrank K L := by
  haveI : IsCyclic (L ≃ₐ[K] L) := ⟨⟨σ₀, hsigma⟩⟩
  rw [← index_normSubgroup_eq_finrank_local K L hres, Subgroup.index_eq_card,
    Nat.card_congr (cyclicBrauerEquiv hsigma).toEquiv]

/-- **The relative Brauer group of a cyclic extension of a local field is the subgroup of classes
killed by the degree.**  Both have the order of the degree, and one contains the other. -/
theorem relative_eq_brauerTorsion_of_cyclic
    (hsigma : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers σ₀) (hres : HasResidueChar K p e)
    (hm : IsUnitValGen K m) :
    BrauerGroup.relative K L = brauerTorsion K (finrank K L) := by
  haveI : NeZero (finrank K L) := ⟨Module.finrank_pos.ne'⟩
  haveI := finite_brauerTorsion hres hm (finrank K L)
  refine Subgroup.eq_of_le_of_card_ge (relative_le_brauerTorsion L) ?_
  rw [natCard_relative_eq_finrank_of_cyclic hsigma hres]
  exact le_of_eq (natCard_brauerTorsion K hres hm (finrank K L))

/-! ### The norm residue symbol -/

variable (hsigma : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers σ₀)

/-- **The norm residue symbol of a cyclic extension of a local field**: the invariant of the cyclic
algebra whose scalar is the given unit. -/
noncomputable def cyclicNormResidue (hm : IsUnitValGen K m) : Kˣ →* Multiplicative QModZ :=
  (localInvariantHom K hm).comp (cyclicBrauerHom hsigma)

theorem cyclicNormResidue_apply (hm : IsUnitValGen K m) (a : Kˣ) :
    cyclicNormResidue hsigma hm a = localInvariantHom K hm (cyclicBrauerHom hsigma a) := rfl

/-- **The norm residue symbol vanishes exactly on the norms.**  The invariant map of a local field
is injective, so the symbol has the kernel of the cyclic algebra construction. -/
theorem ker_cyclicNormResidue (hres : HasResidueChar K p e) (hm : IsUnitValGen K m) :
    (cyclicNormResidue hsigma hm).ker = normSubgroup K L := by
  rw [← ker_cyclicBrauerHom hsigma]
  ext a
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, cyclicNormResidue_apply]
  exact ⟨fun h => localInvariantHom_injective K hres hm (by rw [h, map_one]),
    fun h => by rw [h, map_one]⟩

/-- **A unit has trivial norm residue symbol exactly when it is a norm.** -/
theorem cyclicNormResidue_eq_one_iff (hres : HasResidueChar K p e) (hm : IsUnitValGen K m)
    (a : Kˣ) :
    cyclicNormResidue hsigma hm a = 1 ↔ ∃ b : Lˣ, Algebra.norm K (b : L) = (a : K) := by
  rw [← MonoidHom.mem_ker, ker_cyclicNormResidue hsigma hres hm, mem_normSubgroup_iff]

/-- The norm residue symbol takes values killed by the degree. -/
theorem pow_cyclicNormResidue_eq_one (hm : IsUnitValGen K m) (a : Kˣ) :
    cyclicNormResidue hsigma hm a ^ finrank K L = 1 := by
  rw [cyclicNormResidue_apply, ← map_pow]
  rw [pow_finrank_eq_one_of_mem_relative _ (cyclicBrauerHom_mem_relative hsigma a), map_one]

/-- **The norm residue symbol attains the reciprocal of the degree.**  Every class killed by the
degree is split by the extension, hence is the class of a cyclic algebra. -/
theorem exists_cyclicNormResidue_eq (hres : HasResidueChar K p e) (hm : IsUnitValGen K m) :
    ∃ a : Kˣ, cyclicNormResidue hsigma hm a
      = Multiplicative.ofAdd (QuotientAddGroup.mk (1 / (finrank K L : ℚ)) : QModZ) := by
  haveI : NeZero (finrank K L) := ⟨Module.finrank_pos.ne'⟩
  have hn : ((finrank K L : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne _)
  have hzero : finrank K L •
      (QuotientAddGroup.mk (1 / (finrank K L : ℚ)) : QModZ) = 0 := by
    have h1 : (QuotientAddGroup.mk (finrank K L • (1 / (finrank K L : ℚ))) : QModZ)
        = finrank K L • (QuotientAddGroup.mk (1 / (finrank K L : ℚ)) : QModZ) := by
      rw [← QuotientAddGroup.mk'_apply, ← QuotientAddGroup.mk'_apply, map_nsmul]
    rw [← h1, nsmul_eq_mul, mul_one_div, div_self hn]
    exact (QModZ.mk_eq_zero_iff _).2 ⟨1, by norm_num⟩
  obtain ⟨x, hx⟩ := localInvariantHom_surjective K hm
    (Multiplicative.ofAdd (QuotientAddGroup.mk (1 / (finrank K L : ℚ)) : QModZ))
  have hxt : x ∈ BrauerGroup.relative K L := by
    rw [relative_eq_brauerTorsion_of_cyclic hsigma hres hm, mem_brauerTorsion]
    refine localInvariantHom_injective K hres hm ?_
    rw [map_pow, hx, map_one]
    exact (pow_eq_one_iff_nsmul_toAdd _ _).2 hzero
  obtain ⟨a, ha⟩ := exists_cyclicBrauerHom_eq hsigma x hxt
  exact ⟨a, by rw [cyclicNormResidue_apply, ha, hx]⟩

end CyclicNormResidue

end InverseGalois.CFT

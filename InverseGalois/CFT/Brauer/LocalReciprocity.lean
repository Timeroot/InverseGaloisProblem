/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.InvariantBaseChange
import InverseGalois.CFT.Brauer.RelativeTorsion

/-!
# The relative Brauer group of an arbitrary extension of local fields

The classes of the Brauer group of a local field killed by a number `n` are `n` in number, and the
relative Brauer group of a finite Galois extension consists of classes killed by the degree.  The
base-change formula for the invariant map supplies the converse inclusion: a class killed by the
degree has invariant zero upstairs, hence is trivial upstairs because the invariant map of the
extension is injective.  So the relative Brauer group of a finite Galois extension of local fields
is exactly the subgroup of classes killed by the degree, and it has exactly as many elements as the
degree.  This is the local reciprocity count, with no hypothesis on the ramification and none on
the Galois group.

The residue characteristic of the extension is not an extra hypothesis: the absolute values agree,
so the residue characteristic downstairs is a prime of absolute value less than one upstairs.

## Main results

* `InverseGalois.CFT.exists_hasResidueChar_of_norm`: an extension of a local field on which the
  absolute value extends has the same residue characteristic.
* `InverseGalois.CFT.brauerTorsion_le_relative`: **a class over a local field killed by the degree
  of a finite extension is split by that extension.**
* `InverseGalois.CFT.relative_eq_brauerTorsion`: **the relative Brauer group of a finite Galois
  extension of local fields is the subgroup of classes killed by the degree.**
* `InverseGalois.CFT.card_relative_eq_finrank_of_valued`: **the relative Brauer group of a finite
  Galois extension of local fields has exactly as many elements as the degree.**

## Tags

Brauer group, relative Brauer group, local field, invariant map, local reciprocity,
class field theory
-/

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open Module

open scoped Valued WithZero

section Reciprocity

variable {K M : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K]
variable [Field M] [Valued M ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation M ℤᵐ⁰)] [CompleteSpace M] [ProperSpace M]
variable [Algebra K M] [FiniteDimensional K M] {mK mM : ℤ} {p e : ℕ}

omit [CompleteSpace K] [ProperSpace K] [CompleteSpace M] [ProperSpace M]
  [FiniteDimensional K M] in
/-- **An extension of a local field on which the absolute value extends has the same residue
characteristic.**  The residue characteristic downstairs is a prime whose absolute value is less
than one, and its absolute value upstairs is the same, so its valuation upstairs is again the
exponential of a negative integer. -/
theorem exists_hasResidueChar_of_norm (hnorm : ∀ x : K, ‖algebraMap K M x‖ = ‖x‖)
    (hresK : HasResidueChar K p e) : ∃ e' : ℕ, HasResidueChar M p e' := by
  have hepos := hresK.pos
  have hpK : ((p : ℕ) : K) ≠ 0 := hresK.natCast_ne_zero hresK.prime.ne_zero
  have hpM : ((p : ℕ) : M) = algebraMap K M ((p : ℕ) : K) := (map_natCast _ p).symm
  have hne : ((p : ℕ) : M) ≠ 0 := by
    rw [hpM]
    exact fun h => hpK ((map_eq_zero_iff _ (algebraMap K M).injective).1 h)
  have hlt1K : ‖((p : ℕ) : K)‖ < 1 := by
    refine Valued.toNormedField.norm_lt_one_iff.2 ?_
    rw [hresK.val_p, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.2 (by omega)
  have hlt1M : (Valued.v ((p : ℕ) : M) : ℤᵐ⁰) < 1 := by
    refine Valued.toNormedField.norm_lt_one_iff.1 ?_
    rw [hpM, hnorm]
    exact hlt1K
  have hv0 : (Valued.v ((p : ℕ) : M) : ℤᵐ⁰) ≠ 0 := (Valuation.ne_zero_iff _).2 hne
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (Valued.v ((p : ℕ) : M) : ℤᵐ⁰) = WithZero.exp n :=
    ⟨WithZero.log _, (WithZero.exp_log hv0).symm⟩
  have hnneg : n < 0 := by
    rw [hn, ← WithZero.exp_zero] at hlt1M
    exact WithZero.exp_lt_exp.1 hlt1M
  refine ⟨(-n).toNat, hresK.prime, by omega, ?_⟩
  rw [hn]
  congr 1
  omega

variable (M) in
/-- **A class over a local field killed by the degree of a finite extension is split by that
extension.**  Its invariant computed upstairs is the degree times its invariant computed
downstairs, hence trivial, and a class over a local field is determined by its invariant. -/
theorem brauerTorsion_le_relative (hnorm : ∀ x : K, ‖algebraMap K M x‖ = ‖x‖)
    (hresM : HasResidueChar M p e) (hmK : IsUnitValGen K mK) (hmM : IsUnitValGen M mM)
    (hsign : 0 < mK * mM) :
    brauerTorsion K (finrank K M) ≤ BrauerGroup.relative K M := by
  intro x hx
  rw [BrauerGroup.relative, MonoidHom.mem_ker]
  refine localInvariantHom_injective M hresM hmM ?_
  rw [map_one, localInvariantHom_baseChange hnorm hmK hmM hsign x, ← map_pow,
    mem_brauerTorsion.1 hx, map_one]

variable (M) in
/-- **The relative Brauer group of a finite Galois extension of local fields is the subgroup of
classes killed by the degree.**  The classes it contains are killed by the degree because the
cohomology of a finite group is killed by its order, and every class killed by the degree is split
because the invariant map multiplies by the degree under base change. -/
theorem relative_eq_brauerTorsion [IsGalois K M] (hnorm : ∀ x : K, ‖algebraMap K M x‖ = ‖x‖)
    (hresM : HasResidueChar M p e) (hmK : IsUnitValGen K mK) (hmM : IsUnitValGen M mM)
    (hsign : 0 < mK * mM) :
    BrauerGroup.relative K M = brauerTorsion K (finrank K M) :=
  le_antisymm (relative_le_brauerTorsion M)
    (brauerTorsion_le_relative M hnorm hresM hmK hmM hsign)

variable (M) in
/-- **The relative Brauer group of a finite Galois extension of local fields has exactly as many
elements as the degree.**  It is the subgroup of classes killed by the degree, and the classes of
the Brauer group of a local field killed by a number are that number in size. -/
theorem card_relative_eq_finrank_of_valued [IsGalois K M]
    (hnorm : ∀ x : K, ‖algebraMap K M x‖ = ‖x‖) (hresK : HasResidueChar K p e)
    (hmK : IsUnitValGen K mK) (hmM : IsUnitValGen M mM) (hsign : 0 < mK * mM) :
    Nat.card ↥(BrauerGroup.relative K M) = finrank K M := by
  haveI : NeZero (finrank K M) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨e', hresM⟩ := exists_hasResidueChar_of_norm hnorm hresK
  rw [relative_eq_brauerTorsion M hnorm hresM hmK hmM hsign,
    natCard_brauerTorsion K hresK hmK (finrank K M)]

end Reciprocity

end InverseGalois.CFT

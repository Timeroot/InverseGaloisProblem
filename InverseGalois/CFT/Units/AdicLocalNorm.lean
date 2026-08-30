/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.AdicHerbrand
import InverseGalois.CFT.Local.AdicUnramified
import InverseGalois.CFT.Local.InfiniteHerbrand
import InverseGalois.CFT.Units.LocalNorm

/-!
# Units of the valuation ring are local norms at a place that is unramified

At a finite place of a Galois extension of number fields the decomposition group is the Galois
group of the extension of completions, and the field norm of that local extension is the product of
the conjugates under the decomposition group, that is, the norm operator of the Tate formalism for
a generator.  So a local unit of the base field is a norm from the completion above exactly when it
is a value of that operator.

Two cases are settled here.  When the decomposition group is trivial the norm operator is the
identity and every local unit of the base field is a norm.  When the decomposition group is cyclic
and fixes a uniformizer, the zeroth Tate group of the units of the valuation ring of the completion
vanishes, so every unit of the valuation ring of the base which is fixed there — and a unit coming
from below always is — is a value of the norm operator on the units of the valuation ring above,
hence a norm.

These are the two local conditions that will be met at the places away from the single prime where
an auxiliary cyclic extension is allowed to ramify.  The same argument for a trivial decomposition
group applies verbatim at an infinite place that splits completely.

## Main results

* `InverseGalois.CFT.mem_normSubgroup_adicCompletion_of_subsingleton_stabilizer`: **at a place that
  splits completely every local unit of the base field is a norm.**
* `InverseGalois.CFT.mem_normSubgroup_adicCompletion_of_unitVal_eq_zero`: **at a place whose
  decomposition group is cyclic and fixes a uniformizer, every unit of the valuation ring of the
  base field is a norm.**
* `InverseGalois.CFT.mem_normSubgroup_adicCompletion_of_isUnramifiedAt`: **at an unramified place
  of a cyclic extension every unit of the valuation ring of the base field is a norm.**
* `InverseGalois.CFT.mem_normSubgroup_infiniteCompletion_of_subsingleton_stabilizer`: **at an
  infinite place that splits completely every local unit of the base field is a norm.**
* `InverseGalois.CFT.mem_normSubgroup_infiniteCompletion_of_isReal`: **at a real infinite place
  every local unit of the base field is a norm.**

## Tags

number field, adic completion, decomposition group, local norm, unramified
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

section AdicLocalNorm

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

variable (k) in
/-- **At a place that splits completely every local unit of the base field is a norm.**  The
decomposition group being trivial, the norm operator of the Tate formalism is the sum of a single
term, namely the identity, so the unit is its own norm. -/
theorem mem_normSubgroup_adicCompletion_of_subsingleton_stabilizer (w : HeightOneSpectrum (𝓞 K))
    (hsplit : Subsingleton ↥(stabilizer Gal(K/k) w))
    (a : ((primeUnder (𝓞 k) w).adicCompletion k)ˣ) :
    a ∈ normSubgroup ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K) := by
  haveI : Fintype ↥(stabilizer Gal(K/k) w) := Fintype.ofFinite _
  haveI := isGalois_adicCompletion k w
  have hcard : Nat.card ↥(stabilizer Gal(K/k) w) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨hsplit, ⟨1⟩⟩
  refine mem_normSubgroup_of_normHom_smulUnitsAut (exists_stabilizer_smul_eq k w)
    (τ := 1) (fun g => by rw [Subsingleton.elim g 1]; exact Subgroup.mem_zpowers 1)
    (b := adicUnitsComap k w (Additive.ofMul a)) ?_
  rw [hcard, normHom_apply, Finset.sum_range_one, pow_zero]
  rfl

variable (k) in
/-- **At a place whose decomposition group is cyclic and fixes a uniformizer, every unit of the
valuation ring of the base field is a norm.**  The zeroth Tate group of the units of the valuation
ring of the completion vanishes there, and a unit coming from below is fixed by the decomposition
group, so it is the norm operator applied to a unit of the valuation ring above; the norm operator
of a generator is the field norm. -/
theorem mem_normSubgroup_adicCompletion_of_unitVal_eq_zero (w : HeightOneSpectrum (𝓞 K))
    {σ : ↥(stabilizer Gal(K/k) w)} (hgen : ∀ g : ↥(stabilizer Gal(K/k) w), g ∈ Subgroup.zpowers σ)
    (π : (w.adicCompletion K)ˣ)
    (hπfix : ∀ g : ↥(stabilizer Gal(K/k) w),
      g • (π : w.adicCompletion K) = (π : w.adicCompletion K))
    (hπval : unitVal (Additive.ofMul π) = 1)
    {a : ((primeUnder (𝓞 k) w).adicCompletion k)ˣ} (ha : unitVal (Additive.ofMul a) = 0) :
    a ∈ normSubgroup ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K) := by
  haveI : Fintype ↥(stabilizer Gal(K/k) w) := Fintype.ofFinite _
  haveI := isGalois_adicCompletion k w
  haveI : NeZero (Nat.card ↥(stabilizer Gal(K/k) w)) := ⟨Nat.card_pos.ne'⟩
  have hσ : σ ^ Nat.card ↥(stabilizer Gal(K/k) w) = 1 := pow_card_eq_one'
  -- the unit, read in the completion above, is a unit of the valuation ring fixed by the group
  have hx0 : unitVal (adicUnitsComap k w (Additive.ofMul a)) = 0 :=
    (unitVal_adicUnitsComap_eq_zero_iff k w _).mpr ha
  have hxfix : smulUnitsAut σ (adicUnitsComap k w (Additive.ofMul a))
      = adicUnitsComap k w (Additive.ofMul a) := smulUnitsAut_adicUnitsComap k w σ _
  haveI := (subsingleton_tate_adicUnits w hgen hσ rfl π hπfix hπval).1
  obtain ⟨y, hy⟩ := exists_normHom_of_subsingleton
    (σ := kerUnitValAut (valued_smul_adicCompletion w) σ)
    (n := Nat.card ↥(stabilizer Gal(K/k) w))
    ⟨adicUnitsComap k w (Additive.ofMul a), hx0⟩ (Subtype.ext hxfix)
  -- reading that identity in the units of the completion exhibits the unit as a norm
  have hpush := map_normHom (σA := kerUnitValAut (valued_smul_adicCompletion w) σ)
    (σB := smulUnitsAut (R := w.adicCompletion K) σ)
    (AddSubgroup.subtype (unitVal (A := w.adicCompletion K)).ker)
    (fun _ => rfl) (Nat.card ↥(stabilizer Gal(K/k) w)) y
  rw [hy] at hpush
  exact mem_normSubgroup_of_normHom_smulUnitsAut (exists_stabilizer_smul_eq k w) hgen
    (b := (y : Additive (w.adicCompletion K)ˣ)) hpush.symm

variable (k) in
/-- **At a place unramified over the base every unit of the valuation ring of the base field is a
norm**, the Galois group being cyclic.  The decomposition group is then cyclic as a subgroup of a
cyclic group, and an unramified place carries a uniformizer fixed by it. -/
theorem mem_normSubgroup_adicCompletion_of_isUnramifiedAt [IsCyclic Gal(K/k)]
    (w : HeightOneSpectrum (𝓞 K)) (hw : Algebra.IsUnramifiedAt (𝓞 k) w.asIdeal)
    {a : ((primeUnder (𝓞 k) w).adicCompletion k)ˣ} (ha : unitVal (Additive.ofMul a) = 0) :
    a ∈ normSubgroup ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K) := by
  obtain ⟨π, hπfix, hπval⟩ := exists_fixedUniformizer_of_isUnramifiedAt (k := k) w hw
  obtain ⟨σ, hgen⟩ := IsCyclic.exists_generator (α := ↥(stabilizer Gal(K/k) w))
  exact mem_normSubgroup_adicCompletion_of_unitVal_eq_zero k w hgen π hπfix hπval ha

end AdicLocalNorm

/-! ### An infinite place that splits completely -/

section InfiniteLocalNorm

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

variable (k) in
/-- **At an infinite place that splits completely every local unit of the base field is a norm.**
The decomposition group being trivial, the norm operator of the Tate formalism is the sum of a
single term, namely the identity, so the unit is its own norm. -/
theorem mem_normSubgroup_infiniteCompletion_of_subsingleton_stabilizer (w : InfinitePlace K)
    (hsplit : Subsingleton ↥(stabilizer Gal(K/k) w))
    (a : ((w.comap (algebraMap k K)).Completion)ˣ) :
    a ∈ normSubgroup ((w.comap (algebraMap k K)).Completion) w.Completion := by
  haveI : Fintype ↥(stabilizer Gal(K/k) w) := Fintype.ofFinite _
  haveI := isGalois_infiniteCompletion k w
  have hcard : Nat.card ↥(stabilizer Gal(K/k) w) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨hsplit, ⟨1⟩⟩
  refine mem_normSubgroup_of_normHom_smulUnitsAut (exists_stabilizer_smul_eq_infinite k w)
    (τ := 1) (fun g => by rw [Subsingleton.elim g 1]; exact Subgroup.mem_zpowers 1)
    (b := infiniteUnitsComap k w (Additive.ofMul a)) ?_
  rw [hcard, normHom_apply, Finset.sum_range_one, pow_zero]
  rfl

variable (k) in
/-- **At a real infinite place every local unit of the base field is a norm.**  A place whose
decomposition group is nontrivial is ramified, hence complex. -/
theorem mem_normSubgroup_infiniteCompletion_of_isReal (w : InfinitePlace K) (hw : w.IsReal)
    (a : ((w.comap (algebraMap k K)).Completion)ˣ) :
    a ∈ normSubgroup ((w.comap (algebraMap k K)).Completion) w.Completion := by
  refine mem_normSubgroup_infiniteCompletion_of_subsingleton_stabilizer k w ?_ a
  rcases InfinitePlace.nat_card_stabilizer_eq_one_or_two k w with h1 | h2
  · exact (Nat.card_eq_one_iff_unique.mp h1).1
  · exact absurd (InfinitePlace.isRamified_iff_card_stabilizer_eq_two.mpr h2).isComplex
      (InfinitePlace.not_isComplex_iff_isReal.mpr hw)

end InfiniteLocalNorm

end InverseGalois.CFT

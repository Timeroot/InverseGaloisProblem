/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Rigidity.Rigidity

/-!
# Sanity certificate: `S₃ = Equiv.Perm (Fin 3)` is rigid

This file builds a concrete `RigidityCertificate` for the symmetric group `S₃` and fires the
rigidity criterion end-to-end:

```
example : IsInverseGalois (Equiv.Perm (Fin 3)) := rigidity_realizable s3Cert
```

The certificate is the classical rigid triple for `S₃`: two transposition classes and one
`3`-cycle class, `C = ![mk (swap 0 1), mk (swap 0 1), mk c₃]`.  There are exactly `6 = |S₃|`
product-one generating tuples `(g₀, g₁, g₂)` in these classes (given `g₀, g₁` transpositions with
`g₀ g₁ g₂ = 1`, the third entry `g₂ = (g₀ g₁)⁻¹` is a `3`-cycle iff `g₀ ≠ g₁`, and each of the six
ordered pairs of distinct transpositions generates `S₃`), so the structure constant is `1`.  All
three classes are rational because `S₃` is a rational group.

Every field of the certificate is discharged by genuine proof or by `decide`/`native_decide`,
demonstrating that the certificate really is *cheap to check*.

## Main results

* `Rigidity.S3Example.s3Cert` — the rigidity certificate for `S₃`.
* `Rigidity.S3Example.s3_isInverseGalois` — `IsInverseGalois (Equiv.Perm (Fin 3))`.
-/

open Polynomial Equiv Equiv.Perm

namespace Rigidity

namespace S3Example

/-- `S₃`, realized as `Equiv.Perm (Fin 3)`. -/
abbrev S3 := Equiv.Perm (Fin 3)

/-- The transposition `(0 1)`. -/
def t01 : S3 := Equiv.swap 0 1

/-- The `3`-cycle `(0 1 2)`, as `finRotate 3`. -/
def c3 : S3 := finRotate 3

/-- The prescribed conjugacy classes: two transposition classes and one `3`-cycle class. -/
def Ccert : Fin 3 → ConjClasses S3 := ![ConjClasses.mk t01, ConjClasses.mk t01, ConjClasses.mk c3]

/-- The transposition class `[t01]` is rational: a coprime power of a permutation conjugate to a
transposition is again a transposition, hence conjugate to the original. -/
theorem t01_rational : IsRationalClass (ConjClasses.mk t01) := by
  intro g hg k hk
  have hgc : IsConj g t01 := ConjClasses.mk_eq_mk_iff_isConj.mp hg
  have hgct : g.cycleType = {2} := by
    rw [isConj_iff_cycleType_eq.mp hgc]
    exact isSwap_iff_cycleType.mp (card_support_eq_two.mp (by decide))
  have hsupp : (g ^ k).support = g.support := support_pow_coprime hk
  have hgsupp2 : g.support.card = 2 := by rw [← sum_cycleType, hgct]; rfl
  have hgkct : (g ^ k).cycleType = {2} :=
    isSwap_iff_cycleType.mp (card_support_eq_two.mp (by rw [hsupp, hgsupp2]))
  rw [← hg, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff_cycleType_eq, hgkct, hgct]

/-- The `3`-cycle class `[c3]` is rational: a coprime power of a permutation conjugate to a
`3`-cycle is again a `3`-cycle, hence conjugate to the original. -/
theorem c3_rational : IsRationalClass (ConjClasses.mk c3) := by
  intro g hg k hk
  have hgc : IsConj g c3 := ConjClasses.mk_eq_mk_iff_isConj.mp hg
  have hgct : g.cycleType = {3} := by
    rw [isConj_iff_cycleType_eq.mp hgc]
    exact (card_support_eq_three_iff.mp (by decide) : c3.IsThreeCycle)
  have hsupp : (g ^ k).support = g.support := support_pow_coprime hk
  have hgsupp3 : g.support.card = 3 := by rw [← sum_cycleType, hgct]; rfl
  have hgkct : (g ^ k).cycleType = {3} :=
    (card_support_eq_three_iff.mp (by rw [hsupp, hgsupp3]) : (g ^ k).IsThreeCycle)
  rw [← hg, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff_cycleType_eq, hgkct, hgct]

/-- The **closure-free** decidable set of product-one tuples in the prescribed classes.  Since a
`3`-cycle together with a transposition always generates `S₃`, this set coincides with
`rigidTuples Ccert` (see `rigidTuples_eq_Dset`), which lets us count it by `native_decide`. -/
def Dset : Finset (Fin 3 → S3) :=
  Finset.univ.filter fun g => (∀ i, ConjClasses.mk (g i) = Ccert i) ∧ (List.ofFn g).prod = 1

/-- Any tuple in the prescribed classes has entry `2` a `3`-cycle with full support. -/
theorem isThreeCycle_of_mem {g : Fin 3 → S3} (h : ∀ i, ConjClasses.mk (g i) = Ccert i) :
    (g 2).IsThreeCycle := by
  have hconj : IsConj (g 2) c3 := ConjClasses.mk_eq_mk_iff_isConj.mp (by rw [h 2]; rfl)
  show (g 2).cycleType = {3}
  rw [isConj_iff_cycleType_eq.mp hconj]
  exact (card_support_eq_three_iff.mp (by decide) : c3.IsThreeCycle)

/-- Any tuple in the prescribed classes has entry `0` a transposition. -/
theorem isSwap_of_mem {g : Fin 3 → S3} (h : ∀ i, ConjClasses.mk (g i) = Ccert i) :
    (g 0).IsSwap := by
  have hconj : IsConj (g 0) t01 := ConjClasses.mk_eq_mk_iff_isConj.mp (by rw [h 0]; rfl)
  rw [isSwap_iff_cycleType, isConj_iff_cycleType_eq.mp hconj]
  exact isSwap_iff_cycleType.mp (card_support_eq_two.mp (by decide))

/-- The generating condition is automatic: in the prescribed classes every product-one tuple
generates `S₃`, because a `3`-cycle and a transposition generate.  Hence `rigidTuples Ccert`
equals the closure-free decidable set `Dset`. -/
theorem rigidTuples_eq_Dset : rigidTuples Ccert = (Dset : Set (Fin 3 → S3)) := by
  ext g
  simp only [rigidTuples, Set.mem_setOf_eq, Dset, Finset.coe_filter, Finset.mem_univ, true_and,
    Set.mem_setOf_eq]
  refine ⟨fun ⟨hc, hp, _⟩ => ⟨hc, hp⟩, fun ⟨hc, hp⟩ => ⟨hc, hp, ?_⟩⟩
  -- generation: `⟨g 2, g 0⟩ = ⊤` since `g 2` is a full-support `3`-cycle and `g 0` a swap
  have h3 : (g 2).IsThreeCycle := isThreeCycle_of_mem hc
  have hsupp : (g 2).support = Finset.univ :=
    Finset.eq_univ_of_card _ (by simp [h3.card_support])
  have hclosure : Subgroup.closure ({g 2, g 0} : Set S3) = ⊤ :=
    closure_prime_cycle_swap (by decide) h3.isCycle hsupp (isSwap_of_mem hc)
  have hsub : ({g 2, g 0} : Set S3) ⊆ Set.range g := by
    intro x hx
    rcases hx with h | h
    · exact ⟨2, h.symm⟩
    · exact ⟨0, (Set.mem_singleton_iff.mp h).symm⟩
  have hle := Subgroup.closure_mono hsub
  rw [hclosure] at hle
  exact top_le_iff.mp hle

/-- The rigidity certificate for `S₃`: two transposition classes and one `3`-cycle class. -/
def s3Cert : RigidityCertificate S3 where
  r := 3
  C := Ccert
  center_triv := by decide
  rational := by
    intro i
    fin_cases i
    · exact t01_rational
    · exact t01_rational
    · exact c3_rational
  gen := by
    rw [rigidTuples_eq_Dset]
    have hcard : Dset.card = 6 := by native_decide
    exact Finset.coe_nonempty.mpr (Finset.card_pos.mp (by rw [hcard]; norm_num))
  rigid := by
    rw [rigidTuples_eq_Dset]
    have hcard : Dset.card = 6 := by native_decide
    have hS3 : Nat.card S3 = 6 := by rw [Nat.card_eq_fintype_card]; decide
    simp only [Nat.card_coe_set_eq, Set.ncard_coe_finset, hcard, hS3]

/-- **`S₃` is an inverse Galois group over `ℚ`**, via the rigidity criterion applied to the
concrete certificate `s3Cert`. -/
theorem s3_isInverseGalois : IsInverseGalois (Equiv.Perm (Fin 3)) :=
  rigidity_realizable s3Cert

end S3Example

end Rigidity

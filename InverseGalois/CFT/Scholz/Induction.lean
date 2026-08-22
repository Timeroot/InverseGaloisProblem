import Mathlib
import InverseGalois.Core.Basic
import InverseGalois.CFT.Scholz.Realization

/-!
# The Scholz–Reichardt induction

Scholz and Reichardt realise every finite `ℓ`-group as a Galois group over `ℚ` by induction on the
order of the group.  A nontrivial finite `ℓ`-group `G` has a central subgroup `Z` of order `ℓ`, and
`G` is then a central extension of the smaller group `G ⧸ Z` by `Z`; if the quotient is already
realised by a field satisfying Serre's condition, one has to solve the corresponding embedding
problem while keeping the condition, at the cost of one unit of the level.

This file isolates that embedding step as a single named property, `IsCentralStepSolvable`, and
carries out the rest of the induction: granted the step, every finite `ℓ`-group is realised by a
field satisfying Serre's condition at every level, and hence occurs as a Galois group over `ℚ`.
The base of the induction is the trivial group, realised by `ℚ` itself at every level, so the loss
of a level at each step costs nothing.

## Main definitions

* `InverseGalois.CFT.IsCentralStepSolvable`: the central embedding step of the induction.

## Main results

* `InverseGalois.CFT.IsScholzRealizable.isInverseGalois`: a group realised by a field satisfying
  Serre's condition is a Galois group over `ℚ`.
* `InverseGalois.CFT.isScholzRealizable_of_isPGroup`: **granted the central step, every finite
  `ℓ`-group is realised at every level.**
* `InverseGalois.CFT.isInverseGalois_of_isCentralStepSolvable`: **granted the central step, every
  finite `ℓ`-group is a Galois group over `ℚ`.**
-/

namespace InverseGalois.CFT

/-! ### From a normalised realization to a Galois group over `ℚ` -/

/-- **A group realised by a field satisfying Serre's condition is a Galois group over `ℚ`.**  The
realising field is a subfield of the algebraic closure of `ℚ`, finite and Galois over `ℚ`. -/
theorem IsScholzRealizable.isInverseGalois {G : Type*} [Group G] {ℓ N : ℕ}
    (h : IsScholzRealizable G ℓ N) : IsInverseGalois G := by
  obtain ⟨R⟩ := h
  exact ⟨↥R.carrier, inferInstance, inferInstance, inferInstance, inferInstance, ⟨R.galEquiv⟩⟩

/-! ### The central step -/

/-- **The central embedding step of the Scholz–Reichardt induction.**  Whenever a finite `ℓ`-group
`G` surjects onto `H` with central kernel of order `ℓ`, a realization of `H` satisfying Serre's
condition at level `N + 1` can be enlarged to a realization of `G` satisfying it at level `N`.
The induction only ever meets `ℓ`-groups, so nothing beyond them is demanded. -/
def IsCentralStepSolvable (ℓ : ℕ) : Prop :=
  ∀ (N : ℕ) {G H : Type} [Group G] [Group H] [Finite G] (f : G →* H), IsPGroup ℓ G →
    Function.Surjective f → f.ker ≤ Subgroup.center G → Nat.card f.ker = ℓ →
    IsScholzRealizable H ℓ (N + 1) → IsScholzRealizable G ℓ N

/-- **The central step holds for a split extension.**  When `G` is the direct product of `H` with
a cyclic group of order `ℓ`, the compositum construction of the split case supplies the enlarged
realization, and without even spending a level. -/
theorem isScholzRealizable_of_prod_cyclic {ℓ : ℕ} (hℓ : ℓ.Prime) {G H : Type*} [Group G] [Group H]
    {N : ℕ} (e : G ≃* H × Multiplicative (ZMod ℓ)) (h : IsScholzRealizable H ℓ N) :
    IsScholzRealizable G ℓ N :=
  (h.prod_cyclic hℓ).of_mulEquiv e.symm

/-! ### The induction -/

/-- **Granted the central step, a finite group of order `ℓ ^ k` is realised at every level.**  The
induction is on the exponent `k`: the trivial group is realised by `ℚ`, and a nontrivial
`ℓ`-group has a central subgroup of order `ℓ`, whose quotient is realised one level higher by the
induction hypothesis. -/
theorem isScholzRealizable_of_card_eq_pow {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hstep : IsCentralStepSolvable ℓ) (k : ℕ) :
    ∀ (N : ℕ) (G : Type) [Group G] [Finite G], Nat.card G = ℓ ^ k →
      IsScholzRealizable G ℓ N := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  induction k with
  | zero =>
    intro N G _ _ hcard
    rw [pow_zero] at hcard
    haveI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp hcard).1
    exact isScholzRealizable_of_subsingleton
  | succ k ih =>
    intro N G _ _ hcard
    have hone : 1 < Nat.card G := by
      rw [hcard]
      exact Nat.one_lt_pow (Nat.succ_ne_zero k) hℓ.one_lt
    haveI : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp hone
    have hpg : IsPGroup ℓ G := IsPGroup.of_card hcard
    haveI : Nontrivial (Subgroup.center G) := hpg.center_nontrivial
    -- the centre is a nontrivial `ℓ`-group, so it contains an element of order `ℓ`
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (hpg.to_subgroup (Subgroup.center G))
    have hjne : j ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hj
      exact absurd hj (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne'
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center G) ℓ
      (hj ▸ dvd_pow_self ℓ hjne)
    -- the subgroup it generates is central of order `ℓ`
    set Z : Subgroup G := Subgroup.zpowers (z : G) with hZ
    have hZle : Z ≤ Subgroup.center G := by
      rw [hZ, Subgroup.zpowers_le]
      exact z.2
    have hZcard : Nat.card Z = ℓ := by
      rw [hZ, Nat.card_zpowers, ← hz]
      exact (Subgroup.orderOf_coe z).symm ▸ rfl
    haveI : Z.Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hc := Subgroup.mem_center_iff.mp (hZle hn) g
      have hgn : g * n * g⁻¹ = n := by rw [hc, mul_assoc, mul_inv_cancel, mul_one]
      rwa [hgn]
    -- the quotient is smaller, so the induction hypothesis realises it one level higher
    have hquot : Nat.card (G ⧸ Z) = ℓ ^ k := by
      have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
      rw [hcard, hZcard, pow_succ] at hsplit
      exact Nat.eq_of_mul_eq_mul_right hℓ.pos hsplit.symm
    refine hstep N (QuotientGroup.mk' Z) hpg (QuotientGroup.mk'_surjective Z) ?_ ?_
      (ih (N + 1) (G ⧸ Z) hquot)
    · rw [QuotientGroup.ker_mk']
      exact hZle
    · rw [QuotientGroup.ker_mk']
      exact hZcard

/-- **Granted the central step, every finite `ℓ`-group is realised at every level** by a field
satisfying Serre's condition. -/
theorem isScholzRealizable_of_isPGroup {ℓ : ℕ} (hℓ : ℓ.Prime) (hstep : IsCentralStepSolvable ℓ)
    (N : ℕ) (G : Type) [Group G] [Finite G] (hG : IsPGroup ℓ G) :
    IsScholzRealizable G ℓ N := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hG
  exact isScholzRealizable_of_card_eq_pow hℓ hstep k N G hk

/-- **Granted the central step, every finite `ℓ`-group is a Galois group over `ℚ`.** -/
theorem isInverseGalois_of_isCentralStepSolvable {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hstep : IsCentralStepSolvable ℓ) (G : Type) [Group G] [Finite G] (hG : IsPGroup ℓ G) :
    IsInverseGalois G :=
  (isScholzRealizable_of_isPGroup hℓ hstep 1 G hG).isInverseGalois

end InverseGalois.CFT

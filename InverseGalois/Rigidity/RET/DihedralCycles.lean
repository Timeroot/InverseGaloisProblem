/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.DihedralReflection
import InverseGalois.Rigidity.RET.AbelianizedCycles

/-!
# Branch cycles of the inverted dihedral cover

The dihedral cover read in the coordinate `S = T⁻¹` is branched over the three points `0`, `1/2`
and `-1/2`, with a rotation of order `n` generating inertia at the origin and a reflection
generating inertia at each of the other two points.  This file upgrades that local information to
a genuine **system of distinguished branch cycles**: a triple `(g₀, g₁, g₂)` of deck
transformations, each generating an inertia group at the corresponding point, which generates the
whole deck group and whose ordered product is the identity.

The abelianized branch-cycle theorem supplies distinguished inertia elements whose ordered product
is only known to be a commutator.  In a dihedral group the commutator subgroup consists of the even
rotations, and conjugating the third cycle by a rotation `r i` shifts it by `r (-2i)`; choosing `i`
so that `2i` is the recorded discrepancy makes the product exactly `1`.  Generation is then
automatic, because a rotation of maximal order together with a reflection already generates.

## Main results

* `Rigidity.RET.commutator_le_evenRot` — the commutator subgroup of a dihedral group consists of
  even rotations.
* `Rigidity.RET.closure_r_sr_eq_top` — a rotation of maximal order and a reflection generate.
* `Rigidity.RET.exists_branchCycleGenSystem_dihInfCover` — the inverted dihedral cover has a system
  of distinguished branch cycles over the three points `0`, `1/2`, `-1/2`.
-/

open Polynomial GeomAKLB

noncomputable section

namespace Rigidity.RET

attribute [local instance] Ideal.Quotient.field GeomAKLB.instMSA GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instIntegral GeomAKLB.instFaithful
  GeomAKLB.instDedekindB

/-! ### Even rotations -/

section EvenRot

/-- The subgroup of **even rotations** of a dihedral group. -/
def evenRot (n : ℕ) : Subgroup (DihedralGroup n) where
  carrier := {g | ∃ i : ZMod n, g = DihedralGroup.r (2 * i)}
  one_mem' := ⟨0, by rw [mul_zero]; exact DihedralGroup.one_def⟩
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨i + j, by rw [DihedralGroup.r_mul_r]; congr 1; ring⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨-i, by rw [DihedralGroup.inv_r]; congr 1; ring⟩

theorem mem_evenRot {n : ℕ} {g : DihedralGroup n} :
    g ∈ evenRot n ↔ ∃ i : ZMod n, g = DihedralGroup.r (2 * i) := Iff.rfl

/-- **The commutator subgroup of a dihedral group consists of even rotations.** -/
theorem commutator_le_evenRot (n : ℕ) : commutator (DihedralGroup n) ≤ evenRot n := by
  show ⁅(⊤ : Subgroup (DihedralGroup n)), ⊤⁆ ≤ evenRot n
  refine Subgroup.commutator_le.mpr ?_
  intro a _ b _
  rw [commutatorElement_def]
  refine mem_evenRot.mpr ?_
  cases a with
  | r x =>
    cases b with
    | r y =>
      exact ⟨0, by
        rw [DihedralGroup.inv_r, DihedralGroup.inv_r, DihedralGroup.r_mul_r,
          DihedralGroup.r_mul_r, DihedralGroup.r_mul_r]
        congr 1
        ring⟩
    | sr y =>
      exact ⟨x, by
        rw [DihedralGroup.inv_r, DihedralGroup.inv_sr, DihedralGroup.r_mul_sr,
          DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]
        congr 1
        ring⟩
  | sr x =>
    cases b with
    | r y =>
      exact ⟨-y, by
        rw [DihedralGroup.inv_sr, DihedralGroup.inv_r, DihedralGroup.sr_mul_r,
          DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_r]
        congr 1
        ring⟩
    | sr y =>
      exact ⟨y - x, by
        rw [DihedralGroup.inv_sr, DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr,
          DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_sr]
        congr 1
        ring⟩

/-- The commutator subgroup is carried onto the commutator subgroup by an isomorphism. -/
theorem mem_commutator_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) {x : H}
    (hx : x ∈ commutator H) : e.symm x ∈ commutator G := by
  have hmap : Subgroup.map (e.symm : H →* G) (commutator H) = commutator G := by
    show Subgroup.map (e.symm : H →* G) ⁅(⊤ : Subgroup H), ⊤⁆ = ⁅(⊤ : Subgroup G), ⊤⁆
    rw [Subgroup.map_commutator,
      Subgroup.map_top_of_surjective (e.symm : H →* G) (MulEquiv.surjective e.symm)]
  rw [← hmap]
  exact Subgroup.mem_map_of_mem _ hx

/-- **A rotation of maximal order together with a reflection generates a dihedral group.** -/
theorem closure_r_sr_eq_top {n : ℕ} [NeZero n] {m : ZMod n} (hm : IsUnit m) (j : ZMod n) :
    Subgroup.closure ({DihedralGroup.r m, DihedralGroup.sr j} : Set (DihedralGroup n)) = ⊤ := by
  obtain ⟨u, hu⟩ := hm
  have hv : m * ((u⁻¹ : (ZMod n)ˣ) : ZMod n) = 1 := by rw [← hu]; exact u.mul_inv
  set K : Subgroup (DihedralGroup n) :=
    Subgroup.closure ({DihedralGroup.r m, DihedralGroup.sr j} : Set (DihedralGroup n)) with hK
  have hrm : DihedralGroup.r m ∈ K := Subgroup.subset_closure (Or.inl rfl)
  have hsrj : DihedralGroup.sr j ∈ K := Subgroup.subset_closure (Or.inr rfl)
  have hrot : ∀ a : ZMod n, DihedralGroup.r a ∈ K := by
    intro a
    have hpow : DihedralGroup.r m ^ (a * ((u⁻¹ : (ZMod n)ˣ) : ZMod n)).val = DihedralGroup.r a := by
      rw [DihedralGroup.r_pow]
      congr 1
      have hcast : (((a * ((u⁻¹ : (ZMod n)ˣ) : ZMod n)).val : ℕ) : ZMod n)
          = a * ((u⁻¹ : (ZMod n)ˣ) : ZMod n) := by
        simp [ZMod.natCast_val, ZMod.cast_id]
      rw [hcast]
      linear_combination a * hv
    rw [← hpow]
    exact pow_mem hrm _
  refine (Subgroup.eq_top_iff' K).mpr ?_
  intro g
  cases g with
  | r a => exact hrot a
  | sr b =>
    have hmul : DihedralGroup.r (j - b) * DihedralGroup.sr j = DihedralGroup.sr b := by
      rw [DihedralGroup.r_mul_sr]
      congr 1
      ring
    rw [← hmul]
    exact mul_mem (hrot _) hsrj

/-- The image of a generating pair under an isomorphism generates. -/
theorem closure_pair_image_eq_top {G H : Type*} [Group G] [Group H] (e : G ≃* H) {a b : G}
    (h : Subgroup.closure ({a, b} : Set G) = ⊤) :
    Subgroup.closure ({e a, e b} : Set H) = ⊤ := by
  refine (Subgroup.eq_top_iff' _).mpr ?_
  intro y
  have hle : Subgroup.closure ({a, b} : Set G)
      ≤ Subgroup.comap (e : G →* H) (Subgroup.closure ({e a, e b} : Set H)) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x (rfl | rfl)
    · exact Subgroup.subset_closure (Or.inl rfl)
    · exact Subgroup.subset_closure (Or.inr rfl)
  have hy : e.symm y ∈ Subgroup.closure ({a, b} : Set G) := by rw [h]; trivial
  have hmem := hle hy
  rw [Subgroup.mem_comap] at hmem
  simpa using hmem

/-! ### The dihedral triple identities -/

variable {n : ℕ}

/-- The ordered product of a rotation and two reflections is a rotation. -/
theorem dih_triple_mul (m j₁ j₂ : ZMod n) :
    DihedralGroup.r m * DihedralGroup.sr j₁ * DihedralGroup.sr j₂
      = DihedralGroup.r (m + j₂ - j₁) := by
  rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_sr]
  congr 1
  ring

/-- Conjugating the second reflection by a rotation corrects the product to `1`. -/
theorem dih_triple_correct {m j₁ j₂ i : ZMod n} (hi : m + j₂ - j₁ = 2 * i) :
    DihedralGroup.r i * DihedralGroup.sr j₂ * (DihedralGroup.r i)⁻¹
      = DihedralGroup.sr (j₁ - m) := by
  rw [DihedralGroup.inv_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r]
  congr 1
  linear_combination hi

/-- The corrected triple has ordered product `1`. -/
theorem dih_triple_prod (m j₁ : ZMod n) :
    DihedralGroup.r m * DihedralGroup.sr j₁ * DihedralGroup.sr (j₁ - m) = 1 := by
  rw [dih_triple_mul, DihedralGroup.one_def]
  congr 1
  ring

end EvenRot

/-! ### Identifying the inertia generators -/

section Identify

variable {n : ℕ} [NeZero n] {ζ : k}

/-- **A distinguished inertia element at the origin of the inverted dihedral cover is a rotation of
maximal order.** -/
theorem exists_r_of_isInertiaGenAt_zero (hζ : IsPrimitiveRoot ζ n) (hn : 3 ≤ n)
    {σ : (dihInfCover n).deck} (h : (dihInfCover n).IsInertiaGenAt 0 σ) :
    ∃ m : ZMod n, IsUnit m ∧ σ = dihInfDeckEquiv hζ (DihedralGroup.r m) := by
  obtain ⟨Q, hQmax, hQover, hI⟩ := h
  haveI := hQmax
  haveI := hQover
  have hcard := card_geomInertia_dihInf n hn Q
  have hord : orderOf σ = n := by rw [← Nat.card_zpowers, ← hI, hcard]
  obtain ⟨g, hg⟩ := (dihInfDeckEquiv hζ).surjective σ
  have hordg : orderOf g = n := by
    rw [← (dihInfDeckEquiv hζ).orderOf_eq g, hg, hord]
  cases g with
  | sr j =>
    rw [DihedralGroup.orderOf_sr] at hordg
    omega
  | r m =>
    refine ⟨m, ?_, hg.symm⟩
    rw [DihedralGroup.orderOf_r] at hordg
    have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    have hgcd : Nat.gcd n m.val = 1 := by
      have hcancel := Nat.div_mul_cancel (Nat.gcd_dvd_left n m.val)
      rw [hordg] at hcancel
      exact Nat.eq_of_mul_eq_mul_left hnpos (hcancel.trans (mul_one n).symm)
    have hval : ((m.val : ℕ) : ZMod n) = m := by simp [ZMod.natCast_val, ZMod.cast_id]
    have hu : IsUnit ((m.val : ℕ) : ZMod n) :=
      (ZMod.isUnit_iff_coprime m.val n).mpr (Nat.Coprime.symm hgcd)
    rwa [hval] at hu

/-- **A distinguished inertia element at a reflection point of the inverted dihedral cover is a
reflection.** -/
theorem exists_sr_of_isInertiaGenAt_refl (hζ : IsPrimitiveRoot ζ n) {a : k} (ha : a ^ 2 = 1)
    {σ : (dihInfCover n).deck} (h : (dihInfCover n).IsInertiaGenAt (a * 2⁻¹) σ) :
    ∃ j : ZMod n, σ = dihInfDeckEquiv hζ (DihedralGroup.sr j) := by
  obtain ⟨Q, hQmax, hQover, hI⟩ := h
  haveI := hQmax
  haveI := hQover
  have hane : a * 2⁻¹ ≠ 0 := mul_ne_zero (ne_zero_of_sq_eq_one ha) (inv_ne_zero two_ne_zero)
  have hcard := card_geomInertia_inf_eq_two n ha Q
  have hmem : σ ∈ geomInertia (dihInfCover n).M Q := hI ▸ Subgroup.mem_zpowers σ
  have hσ : σ ≠ 1 := by
    intro h1
    rw [h1, Subgroup.zpowers_one_eq_bot] at hI
    rw [hI, Subgroup.card_bot] at hcard
    exact absurd hcard (by norm_num)
  exact exists_sr_of_mem_geomInertia_inf hζ hane Q hmem hσ

end Identify

/-! ### The three branch points as a tuple -/

section Points

/-- The three branch points `0`, `1/2`, `-1/2` of the inverted dihedral cover, as a tuple. -/
def dihPts : Fin 3 → k := ![0, 2⁻¹, -2⁻¹]

@[simp] theorem dihPts_zero : dihPts 0 = 0 := rfl

@[simp] theorem dihPts_one : dihPts 1 = 2⁻¹ := rfl

@[simp] theorem dihPts_two : dihPts 2 = -2⁻¹ := rfl

/-- A map out of `Fin 3` is injective as soon as its three values are pairwise distinct. -/
theorem injective_fin3 {α : Type*} {f : Fin 3 → α} (h01 : f 0 ≠ f 1) (h02 : f 0 ≠ f 2)
    (h12 : f 1 ≠ f 2) : Function.Injective f := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd hij h01
  · exact absurd hij h02
  · exact absurd hij.symm h01
  · rfl
  · exact absurd hij h12
  · exact absurd hij.symm h02
  · exact absurd hij.symm h12
  · rfl

/-- One half is not minus one half. -/
theorem inv_two_ne_neg_inv_two : (2 : k)⁻¹ ≠ -2⁻¹ := by
  intro h
  have h2 : (2 : k) * 2⁻¹ = 0 := by linear_combination h
  rw [mul_inv_cancel₀ two_ne_zero] at h2
  exact one_ne_zero h2

theorem dihPts_injective : Function.Injective dihPts := by
  have h0 : (2 : k)⁻¹ ≠ 0 := inv_ne_zero two_ne_zero
  refine injective_fin3 ?_ ?_ ?_
  · rw [dihPts_zero, dihPts_one]
    exact fun h => h0 h.symm
  · rw [dihPts_zero, dihPts_two]
    exact fun h => (neg_ne_zero.mpr h0) h.symm
  · rw [dihPts_one, dihPts_two]
    exact inv_two_ne_neg_inv_two

theorem range_dihPts : Set.range dihPts = ({0, 2⁻¹, -2⁻¹} : Set k) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

/-- **The inverted dihedral cover is unramified outside the three listed points.** -/
theorem isUnramifiedOutside_dihPts (n : ℕ) [NeZero n] :
    (dihInfCover n).IsUnramifiedOutside (Set.range dihPts) := by
  rw [range_dihPts]
  exact ((dihInfCover n).isUnramifiedOutside_iff_branchLocus_subset _).mpr
    (branchLocus_dihInfCover_subset n)

end Points

/-! ### The system of distinguished branch cycles -/

/-- **Correcting an abelianized branch-cycle triple of a cover with dihedral deck group.**

Given distinguished inertia elements which are a rotation of maximal order and two reflections, and
whose ordered product is only known to be a commutator, conjugating the last one by a suitable
rotation produces a genuine system of distinguished branch cycles. -/
theorem exists_branchCycleGenSystem_of_dihedral {L : LineCover} {n : ℕ} [NeZero n]
    (e : DihedralGroup n ≃* L.deck) {t : Fin 3 → k} {g : Fin 3 → L.deck} {m j₁ j₂ : ZMod n}
    (hmunit : IsUnit m) (hg0 : g 0 = e (DihedralGroup.r m))
    (hg1 : g 1 = e (DihedralGroup.sr j₁)) (hg2 : g 2 = e (DihedralGroup.sr j₂))
    (hgin : ∀ l, L.IsInertiaGenAt (t l) (g l))
    (hgprod : (List.ofFn g).prod ∈ commutator L.deck) :
    ∃ G : Fin 3 → L.deck, L.IsBranchCycleGenSystem t G := by
  -- the recorded product is a commutator, hence an even rotation
  have hprodeq : (List.ofFn g).prod = g 0 * g 1 * g 2 := by
    simp [List.ofFn_succ, mul_assoc]
  have hsym : e.symm ((List.ofFn g).prod) = DihedralGroup.r (m + j₂ - j₁) := by
    rw [hprodeq, hg0, hg1, hg2, ← map_mul, ← map_mul, MulEquiv.symm_apply_apply, dih_triple_mul]
  have hcomm : DihedralGroup.r (m + j₂ - j₁) ∈ commutator (DihedralGroup n) := by
    rw [← hsym]
    exact mem_commutator_of_mulEquiv e hgprod
  obtain ⟨i, hi⟩ := mem_evenRot.mp (commutator_le_evenRot n hcomm)
  have hi' : m + j₂ - j₁ = 2 * i := by rwa [DihedralGroup.r.injEq] at hi
  -- correct the third cycle by conjugating with the rotation `r i`
  have hconj : e (DihedralGroup.r i) * g 2 * (e (DihedralGroup.r i))⁻¹
      = e (DihedralGroup.sr (j₁ - m)) := by
    rw [hg2, ← map_inv, ← map_mul, ← map_mul, dih_triple_correct hi']
  refine ⟨![e (DihedralGroup.r m), e (DihedralGroup.sr j₁), e (DihedralGroup.sr (j₁ - m))],
    ?_, ?_, ?_⟩
  · intro l
    fin_cases l
    · show L.IsInertiaGenAt (t 0) (e (DihedralGroup.r m))
      rw [← hg0]
      exact hgin 0
    · show L.IsInertiaGenAt (t 1) (e (DihedralGroup.sr j₁))
      rw [← hg1]
      exact hgin 1
    · show L.IsInertiaGenAt (t 2) (e (DihedralGroup.sr (j₁ - m)))
      rw [← hconj]
      exact (hgin 2).conj _
  · refine eq_top_iff.mpr ?_
    have hsub : ({e (DihedralGroup.r m), e (DihedralGroup.sr j₁)} : Set L.deck)
        ⊆ Set.range ![e (DihedralGroup.r m), e (DihedralGroup.sr j₁),
            e (DihedralGroup.sr (j₁ - m))] := by
      rintro x (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    have htop := closure_pair_image_eq_top e (closure_r_sr_eq_top hmunit j₁)
    exact htop ▸ Subgroup.closure_mono hsub
  · show (List.ofFn ![e (DihedralGroup.r m), e (DihedralGroup.sr j₁),
      e (DihedralGroup.sr (j₁ - m))]).prod = 1
    have h : (List.ofFn ![e (DihedralGroup.r m), e (DihedralGroup.sr j₁),
        e (DihedralGroup.sr (j₁ - m))]).prod
        = e (DihedralGroup.r m) * e (DihedralGroup.sr j₁) * e (DihedralGroup.sr (j₁ - m)) := by
      simp [List.ofFn_succ, mul_assoc]
    rw [h, ← map_mul, ← map_mul, dih_triple_prod, map_one]

/-- **The inverted dihedral cover admits a system of distinguished branch cycles over the three
points `0`, `1/2`, `-1/2`.**

This is the first non-abelian instance of the branch-cycle conclusion of the Riemann existence
theorem over three branch points. -/
theorem exists_branchCycleGenSystem_dihInfCover (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    ∃ g : Fin 3 → (dihInfCover n).deck, (dihInfCover n).IsBranchCycleGenSystem dihPts g := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_algebraicClosure n (dihPos n)
  obtain ⟨g, hgin, -, hgprod⟩ :=
    exists_inertiaGens_mod_commutator (dihInfCover n) dihPts dihPts_injective
      (isUnramifiedOutside_dihPts n) (isUnramifiedAtInfinity_dihInfCover n)
  have hin0 : (dihInfCover n).IsInertiaGenAt 0 (g 0) := by
    rw [← dihPts_zero]; exact hgin 0
  have hin1 : (dihInfCover n).IsInertiaGenAt ((1 : k) * 2⁻¹) (g 1) := by
    rw [one_mul, ← dihPts_one]; exact hgin 1
  have hin2 : (dihInfCover n).IsInertiaGenAt ((-1 : k) * 2⁻¹) (g 2) := by
    rw [neg_one_mul, ← dihPts_two]; exact hgin 2
  obtain ⟨m, hmunit, hm⟩ := exists_r_of_isInertiaGenAt_zero hζ hn hin0
  obtain ⟨j₁, hj₁⟩ := exists_sr_of_isInertiaGenAt_refl hζ (one_pow 2) hin1
  obtain ⟨j₂, hj₂⟩ := exists_sr_of_isInertiaGenAt_refl hζ (neg_one_sq (R := k)) hin2
  exact exists_branchCycleGenSystem_of_dihedral (dihInfDeckEquiv hζ) hmunit hm hj₁ hj₂ hgin hgprod

end Rigidity.RET

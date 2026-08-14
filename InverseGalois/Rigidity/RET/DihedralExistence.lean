/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.DihedralCycles

/-!
# Realizing every dihedral branch-cycle datum over three points

The inverted dihedral cover is branched over `0`, `1/2` and `-1/2`, with a rotation of maximal
order generating inertia at the origin and a reflection generating inertia at each of the other two
points.  This file shows that this single cover already realizes **every** admissible branch-cycle
datum for a dihedral group over three points: given any triple of elements of `D_n` whose ordered
product is trivial and which generates `D_n`, some relabelling of the deck group by an automorphism
of `D_n` turns the distinguished inertia generators of the inverted dihedral cover into exactly
that triple, read over a suitable ordering of the three branch points.

The two ingredients are a supply of automorphisms of a dihedral group — the maps
`r i ↦ r (u i)`, `sr j ↦ sr (u j + v)` for a unit `u` — and the observation that the ordered
product being trivial forces the triple to consist of one rotation and two reflections whose
parameters differ by the rotation parameter.  Which of the three slots holds the rotation is
absorbed by permuting the three branch points, and the two reflections at `±1/2` are matched up
using stability of distinguished inertia generators under conjugation.

## Main results

* `Rigidity.RET.dihAut` — the automorphisms `r i ↦ r (u i)`, `sr j ↦ sr (u j + v)` of a dihedral
  group.
* `Rigidity.RET.exists_inertiaGens_dihInfCover` — the inverted dihedral cover, with its
  distinguished inertia generators recorded in dihedral coordinates.
* `Rigidity.RET.exists_cover_dihedral` — every generating product-one triple in a dihedral group
  is the tuple of distinguished inertia generators of a cover of the line branched over `0`, `1/2`
  and `-1/2` and unramified at infinity.
-/

open Polynomial GeomAKLB

noncomputable section

namespace Rigidity.RET

attribute [local instance] Ideal.Quotient.field GeomAKLB.instMSA GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instIntegral GeomAKLB.instFaithful
  GeomAKLB.instDedekindB

/-! ### Automorphisms of a dihedral group -/

section Aut

variable {n : ℕ}

/-- The underlying map of the automorphism `r i ↦ r (u i)`, `sr j ↦ sr (u j + v)` of a dihedral
group. -/
def dihAutFun (u : (ZMod n)ˣ) (v : ZMod n) : DihedralGroup n → DihedralGroup n
  | DihedralGroup.r i => DihedralGroup.r ((u : ZMod n) * i)
  | DihedralGroup.sr j => DihedralGroup.sr ((u : ZMod n) * j + v)

@[simp] theorem dihAutFun_r (u : (ZMod n)ˣ) (v i : ZMod n) :
    dihAutFun u v (DihedralGroup.r i) = DihedralGroup.r ((u : ZMod n) * i) := rfl

@[simp] theorem dihAutFun_sr (u : (ZMod n)ˣ) (v j : ZMod n) :
    dihAutFun u v (DihedralGroup.sr j) = DihedralGroup.sr ((u : ZMod n) * j + v) := rfl

theorem dihAutFun_dihAutFun (u : (ZMod n)ˣ) (v : ZMod n) (g : DihedralGroup n) :
    dihAutFun u⁻¹ (-((u⁻¹ : (ZMod n)ˣ) * v)) (dihAutFun u v g) = g := by
  have hiu : ((u⁻¹ : (ZMod n)ˣ) : ZMod n) * (u : ZMod n) = 1 := u.inv_mul
  cases g with
  | r i =>
    rw [dihAutFun_r, dihAutFun_r]
    congr 1
    linear_combination i * hiu
  | sr j =>
    rw [dihAutFun_sr, dihAutFun_sr]
    congr 1
    linear_combination j * hiu

theorem dihAutFun_dihAutFun' (u : (ZMod n)ˣ) (v : ZMod n) (g : DihedralGroup n) :
    dihAutFun u v (dihAutFun u⁻¹ (-((u⁻¹ : (ZMod n)ˣ) * v)) g) = g := by
  have hui : (u : ZMod n) * ((u⁻¹ : (ZMod n)ˣ) : ZMod n) = 1 := u.mul_inv
  cases g with
  | r i =>
    rw [dihAutFun_r, dihAutFun_r]
    congr 1
    linear_combination i * hui
  | sr j =>
    rw [dihAutFun_sr, dihAutFun_sr]
    congr 1
    linear_combination (j - v) * hui

/-- **The automorphism `r i ↦ r (u i)`, `sr j ↦ sr (u j + v)` of a dihedral group.** -/
def dihAut (u : (ZMod n)ˣ) (v : ZMod n) : DihedralGroup n ≃* DihedralGroup n where
  toFun := dihAutFun u v
  invFun := dihAutFun u⁻¹ (-((u⁻¹ : (ZMod n)ˣ) * v))
  left_inv := dihAutFun_dihAutFun u v
  right_inv := dihAutFun_dihAutFun' u v
  map_mul' x y := by
    cases x with
    | r i =>
      cases y with
      | r j =>
        rw [DihedralGroup.r_mul_r, dihAutFun_r, dihAutFun_r, dihAutFun_r,
          DihedralGroup.r_mul_r]
        congr 1
        ring
      | sr j =>
        rw [DihedralGroup.r_mul_sr, dihAutFun_sr, dihAutFun_r, dihAutFun_sr,
          DihedralGroup.r_mul_sr]
        congr 1
        ring
    | sr i =>
      cases y with
      | r j =>
        rw [DihedralGroup.sr_mul_r, dihAutFun_sr, dihAutFun_sr, dihAutFun_r,
          DihedralGroup.sr_mul_r]
        congr 1
        ring
      | sr j =>
        rw [DihedralGroup.sr_mul_sr, dihAutFun_r, dihAutFun_sr, dihAutFun_sr,
          DihedralGroup.sr_mul_sr]
        congr 1
        ring

@[simp] theorem dihAut_r (u : (ZMod n)ˣ) (v i : ZMod n) :
    dihAut u v (DihedralGroup.r i) = DihedralGroup.r ((u : ZMod n) * i) := rfl

@[simp] theorem dihAut_sr (u : (ZMod n)ˣ) (v j : ZMod n) :
    dihAut u v (DihedralGroup.sr j) = DihedralGroup.sr ((u : ZMod n) * j + v) := rfl

end Aut

/-! ### Two subgroups of a dihedral group -/

section Subgroups

variable {n : ℕ}

/-- The subgroup of rotations of a dihedral group. -/
def rotations (n : ℕ) : Subgroup (DihedralGroup n) where
  carrier := {g | ∃ i : ZMod n, g = DihedralGroup.r i}
  one_mem' := ⟨0, DihedralGroup.one_def⟩
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨i + j, DihedralGroup.r_mul_r i j⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨-i, DihedralGroup.inv_r i⟩

theorem sr_notMem_rotations (b : ZMod n) : DihedralGroup.sr b ∉ rotations n := by
  rintro ⟨i, hi⟩
  exact absurd hi (by simp)

theorem sr_ne_one (x : ZMod n) : DihedralGroup.sr x ≠ 1 := by
  intro hx
  refine sr_notMem_rotations x ?_
  rw [hx]
  exact (rotations n).one_mem

/-- The subgroup of a dihedral group consisting of the rotations by multiples of `m` together with
the reflections whose parameter lies in the coset `b + ⟨m⟩`.  It contains `r m` and `sr b`, hence
also the whole subgroup those two generate. -/
def rotCoset (m b : ZMod n) : Subgroup (DihedralGroup n) where
  carrier := {g | ∃ i : ℤ, g = DihedralGroup.r (i • m) ∨ g = DihedralGroup.sr (b + i • m)}
  one_mem' := ⟨0, Or.inl (by rw [zero_zsmul]; exact DihedralGroup.one_def)⟩
  mul_mem' := by
    rintro _ _ ⟨i, hi | hi⟩ ⟨j, hj | hj⟩ <;> subst hi <;> subst hj
    · refine ⟨i + j, Or.inl ?_⟩
      rw [DihedralGroup.r_mul_r, add_zsmul]
    · refine ⟨j - i, Or.inr ?_⟩
      rw [DihedralGroup.r_mul_sr, sub_zsmul]
      congr 1
      abel
    · refine ⟨i + j, Or.inr ?_⟩
      rw [DihedralGroup.sr_mul_r, add_zsmul]
      congr 1
      abel
    · refine ⟨j - i, Or.inl ?_⟩
      rw [DihedralGroup.sr_mul_sr, sub_zsmul]
      congr 1
      abel
  inv_mem' := by
    rintro _ ⟨i, hi | hi⟩ <;> subst hi
    · refine ⟨-i, Or.inl ?_⟩
      rw [DihedralGroup.inv_r, neg_zsmul]
    · exact ⟨i, Or.inr (DihedralGroup.inv_sr _)⟩

theorem r_mem_rotCoset (m b : ZMod n) : DihedralGroup.r m ∈ rotCoset m b :=
  ⟨1, Or.inl (by rw [one_zsmul])⟩

theorem sr_mem_rotCoset (m b : ZMod n) : DihedralGroup.sr b ∈ rotCoset m b :=
  ⟨0, Or.inr (by rw [zero_zsmul, add_zero])⟩

theorem sr_sub_mem_rotCoset (m b : ZMod n) : DihedralGroup.sr (b - m) ∈ rotCoset m b :=
  ⟨-1, Or.inr (by rw [neg_one_zsmul, ← sub_eq_add_neg])⟩

theorem sr_add_mem_rotCoset (m b : ZMod n) : DihedralGroup.sr (b + m) ∈ rotCoset m b :=
  ⟨1, Or.inr (by rw [one_zsmul])⟩

/-- **If the rotations by multiples of `m` and the reflections in the coset `b + ⟨m⟩` exhaust the
dihedral group, then `m` is a unit.** -/
theorem isUnit_of_rotCoset_eq_top {m b : ZMod n} (h : rotCoset m b = ⊤) : IsUnit m := by
  have hmem : DihedralGroup.r (1 : ZMod n) ∈ rotCoset m b := h ▸ Subgroup.mem_top _
  obtain ⟨i, hi | hi⟩ := hmem
  · have hmul : m * (i : ZMod n) = 1 := by
      rw [mul_comm, ← zsmul_eq_mul]
      exact ((DihedralGroup.r.injEq _ _).mp hi).symm
    exact ⟨⟨m, (i : ZMod n), hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩
  · exact absurd hi (by simp)

end Subgroups

/-! ### The distinguished inertia generators in dihedral coordinates -/

/-- **The distinguished inertia generators of the inverted dihedral cover, in dihedral
coordinates.**

Inertia at the origin is generated by a rotation `r m` of maximal order, inertia at `1/2` by a
reflection `sr j`, and inertia at `-1/2` by the reflection `sr (j - m)`. -/
theorem exists_inertiaGens_dihInfCover (n : ℕ) [NeZero n] (hn : 3 ≤ n) {ζ : k}
    (hζ : IsPrimitiveRoot ζ n) :
    ∃ m j : ZMod n, IsUnit m ∧
      (dihInfCover n).IsInertiaGenAt 0 (dihInfDeckEquiv hζ (DihedralGroup.r m)) ∧
      (dihInfCover n).IsInertiaGenAt 2⁻¹ (dihInfDeckEquiv hζ (DihedralGroup.sr j)) ∧
      (dihInfCover n).IsInertiaGenAt (-2⁻¹)
        (dihInfDeckEquiv hζ (DihedralGroup.sr (j - m))) := by
  obtain ⟨g, hgin, -, hgprod⟩ :=
    exists_inertiaGens_mod_commutator (dihInfCover n) dihPts dihPts_injective
      (isUnramifiedOutside_dihPts n) (isUnramifiedAtInfinity_dihInfCover n)
  have hin0 : (dihInfCover n).IsInertiaGenAt 0 (g 0) := by
    rw [← dihPts_zero]; exact hgin 0
  have hin1 : (dihInfCover n).IsInertiaGenAt 2⁻¹ (g 1) := by
    rw [← dihPts_one]; exact hgin 1
  have hin2 : (dihInfCover n).IsInertiaGenAt (-2⁻¹) (g 2) := by
    rw [← dihPts_two]; exact hgin 2
  obtain ⟨m, hmunit, hm⟩ := exists_r_of_isInertiaGenAt_zero hζ hn hin0
  obtain ⟨j₁, hj₁⟩ :=
    exists_sr_of_isInertiaGenAt_refl hζ (one_pow 2) (by rwa [one_mul] : _)
  obtain ⟨j₂, hj₂⟩ :=
    exists_sr_of_isInertiaGenAt_refl hζ (neg_one_sq (R := k)) (by rwa [neg_one_mul] : _)
  set e := dihInfDeckEquiv hζ with he
  have hprodeq : (List.ofFn g).prod = g 0 * g 1 * g 2 := by
    simp [List.ofFn_succ, mul_assoc]
  have hsym : e.symm ((List.ofFn g).prod) = DihedralGroup.r (m + j₂ - j₁) := by
    rw [hprodeq, hm, hj₁, hj₂, ← map_mul, ← map_mul, MulEquiv.symm_apply_apply, dih_triple_mul]
  have hcomm : DihedralGroup.r (m + j₂ - j₁) ∈ commutator (DihedralGroup n) := by
    rw [← hsym]
    exact mem_commutator_of_mulEquiv e hgprod
  obtain ⟨i, hi⟩ := mem_evenRot.mp (commutator_le_evenRot n hcomm)
  have hi' : m + j₂ - j₁ = 2 * i := by rwa [DihedralGroup.r.injEq] at hi
  have hconj : e (DihedralGroup.r i) * g 2 * (e (DihedralGroup.r i))⁻¹
      = e (DihedralGroup.sr (j₁ - m)) := by
    rw [hj₂, ← map_inv, ← map_mul, ← map_mul, dih_triple_correct hi']
  refine ⟨m, j₁, hmunit, ?_, ?_, ?_⟩
  · rw [← hm]; exact hin0
  · rw [← hj₁]; exact hin1
  · rw [← hconj]; exact hin2.conj _

/-! ### Realizing an arbitrary dihedral datum -/

/-- **The inverted dihedral cover, relabelled so that a prescribed rotation of maximal order and a
prescribed reflection are the distinguished inertia generators at `0` and at `1/2`.**

The reflections `sr (b - m)` and `sr (b + m)` are then both distinguished inertia generators at
`-1/2`: they are conjugate by the rotation `r m`. -/
theorem exists_cover_dihedral_aux (n : ℕ) [NeZero n] (hn : 3 ≤ n) {m b : ZMod n} (hm : IsUnit m) :
    ∃ (L : LineCover) (e : L.deck ≃* DihedralGroup n),
      L.IsUnramifiedOutside ({0, 2⁻¹, -2⁻¹} : Set k) ∧ L.IsUnramifiedAtInfinity ∧
      L.IsInertiaGenAt 0 (e.symm (DihedralGroup.r m)) ∧
      L.IsInertiaGenAt 2⁻¹ (e.symm (DihedralGroup.sr b)) ∧
      L.IsInertiaGenAt (-2⁻¹) (e.symm (DihedralGroup.sr (b - m))) ∧
      L.IsInertiaGenAt (-2⁻¹) (e.symm (DihedralGroup.sr (b + m))) := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_algebraicClosure n (dihPos n)
  obtain ⟨m₀, j₀, hm₀, hA, hB, hC⟩ := exists_inertiaGens_dihInfCover n hn hζ
  set E := dihInfDeckEquiv hζ with hE
  -- the unit carrying `m₀` to `m`
  set U : (ZMod n)ˣ := hm.unit * hm₀.unit⁻¹ with hU
  have hUm : (U : ZMod n) * m₀ = m := by
    have h1 : ((hm₀.unit⁻¹ : (ZMod n)ˣ) : ZMod n) * m₀ = 1 := by
      have h := Units.inv_mul hm₀.unit
      rwa [hm₀.unit_spec] at h
    rw [hU, Units.val_mul, mul_assoc, h1, mul_one, hm.unit_spec]
  set α : DihedralGroup n ≃* DihedralGroup n := dihAut U (b - (U : ZMod n) * j₀) with hα
  refine ⟨dihInfCover n, E.symm.trans α, ?_, isUnramifiedAtInfinity_dihInfCover n, ?_, ?_, ?_, ?_⟩
  · rw [← range_dihPts]
    exact isUnramifiedOutside_dihPts n
  all_goals
    have hsymm : ∀ x, (E.symm.trans α).symm x = E (α.symm x) := fun _ => rfl
  · rw [hsymm]
    have : α.symm (DihedralGroup.r m) = DihedralGroup.r m₀ := by
      rw [MulEquiv.symm_apply_eq, hα, dihAut_r, hUm]
    rw [this]
    exact hA
  · rw [hsymm]
    have : α.symm (DihedralGroup.sr b) = DihedralGroup.sr j₀ := by
      rw [MulEquiv.symm_apply_eq, hα, dihAut_sr]
      congr 1
      ring
    rw [this]
    exact hB
  · rw [hsymm]
    have : α.symm (DihedralGroup.sr (b - m)) = DihedralGroup.sr (j₀ - m₀) := by
      rw [MulEquiv.symm_apply_eq, hα, dihAut_sr]
      congr 1
      rw [← hUm]
      ring
    rw [this]
    exact hC
  · rw [hsymm]
    have hval : α.symm (DihedralGroup.sr (b + m)) = DihedralGroup.sr (j₀ + m₀) := by
      rw [MulEquiv.symm_apply_eq, hα, dihAut_sr]
      congr 1
      rw [← hUm]
      ring
    have hconj : E (DihedralGroup.r (-m₀)) * E (DihedralGroup.sr (j₀ - m₀))
        * (E (DihedralGroup.r (-m₀)))⁻¹ = E (DihedralGroup.sr (j₀ + m₀)) := by
      rw [← map_inv, ← map_mul, ← map_mul, DihedralGroup.inv_r, DihedralGroup.r_mul_sr,
        DihedralGroup.sr_mul_r]
      congr 2
      ring
    rw [hval, ← hconj]
    exact hC.conj _

/-- The range of a triple, listed. -/
theorem range_fin3 {α : Type*} (f : Fin 3 → α) : Set.range f = {f 0, f 1, f 2} := by
  ext x
  constructor
  · rintro ⟨l, rfl⟩
    fin_cases l
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]

/-- Two of the three orderings of the branch points, as sets. -/
theorem dihSet_perm₁ : ({2⁻¹, 0, -2⁻¹} : Set k) = {0, 2⁻¹, -2⁻¹} := Set.insert_comm _ _ _

theorem dihSet_perm₂ : ({2⁻¹, -2⁻¹, 0} : Set k) = {0, 2⁻¹, -2⁻¹} := by
  ext u
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- **Every generating product-one triple in a dihedral group is realized as the tuple of
distinguished inertia generators of a cover of the line branched over `0`, `1/2` and `-1/2`.**

This is the existence half of the Riemann existence correspondence for dihedral groups over three
branch points: the branch points can be taken to be a fixed triple, only their ordering depending
on the datum. -/
theorem exists_cover_dihedral (n : ℕ) [NeZero n] (hn : 3 ≤ n) {h : Fin 3 → DihedralGroup n}
    (hprod : (List.ofFn h).prod = 1) (htop : Subgroup.closure (Set.range h) = ⊤) :
    ∃ (t : Fin 3 → k) (L : LineCover) (e : L.deck ≃* DihedralGroup n),
      Set.range t = ({0, 2⁻¹, -2⁻¹} : Set k) ∧
      L.IsUnramifiedOutside (Set.range t) ∧ L.IsUnramifiedAtInfinity ∧
      ∀ i, L.IsInertiaGenAt (t i) (e.symm (h i)) := by
  obtain ⟨x, y, z, rfl⟩ : ∃ x y z, h = ![x, y, z] :=
    ⟨h 0, h 1, h 2, by funext l; fin_cases l <;> rfl⟩
  have hp : x * y * z = 1 := by
    rw [← hprod]
    simp [List.ofFn_succ, mul_assoc]
  -- a subgroup containing the three entries is everything
  have hsub : ∀ K : Subgroup (DihedralGroup n),
      ({x, y, z} : Set (DihedralGroup n)) ⊆ (K : Set (DihedralGroup n)) → K = ⊤ := by
    intro K hK
    refine eq_top_iff.mpr ?_
    rw [← htop]
    refine (Subgroup.closure_le K).mpr ?_
    rw [range_fin3]
    exact hK
  -- hence the rotation parameter of an admissible triple is a unit
  have hunit : ∀ m b : ZMod n, ({x, y, z} : Set (DihedralGroup n))
      ⊆ (rotCoset m b : Set (DihedralGroup n)) → IsUnit m :=
    fun m b hK => isUnit_of_rotCoset_eq_top (hsub _ hK)
  cases x with
  | r a =>
    cases y with
    | r b =>
      cases z with
      | r c =>
        -- three rotations never generate
        exfalso
        refine sr_notMem_rotations (0 : ZMod n) ?_
        rw [hsub (rotations n) ?_]
        · trivial
        · rintro g hg
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
          rcases hg with rfl | rfl | rfl
          exacts [⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩]
      | sr c =>
        exfalso
        rw [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr] at hp
        exact sr_ne_one _ hp
    | sr b =>
      cases z with
      | r c =>
        exfalso
        rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r] at hp
        exact sr_ne_one _ hp
      | sr c =>
        -- the rotation sits in the first slot
        have hc : c = b - a := by
          rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_sr, DihedralGroup.one_def,
            DihedralGroup.r.injEq] at hp
          linear_combination hp
        subst hc
        have ha : IsUnit a := by
          refine hunit a b ?_
          rintro g hg
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
          rcases hg with rfl | rfl | rfl
          exacts [r_mem_rotCoset a b, sr_mem_rotCoset a b, sr_sub_mem_rotCoset a b]
        obtain ⟨L, e, hout, hinf, h0, h1, h2, -⟩ := exists_cover_dihedral_aux n hn ha (b := b)
        have hr : Set.range (![0, 2⁻¹, -2⁻¹] : Fin 3 → k) = ({0, 2⁻¹, -2⁻¹} : Set k) := by
          rw [range_fin3]
          rfl
        refine ⟨![0, 2⁻¹, -2⁻¹], L, e, hr, by rw [hr]; exact hout, hinf, ?_⟩
        intro l
        fin_cases l
        exacts [h0, h1, h2]
  | sr a =>
    cases y with
    | r b =>
      cases z with
      | r c =>
        exfalso
        rw [DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_r] at hp
        exact sr_ne_one _ hp
      | sr c =>
        -- the rotation sits in the second slot
        have hc : c = a + b := by
          rw [DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, DihedralGroup.one_def,
            DihedralGroup.r.injEq] at hp
          linear_combination hp
        subst hc
        have hb : IsUnit b := by
          refine hunit b a ?_
          rintro g hg
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
          rcases hg with rfl | rfl | rfl
          exacts [sr_mem_rotCoset b a, r_mem_rotCoset b a, sr_add_mem_rotCoset b a]
        obtain ⟨L, e, hout, hinf, h0, h1, -, h2⟩ := exists_cover_dihedral_aux n hn hb (b := a)
        have hr : Set.range (![2⁻¹, 0, -2⁻¹] : Fin 3 → k) = ({0, 2⁻¹, -2⁻¹} : Set k) := by
          rw [range_fin3]
          exact dihSet_perm₁
        refine ⟨![2⁻¹, 0, -2⁻¹], L, e, hr, by rw [hr]; exact hout, hinf, ?_⟩
        intro l
        fin_cases l
        exacts [h1, h0, h2]
    | sr b =>
      cases z with
      | r c =>
        -- the rotation sits in the third slot
        have hb : b = a - c := by
          rw [DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_r, DihedralGroup.one_def,
            DihedralGroup.r.injEq] at hp
          linear_combination hp
        subst hb
        have hcu : IsUnit c := by
          refine hunit c a ?_
          rintro g hg
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
          rcases hg with rfl | rfl | rfl
          exacts [sr_mem_rotCoset c a, sr_sub_mem_rotCoset c a, r_mem_rotCoset c a]
        obtain ⟨L, e, hout, hinf, h0, h1, h2, -⟩ := exists_cover_dihedral_aux n hn hcu (b := a)
        have hr : Set.range (![2⁻¹, -2⁻¹, 0] : Fin 3 → k) = ({0, 2⁻¹, -2⁻¹} : Set k) := by
          rw [range_fin3]
          exact dihSet_perm₂
        refine ⟨![2⁻¹, -2⁻¹, 0], L, e, hr, by rw [hr]; exact hout, hinf, ?_⟩
        intro l
        fin_cases l
        exacts [h1, h2, h0]
      | sr c =>
        exfalso
        rw [DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_sr] at hp
        exact sr_ne_one _ hp

end Rigidity.RET

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Rigidity.StructureCount
import InverseGalois.Rigidity.RET.Descent
import Mathieu.EnumM11
import Mathieu.M12Simple

/-!
# A rigid class triple in the Mathieu group `M₁₂`

`M₁₂` has fifteen conjugacy classes, and exactly eight unordered triples of them are **rigid**:
`(2A, 3A, 11A/B)`, `(2A, 4A, 11A/B)`, `(2A, 4B, 11A/B)` and `(2B, 3B, 11A/B)`.  This file
certifies one of them in the Lean kernel:

`(2A, 3A, 11A)` — a fixed-point-free involution (cycle type `2⁶`), an element of cycle type
`3³1³`, and the standard `11`-cycle generator `m12a`.

Concretely, with `z = m12a` and the involution

`x = m12b⁻¹ · m12c · m12a⁻¹ · m12b² · m12a⁻¹ · m12c · m12a⁻¹`

the pair `x, z` generates `M₁₂`, and the structure constant `#{w ∈ 2A : w z⁻¹ ∈ 3A}` equals
`11 = |C_{M₁₂}(z)|`.  By `Rigidity.rigid_of_card_prodOneFibre` that single count forces
`Nat.card (rigidTuples classTriple) = Nat.card M₁₂`: the product-one triples in these three
classes form a single simultaneous-conjugacy orbit, which is rigidity.

## How the count is certified

Permutations are handled in a base-`12` integer encoding (`enc12`, `dec12`, `φ12`), the exact
analogue of the base-`11` encoding of `Mathieu.EnumM11`, together with a multiplication `mulC12`
of two encoded permutations; it is `stepImg12` applied to the digit function of the left factor,
so `stepImg12_bridge` gives `mulC12 (φ12 g) (φ12 p) = φ12 (g * p)` immediately.

The class `2A` is stored as a binary search-tree literal `TX` (`396` keys).  The kernel checks by
`decide` that it is closed under conjugation by the three generators and their inverses; since
`Btree.mem` is one-sidedly sound, that alone gives the containment *class ⊆ tree*, which is what
an upper bound on the fibre needs.  For the second class no tree is required.  Both `3A` and `3B`
consist of elements of order `3`, but `3A = 3³1³` has fixed points while `3B = 3⁴` does not, so
the pair of tests `q³ = 1` and "`q` fixes a point" cuts out `3A` among the relevant codes; both
are conjugation-invariant and cheap.  Filtering `TX` by that test applied to `w z⁻¹` leaves
exactly `11` keys, and the fibre injects into that list by `w ↦ φ12 w`, using that every element
of `2A` is an involution.

Nothing here uses `native_decide`.

## Main results

* `Rigidity.MathieuM12.center_eq_bot` — `M₁₂` is centerless.
* `Rigidity.MathieuM12.gen_top` — the pair `x, z` generates `M₁₂`.
* `Rigidity.MathieuM12.card_prodOneFibre_le` — the structure constant is at most `11`.
* `Rigidity.MathieuM12.rigid_triple` — `Nat.card (rigidTuples classTriple) = Nat.card M₁₂`.

The classes `11A` and `11B` are not rational (`m12a` is not conjugate to `m12a ^ 2` inside
`M₁₂`), so this triple does not assemble into a `RigidityCertificate M₁₂`, whose classes must
each be fixed by the whole cyclotomic action; the field cut out by the stabiliser of the triple
is `ℚ(√-11)`.
-/

namespace Rigidity

namespace MathieuM12

open Equiv Mathieu Mathieu.EnumM11

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

/-! ### The base-`12` encoding of permutations -/

/-- Encode an image vector `f : Fin 12 → Fin 12` as the base-`12` numeral
`∑ i, (f i) * 12 ^ i`. -/
def enc12 (f : Fin 12 → Fin 12) : ℕ := ∑ i : Fin 12, (f i).val * 12 ^ (i : ℕ)

/-- Decode a natural number back to an image vector (`i`-th base-`12` digit). -/
def dec12 (n : ℕ) : Fin 12 → Fin 12 :=
  fun i => ⟨(n / 12 ^ (i : ℕ)) % 12, Nat.mod_lt _ (by norm_num)⟩

/-- Apply a permutation `g` to an encoded permutation: decode, left-multiply, re-encode. -/
def applyGenF12 (g : Perm (Fin 12)) (n : ℕ) : ℕ := enc12 (fun i => g (dec12 n i))

/-- Encoding of the identity permutation. -/
def idCode12 : ℕ := enc12 id

/-- The encoding of a permutation by its image vector. -/
def φ12 (p : Perm (Fin 12)) : ℕ := enc12 (fun i => p i)

lemma enc12_eq (f : Fin 12 → Fin 12) : enc12 f = (finFunctionFinEquiv f).val := by
  rw [finFunctionFinEquiv_apply_val]; rfl

lemma dec12_enc12 (f : Fin 12 → Fin 12) : dec12 (enc12 f) = f := by
  funext j
  apply Fin.ext
  show (enc12 f / 12 ^ (j : ℕ)) % 12 = (f j).val
  have h := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv f) j
  rw [Equiv.symm_apply_apply] at h
  rw [enc12_eq]; omega

lemma φ12_injective : Function.Injective φ12 := by
  intro p q h
  have h2 : dec12 (φ12 p) = dec12 (φ12 q) := by rw [h]
  rw [φ12, φ12, dec12_enc12, dec12_enc12] at h2
  exact Equiv.ext (fun i => congrFun h2 i)

lemma applyGenF12_φ12 (g p : Perm (Fin 12)) : applyGenF12 g (φ12 p) = φ12 (g * p) := by
  unfold applyGenF12 φ12
  rw [dec12_enc12]
  congr 1

lemma φ12_one : φ12 1 = idCode12 := by
  unfold φ12 idCode12
  congr 1

/-- Kernel-friendly digit-permutation apply (no `Finset.sum`): permutes the base-`12` digits of
`n` by the table `t`. -/
def stepImg12 (t : ℕ → ℕ) (n : ℕ) : ℕ :=
  t (n / 12^0 % 12) + 12*(t (n / 12^1 % 12) + 12*(t (n / 12^2 % 12) + 12*(t (n / 12^3 % 12)
  + 12*(t (n / 12^4 % 12) + 12*(t (n / 12^5 % 12) + 12*(t (n / 12^6 % 12) + 12*(t (n / 12^7 % 12)
  + 12*(t (n / 12^8 % 12) + 12*(t (n / 12^9 % 12) + 12*(t (n / 12^10 % 12)
  + 12*(t (n / 12^11 % 12))))))))))))

/-- Generic bridge: a permutation `g` whose value table on `0..11` is `t` acts on encoded codes
as `stepImg12 t`. -/
lemma stepImg12_bridge (g : Perm (Fin 12)) (t : ℕ → ℕ)
    (h : ∀ x : Fin 12, (g x).val = t x.val) (n : ℕ) : stepImg12 t n = applyGenF12 g n := by
  simp only [applyGenF12, enc12, stepImg12, Fin.sum_univ_succ, Fin.sum_univ_zero, h, dec12,
    Fin.val_succ, Fin.val_zero]
  ring

/-! ### Multiplication of encoded permutations -/

/-- The `j`-th base-`12` digit of a code. -/
def dg12 (a j : ℕ) : ℕ := a / 12 ^ j % 12

/-- Product of two encoded permutations: permute the digits of the right factor by the digit
table of the left factor. -/
def mulC12 (a b : ℕ) : ℕ := stepImg12 (dg12 a) b

lemma dg12_φ12 (g : Perm (Fin 12)) (i : Fin 12) : (g i).val = dg12 (φ12 g) i.val := by
  have h : dec12 (φ12 g) = fun i => g i := dec12_enc12 _
  exact (congrArg Fin.val (congrFun h i)).symm

lemma mulC12_φ12 (g p : Perm (Fin 12)) : mulC12 (φ12 g) (φ12 p) = φ12 (g * p) := by
  rw [mulC12, stepImg12_bridge g (dg12 (φ12 g)) (dg12_φ12 g), applyGenF12_φ12]

lemma mulC12_conj (g q : Perm (Fin 12)) :
    mulC12 (φ12 g) (mulC12 (φ12 q) (φ12 g⁻¹)) = φ12 (g * q * g⁻¹) := by
  rw [mulC12_φ12, mulC12_φ12, mul_assoc]

lemma mulC12_conj' (g q : Perm (Fin 12)) :
    mulC12 (φ12 g⁻¹) (mulC12 (φ12 q) (φ12 g)) = φ12 (g⁻¹ * q * g) := by
  rw [mulC12_φ12, mulC12_φ12, mul_assoc]

/-- `m12c` is an involution, so it is its own inverse. -/
lemma m12c_inv : m12c⁻¹ = m12c := by decide

/-! ### The three elements of the triple -/

/-- `m12b` is a member of `M₁₂`. -/
theorem m12b_mem : m12b ∈ M12 :=
  Subgroup.subset_closure (by right; left; rfl)

/-- The involution of the triple, as an explicit word in the three standard generators. -/
def x0 : Perm (Fin 12) :=
  m12b⁻¹ * m12c * m12a⁻¹ * m12b * m12b * m12a⁻¹ * m12c * m12a⁻¹

lemma x0_mem : x0 ∈ M12 := by
  unfold x0
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
    (inv_mem m12b_mem) m12c_mem) (inv_mem m12a_mem)) m12b_mem) m12b_mem)
    (inv_mem m12a_mem)) m12c_mem) (inv_mem m12a_mem)

lemma x0_sq : x0 * x0 = 1 := by decide

/-- The involution of the triple, as an element of `M₁₂`. -/
def xEl : ↥M12 := ⟨x0, x0_mem⟩

/-- The `11`-cycle of the triple: the standard generator `m12a`. -/
def zEl : ↥M12 := ⟨m12a, m12a_mem⟩

/-- The remaining entry of the triple, forced by the product-one relation. -/
def yEl : ↥M12 := xEl⁻¹ * zEl⁻¹

/-- The triple of conjugacy classes `(2A, 3A, 11A)` of `M₁₂`. -/
def classTriple : Fin 3 → ConjClasses ↥M12 :=
  ![ConjClasses.mk xEl, ConjClasses.mk yEl, ConjClasses.mk zEl]

lemma classTriple_zero : classTriple 0 = ConjClasses.mk xEl := rfl
lemma classTriple_one : classTriple 1 = ConjClasses.mk yEl := rfl
lemma classTriple_two : classTriple 2 = ConjClasses.mk zEl := rfl

lemma xEl_sq : xEl * xEl = 1 := Subtype.ext x0_sq

lemma xEl_inv : xEl⁻¹ = xEl := inv_eq_of_mul_eq_one_right xEl_sq

/-! ### Codes of the generators -/

/-- Code of `m12a`. -/
def cA : ℕ := 8228868876745
/-- Code of `m12a⁻¹`. -/
def cAi : ℕ := 8774867452186
/-- Code of `m12b`. -/
def cB : ℕ := 8630694992172
/-- Code of `m12b⁻¹`. -/
def cBi : ℕ := 8563880939196
/-- Code of `m12c`, which is an involution and so equals the code of `m12c⁻¹`. -/
def cC : ℕ := 94731018899

lemma cA_eq : φ12 m12a = cA := by decide
lemma cAi_eq : φ12 m12a⁻¹ = cAi := by decide
lemma cB_eq : φ12 m12b = cB := by decide
lemma cBi_eq : φ12 m12b⁻¹ = cBi := by decide
lemma cC_eq : φ12 m12c = cC := by decide
lemma cCi_eq : φ12 m12c⁻¹ = cC := by decide

lemma x0_code : φ12 x0 = 5067978086017 := by decide

/-- Conjugation by `m12c` in codes, using that `m12c` is its own inverse. -/
lemma mulC12_conj_c (q : Perm (Fin 12)) :
    mulC12 cC (mulC12 (φ12 q) cC) = φ12 (m12c * q * m12c) := by
  rw [← cC_eq, mulC12_φ12, mulC12_φ12, mul_assoc]

/-! ### Conjugation-closed sets of codes

A tree of codes closed under conjugation by the three generators and their inverses contains the
whole `M₁₂`-conjugacy class of each of its keys.  Only the one-sided soundness of `Btree.mem` is
used, so no search-tree invariant is needed. -/

/-- The conjugation-closure test for a tree of codes. -/
abbrev ConjClosed (T : Btree) : Prop :=
  T.all (fun k => T.mem (mulC12 cA (mulC12 k cAi)) && T.mem (mulC12 cAi (mulC12 k cA)) &&
    T.mem (mulC12 cB (mulC12 k cBi)) && T.mem (mulC12 cBi (mulC12 k cB)) &&
    T.mem (mulC12 cC (mulC12 k cC))) = true

lemma conj_gen_key {T : Btree} (hcl : ConjClosed T) {q : Perm (Fin 12)}
    (hq : T.mem (φ12 q) = true) :
    T.mem (φ12 (m12a * q * m12a⁻¹)) = true ∧ T.mem (φ12 (m12a⁻¹ * q * m12a)) = true ∧
      T.mem (φ12 (m12b * q * m12b⁻¹)) = true ∧ T.mem (φ12 (m12b⁻¹ * q * m12b)) = true ∧
      T.mem (φ12 (m12c * q * m12c⁻¹)) = true ∧ T.mem (φ12 (m12c⁻¹ * q * m12c)) = true := by
  have h := Btree.all_toList hcl _ (Btree.mem_toList hq)
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← cA_eq, ← cAi_eq, mulC12_conj] at h1; exact h1
  · rw [← cAi_eq, ← cA_eq, mulC12_conj'] at h2; exact h2
  · rw [← cB_eq, ← cBi_eq, mulC12_conj] at h3; exact h3
  · rw [← cBi_eq, ← cB_eq, mulC12_conj'] at h4; exact h4
  · rw [mulC12_conj_c] at h5; rw [m12c_inv]; exact h5
  · rw [mulC12_conj_c] at h5; rw [m12c_inv]; exact h5

/-- Closure under conjugation by the generators propagates to all of `M₁₂`. -/
theorem conj_key {T : Btree} (hcl : ConjClosed T) {c : Perm (Fin 12)} (hc : c ∈ M12)
    {p : Perm (Fin 12)} (hp : T.mem (φ12 p) = true) : T.mem (φ12 (c * p * c⁻¹)) = true := by
  have hc' : c ∈ Subgroup.closure ({m12a, m12b, m12c} : Set (Perm (Fin 12))) := hc
  refine Subgroup.closure_induction_left
    (p := fun c _ => ∀ q : Perm (Fin 12), T.mem (φ12 q) = true →
      T.mem (φ12 (c * q * c⁻¹)) = true) ?_ ?_ ?_ hc' p hp
  · intro q hq; simpa using hq
  · intro g hg y _ ih q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    have hstep : g * y * q * (g * y)⁻¹ = g * (y * q * y⁻¹) * g⁻¹ := by group
    rw [hstep]
    rcases hg with rfl | rfl | rfl
    · exact (conj_gen_key hcl (ih q hq)).1
    · exact (conj_gen_key hcl (ih q hq)).2.2.1
    · exact (conj_gen_key hcl (ih q hq)).2.2.2.2.1
  · intro g hg y _ ih q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    have hstep : g⁻¹ * y * q * (g⁻¹ * y)⁻¹ = g⁻¹ * (y * q * y⁻¹) * g := by group
    rw [hstep]
    rcases hg with rfl | rfl | rfl
    · exact (conj_gen_key hcl (ih q hq)).2.1
    · exact (conj_gen_key hcl (ih q hq)).2.2.2.1
    · exact (conj_gen_key hcl (ih q hq)).2.2.2.2.2

/-- Every member of the conjugacy class of a key is again a key. -/
theorem key_of_conjClass {T : Btree} (hcl : ConjClosed T) {p : Perm (Fin 12)}
    (hp : T.mem (φ12 p) = true) {u w : ↥M12} (hu : (u : Perm (Fin 12)) = p)
    (hw : ConjClasses.mk w = ConjClasses.mk u) : T.mem (φ12 (w : Perm (Fin 12))) = true := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hw)
  have hval : (c : Perm (Fin 12)) * (w : Perm (Fin 12)) * ((c : Perm (Fin 12)))⁻¹ = p := by
    rw [← hu, ← hc]; rfl
  have hw' : (w : Perm (Fin 12)) = ((c : Perm (Fin 12)))⁻¹ * p * (((c : Perm (Fin 12)))⁻¹)⁻¹ := by
    rw [← hval]; group
  rw [hw']
  exact conj_key hcl (inv_mem c.2) hp

/-! ### `M₁₂` is centerless -/

theorem center_eq_bot : Subgroup.center (↥M12) = ⊥ := by
  rcases M12_isSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥M12)
    inferInstance with h | h
  · exact h
  · exfalso
    haveI : IsMulCommutative ↥M12 := by
      constructor
      constructor
      intro x y
      have hy : y ∈ Subgroup.center ↥M12 := by rw [h]; exact Subgroup.mem_top y
      exact Subgroup.mem_center_iff.mp hy x
    have hp : (Nat.card ↥M12).Prime :=
      (Group.is_simple_iff_prime_card (α := ↥M12)).mp M12_isSimpleGroup
    rw [M12_card] at hp
    exact absurd hp (by norm_num)

/-! ### The pair generates -/

/-- If a subgroup of `M₁₂` contains all three standard generators, it is everything. -/
theorem eq_top_of_gens_mem (K : Subgroup ↥M12)
    (ha : (⟨m12a, m12a_mem⟩ : ↥M12) ∈ K) (hb : (⟨m12b, m12b_mem⟩ : ↥M12) ∈ K)
    (hcg : (⟨m12c, m12c_mem⟩ : ↥M12) ∈ K) : K = ⊤ := by
  have key : ∀ (p : Perm (Fin 12)) (hp : p ∈ M12), (⟨p, hp⟩ : ↥M12) ∈ K := by
    intro p hp
    have hp' : p ∈ Subgroup.closure ({m12a, m12b, m12c} : Set (Perm (Fin 12))) := hp
    refine Subgroup.closure_induction_left
      (p := fun q hq => (⟨q, hq⟩ : ↥M12) ∈ K) ?_ ?_ ?_ hp'
    · exact one_mem K
    · intro g hg y hy ih
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      have hgm : g ∈ M12 := by
        rcases hg with rfl | rfl | rfl; exacts [m12a_mem, m12b_mem, m12c_mem]
      have hgK : (⟨g, hgm⟩ : ↥M12) ∈ K := by rcases hg with rfl | rfl | rfl; exacts [ha, hb, hcg]
      exact (show (⟨g, hgm⟩ : ↥M12) * ⟨y, hy⟩ ∈ K from mul_mem hgK ih)
    · intro g hg y hy ih
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      have hgm : g ∈ M12 := by
        rcases hg with rfl | rfl | rfl; exacts [m12a_mem, m12b_mem, m12c_mem]
      have hgK : (⟨g, hgm⟩ : ↥M12) ∈ K := by rcases hg with rfl | rfl | rfl; exacts [ha, hb, hcg]
      exact (show (⟨g, hgm⟩ : ↥M12)⁻¹ * ⟨y, hy⟩ ∈ K from mul_mem (inv_mem hgK) ih)
  rw [Subgroup.eq_top_iff']
  rintro ⟨p, hp⟩
  exact key p hp

theorem gen_top : Subgroup.closure ({xEl, zEl} : Set ↥M12) = ⊤ := by
  have hxK : xEl ∈ Subgroup.closure ({xEl, zEl} : Set ↥M12) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hzK : zEl ∈ Subgroup.closure ({xEl, zEl} : Set ↥M12) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hiK : zEl⁻¹ ∈ Subgroup.closure ({xEl, zEl} : Set ↥M12) := inv_mem hzK
  refine eq_top_of_gens_mem _ hzK ?_ ?_
  · have hval : (⟨m12b, m12b_mem⟩ : ↥M12) =
        zEl⁻¹ * zEl⁻¹ * zEl⁻¹ * zEl⁻¹ * zEl⁻¹ * xEl * zEl * zEl * xEl * zEl⁻¹ * zEl⁻¹ * xEl *
          zEl * xEl * zEl⁻¹ := by
      apply Subtype.ext
      show m12b = m12a⁻¹ * m12a⁻¹ * m12a⁻¹ * m12a⁻¹ * m12a⁻¹ * x0 * m12a * m12a * x0 * m12a⁻¹ *
        m12a⁻¹ * x0 * m12a * x0 * m12a⁻¹
      decide
    rw [hval]
    exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
      (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem hiK hiK) hiK) hiK) hiK) hxK) hzK) hzK) hxK)
      hiK) hiK) hxK) hzK) hxK) hiK
  · have hval : (⟨m12c, m12c_mem⟩ : ↥M12) =
        xEl * zEl * zEl * zEl * zEl * xEl * zEl⁻¹ * zEl⁻¹ * zEl⁻¹ * zEl⁻¹ * xEl := by
      apply Subtype.ext
      show m12c = x0 * m12a * m12a * m12a * m12a * x0 * m12a⁻¹ * m12a⁻¹ * m12a⁻¹ * m12a⁻¹ * x0
      decide
    rw [hval]
    exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
      (mul_mem hxK hzK) hzK) hzK) hzK) hxK) hiK) hiK) hiK) hiK) hxK

/-! ### The class tree -/

/-- The `396` codes of the class `2A` of `M₁₂` (the fixed-point-free involutions, of cycle
type `2⁶`). -/
noncomputable def TX : Btree :=
  (Btree.nd (Btree.nd (Btree.nd (Btree.nd (Btree.nd (Btree.nd (Btree.nd (Btree.nd (Btree.nd
  Btree.lf 75546276179 Btree.lf ) 79784554883 (Btree.nd Btree.lf 94731018899 Btree.lf ))
  107153599091 (Btree.nd (Btree.nd Btree.lf 142098786203 Btree.lf ) 145816251647 Btree.lf ))
  158117912975 (Btree.nd (Btree.nd (Btree.nd Btree.lf 161999512499 Btree.lf ) 198819171287 Btree.lf
  ) 213315148607 (Btree.nd (Btree.nd Btree.lf 222639505451 Btree.lf ) 231137179955 Btree.lf )))
  253926057143 (Btree.nd (Btree.nd (Btree.nd (Btree.nd Btree.lf 260185925615 Btree.lf )
  276146249951 Btree.lf ) 279266106779 (Btree.nd (Btree.nd Btree.lf 318054626615 Btree.lf )
  325976530847 Btree.lf )) 332939903219 (Btree.nd (Btree.nd (Btree.nd Btree.lf 354883849859
  Btree.lf ) 378127755335 Btree.lf ) 387516147227 (Btree.nd (Btree.nd Btree.lf 400631737451
  Btree.lf ) 410126962355 Btree.lf )))) 454855885451 (Btree.nd (Btree.nd (Btree.nd (Btree.nd
  (Btree.nd Btree.lf 460873995923 Btree.lf ) 465625706183 (Btree.nd Btree.lf 478937433227 Btree.lf
  )) 504985454039 (Btree.nd (Btree.nd Btree.lf 510069885347 Btree.lf ) 520514184311 Btree.lf ))
  536092247999 (Btree.nd (Btree.nd (Btree.nd Btree.lf 609837997307 Btree.lf ) 610337009843 Btree.lf
  ) 610655056055 (Btree.nd (Btree.nd Btree.lf 611155427663 Btree.lf ) 760444211230 Btree.lf )))
  766432361662 (Btree.nd (Btree.nd (Btree.nd (Btree.nd Btree.lf 770248916206 Btree.lf )
  776253375502 Btree.lf ) 869555485293 (Btree.nd (Btree.nd Btree.lf 885631052009 Btree.lf )
  889643276203 Btree.lf )) 912135406314 (Btree.nd (Btree.nd (Btree.nd Btree.lf 930568660989
  Btree.lf ) 960749473673 Btree.lf ) 967359301480 (Btree.nd (Btree.nd Btree.lf 974101528070
  Btree.lf ) 1002303978907 Btree.lf ))))) 1007198257098 (Btree.nd (Btree.nd (Btree.nd (Btree.nd
  (Btree.nd (Btree.nd Btree.lf 1024960872518 Btree.lf ) 1029723260247 (Btree.nd Btree.lf
  1055900248557 Btree.lf )) 1063036818140 (Btree.nd (Btree.nd Btree.lf 1074332845575 Btree.lf )
  1090758725562 Btree.lf )) 1135254143804 (Btree.nd (Btree.nd (Btree.nd Btree.lf 1141311029320
  Btree.lf ) 1152273365705 Btree.lf ) 1159691061595 (Btree.nd (Btree.nd Btree.lf 1189711647641
  Btree.lf ) 1192274666924 Btree.lf ))) 1204318440710 (Btree.nd (Btree.nd (Btree.nd (Btree.nd
  Btree.lf 1221952781511 Btree.lf ) 1242837012813 Btree.lf ) 1253203311448 (Btree.nd (Btree.nd
  Btree.lf 1268531975799 Btree.lf ) 1273633760443 Btree.lf )) 1352015391452 (Btree.nd (Btree.nd
  (Btree.nd Btree.lf 1353389403014 Btree.lf ) 1354086085242 Btree.lf ) 1355175405496 (Btree.nd
  (Btree.nd Btree.lf 1493480863270 Btree.lf ) 1509969002014 Btree.lf )))) 1518329188750 (Btree.nd
  (Btree.nd (Btree.nd (Btree.nd (Btree.nd Btree.lf 1531401031798 Btree.lf ) 1550682112881
  (Btree.nd Btree.lf 1575261100204 Btree.lf )) 1586111571627 (Btree.nd (Btree.nd Btree.lf
  1593190791918 Btree.lf ) 1675077696501 Btree.lf )) 1678829626914 (Btree.nd (Btree.nd (Btree.nd
  Btree.lf 1693074035477 Btree.lf ) 1708213886720 Btree.lf ) 1738970118116 (Btree.nd (Btree.nd
  Btree.lf 1751805373769 Btree.lf ) 1762793043121 Btree.lf ))) 1779018372219 (Btree.nd (Btree.nd
  (Btree.nd (Btree.nd Btree.lf 1802067860131 Btree.lf ) 1814381956134 Btree.lf ) 1827165062547
  (Btree.nd (Btree.nd Btree.lf 1834650848305 Btree.lf ) 1859021668713 Btree.lf )) 1874750486323
  (Btree.nd (Btree.nd (Btree.nd Btree.lf 1880449502833 Btree.lf ) 1883495403548 Btree.lf )
  1920243084441 (Btree.nd (Btree.nd Btree.lf 1937430852412 Btree.lf ) 1952503014385 Btree.lf ))))))
  1964956758809 (Btree.nd (Btree.nd (Btree.nd (Btree.nd (Btree.nd (Btree.nd (Btree.nd Btree.lf
  2006298522943 Btree.lf ) 2011492515978 (Btree.nd Btree.lf 2016748786096 Btree.lf )) 2022105411557
  (Btree.nd (Btree.nd Btree.lf 2095107493160 Btree.lf ) 2095310873623 Btree.lf )) 2097070623879
  (Btree.nd (Btree.nd (Btree.nd Btree.lf 2097655505176 Btree.lf ) 2237494004614 Btree.lf )
  2239934570170 (Btree.nd (Btree.nd Btree.lf 2261051573242 Btree.lf ) 2268070148806 Btree.lf )))
  2301499049168 (Btree.nd (Btree.nd (Btree.nd (Btree.nd Btree.lf 2314186079887 Btree.lf )
  2329547411642 Btree.lf ) 2336277447196 (Btree.nd (Btree.nd Btree.lf 2359975626833 Btree.lf )
  2374110051654 Btree.lf )) 2381300612152 (Btree.nd (Btree.nd (Btree.nd Btree.lf 2386140788449
  Btree.lf ) 2502931891207 Btree.lf ) 2507752264820 (Btree.nd (Btree.nd Btree.lf 2513998694669
  Btree.lf ) 2521879203690 Btree.lf )))) 2539128155289 (Btree.nd (Btree.nd (Btree.nd (Btree.nd
  (Btree.nd Btree.lf 2552233514908 Btree.lf ) 2571320089327 (Btree.nd Btree.lf 2583998453377
  Btree.lf )) 2601456071709 (Btree.nd (Btree.nd Btree.lf 2607870897907 Btree.lf ) 2624495259518
  Btree.lf )) 2645850726893 (Btree.nd (Btree.nd (Btree.nd Btree.lf 2664531313125 Btree.lf )
  2675276480646 Btree.lf ) 2684320694209 (Btree.nd (Btree.nd Btree.lf 2688618208496 Btree.lf )
  2728810818657 Btree.lf ))) 2733911729824 (Btree.nd (Btree.nd (Btree.nd (Btree.nd Btree.lf
  2754700916594 Btree.lf ) 2765105909742 Btree.lf ) 2838063141584 (Btree.nd (Btree.nd Btree.lf
  2839651560086 Btree.lf ) 2840554676069 Btree.lf )) 2841182810785 (Btree.nd (Btree.nd (Btree.nd
  Btree.lf 2979869689126 Btree.lf ) 2998930711150 Btree.lf ) 3009768102946 (Btree.nd (Btree.nd
  Btree.lf 3017305719538 Btree.lf ) 3036183607281 Btree.lf ))))) 3045741496974 (Btree.nd (Btree.nd
  (Btree.nd (Btree.nd (Btree.nd (Btree.nd Btree.lf 3050306819263 Btree.lf ) 3059865696800
  (Btree.nd Btree.lf 3097394541285 Btree.lf )) 3124969094379 (Btree.nd (Btree.nd Btree.lf
  3127284733639 Btree.lf ) 3141206388001 Btree.lf )) 3166258550510 (Btree.nd (Btree.nd (Btree.nd
  Btree.lf 3170493174673 Btree.lf ) 3188807707052 Btree.lf ) 3203005812402 (Btree.nd (Btree.nd
  Btree.lf 3294582192231 Btree.lf ) 3297338269808 Btree.lf ))) 3318502919138 (Btree.nd (Btree.nd
  (Btree.nd (Btree.nd Btree.lf 3326777072971 Btree.lf ) 3346864782525 Btree.lf ) 3348908441252
  (Btree.nd (Btree.nd Btree.lf 3354424807349 Btree.lf ) 3380868918207 Btree.lf )) 3412269290705
  (Btree.nd (Btree.nd (Btree.nd Btree.lf 3423897211537 Btree.lf ) 3432044705430 Btree.lf )
  3438951033771 (Btree.nd (Btree.nd Btree.lf 3471724700301 Btree.lf ) 3487226448893 Btree.lf ))))
  3502838900198 (Btree.nd (Btree.nd (Btree.nd (Btree.nd (Btree.nd Btree.lf 3508120118305 Btree.lf )
  3581792557145 Btree.lf ) 3583042681471 (Btree.nd (Btree.nd Btree.lf 3583599326846 Btree.lf )
  3584185074030 Btree.lf )) 3731530370194 (Btree.nd (Btree.nd (Btree.nd Btree.lf 3746531862106
  Btree.lf ) 3753211606606 Btree.lf ) 3760240572814 (Btree.nd (Btree.nd Btree.lf 3778057881345
  Btree.lf ) 3800903762139 Btree.lf ))) 3809380942202 (Btree.nd (Btree.nd (Btree.nd (Btree.nd
  Btree.lf 3822119043391 Btree.lf ) 3846642948115 Btree.lf ) 3859629122096 (Btree.nd (Btree.nd
  Btree.lf 3876622296481 Btree.lf ) 3884263293064 Btree.lf )) 3912839341279 (Btree.nd (Btree.nd
  (Btree.nd Btree.lf 3924075618518 Btree.lf ) 3935078783020 Btree.lf ) 3938097634614 (Btree.nd
  (Btree.nd Btree.lf 3964078864449 Btree.lf ) 3971170565538 Btree.lf ))))))) 3978859485986
  (Btree.nd (Btree.nd (Btree.nd (Btree.nd (Btree.nd (Btree.nd (Btree.nd (Btree.nd Btree.lf
  3999164172080 Btree.lf ) 4093566016430 (Btree.nd Btree.lf 4096934098796 Btree.lf )) 4105354560769
  (Btree.nd (Btree.nd Btree.lf 4131798399267 Btree.lf ) 4151428280109 Btree.lf )) 4154853171568
  (Btree.nd (Btree.nd (Btree.nd Btree.lf 4159586070387 Btree.lf ) 4179810038888 Btree.lf )
  4214802897393 (Btree.nd (Btree.nd Btree.lf 4225146357498 Btree.lf ) 4230168671575 Btree.lf )))
  4235403262321 (Btree.nd (Btree.nd (Btree.nd (Btree.nd Btree.lf 4324436203494 Btree.lf )
  4325230435768 Btree.lf ) 4325854661425 (Btree.nd (Btree.nd Btree.lf 4326645922731 Btree.lf )
  4470159311662 Btree.lf )) 4479690098950 (Btree.nd (Btree.nd (Btree.nd Btree.lf 4487180806834
  Btree.lf ) 4496675942506 Btree.lf ) 4521901431729 (Btree.nd (Btree.nd Btree.lf 4538777416250
  Btree.lf ) 4542001365869 Btree.lf )))) 4556442180224 (Btree.nd (Btree.nd (Btree.nd (Btree.nd
  (Btree.nd Btree.lf 4597540877732 Btree.lf ) 4609439035531 (Btree.nd Btree.lf 4618789829379
  Btree.lf )) 4627101778937 (Btree.nd (Btree.nd Btree.lf 4646022952989 Btree.lf ) 4649856023923
  Btree.lf )) 4654335663560 (Btree.nd (Btree.nd (Btree.nd Btree.lf 4670137967572 Btree.lf )
  4706290721913 Btree.lf ) 4719368824313 (Btree.nd (Btree.nd Btree.lf 4723455654577 Btree.lf )
  4750901567599 Btree.lf ))) 4769105810865 (Btree.nd (Btree.nd (Btree.nd (Btree.nd Btree.lf
  4774623917151 Btree.lf ) 4804973294440 Btree.lf ) 4812927985778 (Btree.nd (Btree.nd Btree.lf
  4897023285572 Btree.lf ) 4903473557521 Btree.lf )) 4914654146534 (Btree.nd (Btree.nd (Btree.nd
  Btree.lf 4937011268464 Btree.lf ) 4963025057441 Btree.lf ) 4973237487592 (Btree.nd (Btree.nd
  Btree.lf 4978542009771 Btree.lf ) 4983630491521 Btree.lf ))))) 5067511360802 (Btree.nd (Btree.nd
  (Btree.nd (Btree.nd (Btree.nd (Btree.nd Btree.lf 5067978086017 Btree.lf ) 5068227629575
  (Btree.nd Btree.lf 5070233968767 Btree.lf )) 5213936275966 (Btree.nd (Btree.nd Btree.lf
  5219536978546 Btree.lf ) 5222531501242 Btree.lf )) 5246607571546 (Btree.nd (Btree.nd (Btree.nd
  Btree.lf 5275418732045 Btree.lf ) 5286161320110 Btree.lf ) 5291775097466 (Btree.nd (Btree.nd
  Btree.lf 5295216384700 Btree.lf ) 5327442428913 Btree.lf ))) 5330457322388 (Btree.nd (Btree.nd
  (Btree.nd (Btree.nd Btree.lf 5341213235908 Btree.lf ) 5352378595542 Btree.lf ) 5394968911552
  (Btree.nd (Btree.nd Btree.lf 5407860585776 Btree.lf ) 5413878028801 Btree.lf )) 5432355960845
  (Btree.nd (Btree.nd (Btree.nd Btree.lf 5449991590725 Btree.lf ) 5456440061391 Btree.lf )
  5481397924013 (Btree.nd (Btree.nd Btree.lf 5494286911718 Btree.lf ) 5513645856873 Btree.lf ))))
  5528247476257 (Btree.nd (Btree.nd (Btree.nd (Btree.nd (Btree.nd Btree.lf 5532974307146 Btree.lf )
  5542027653932 Btree.lf ) 5574707637873 (Btree.nd (Btree.nd Btree.lf 5584596559696 Btree.lf )
  5599217954979 Btree.lf )) 5618135970865 (Btree.nd (Btree.nd (Btree.nd Btree.lf 5706264079406
  Btree.lf ) 5711427481155 Btree.lf ) 5716571123010 (Btree.nd (Btree.nd Btree.lf 5732077598929
  Btree.lf ) 5810313117092 Btree.lf ))) 5810748880277 (Btree.nd (Btree.nd (Btree.nd (Btree.nd
  Btree.lf 5811170875851 Btree.lf ) 5812027419066 Btree.lf ) 5954071123990 (Btree.nd (Btree.nd
  Btree.lf 5959300282210 Btree.lf ) 5964364229098 Btree.lf )) 5974642747678 (Btree.nd (Btree.nd
  (Btree.nd Btree.lf 6026342930333 Btree.lf ) 6036527341999 Btree.lf ) 6041772448107 (Btree.nd
  (Btree.nd Btree.lf 6047155644750 Btree.lf ) 6072824465037 Btree.lf )))))) 6077951169807
  (Btree.nd (Btree.nd (Btree.nd (Btree.nd (Btree.nd (Btree.nd (Btree.nd Btree.lf 6103724578325
  Btree.lf ) 6109081660000 (Btree.nd Btree.lf 6134785286025 Btree.lf )) 6155194403875 (Btree.nd
  (Btree.nd Btree.lf 6160496473802 Btree.lf ) 6165715372993 Btree.lf )) 6196508988285 (Btree.nd
  (Btree.nd (Btree.nd Btree.lf 6207022132047 Btree.lf ) 6222375077358 Btree.lf ) 6232923803953
  (Btree.nd (Btree.nd Btree.lf 6263781750688 Btree.lf ) 6268858076305 Btree.lf ))) 6279097048026
  (Btree.nd (Btree.nd (Btree.nd (Btree.nd Btree.lf 6289407530582 Btree.lf ) 6330651147271 Btree.lf
  ) 6335991066988 (Btree.nd (Btree.nd Btree.lf 6341006447655 Btree.lf ) 6356772858854 Btree.lf ))
  6382586699313 (Btree.nd (Btree.nd (Btree.nd Btree.lf 6387737209458 Btree.lf ) 6398068305662
  Btree.lf ) 6403218929789 (Btree.nd (Btree.nd Btree.lf 6557667337903 Btree.lf ) 6557726251516
  Btree.lf )))) 6557770919953 (Btree.nd (Btree.nd (Btree.nd (Btree.nd (Btree.nd Btree.lf
  6557886782249 Btree.lf ) 6744499897498 (Btree.nd Btree.lf 6745206860854 Btree.lf )) 6745742882098
  (Btree.nd (Btree.nd Btree.lf 6747133229650 Btree.lf ) 6805910183600 Btree.lf )) 6806729824829
  (Btree.nd (Btree.nd (Btree.nd Btree.lf 6808535005371 Btree.lf ) 6809056277452 Btree.lf )
  6867716305340 (Btree.nd (Btree.nd Btree.lf 6869511673057 Btree.lf ) 6870055462611 Btree.lf )))
  6870964494306 (Btree.nd (Btree.nd (Btree.nd (Btree.nd Btree.lf 6930027578551 Btree.lf )
  6931880401710 Btree.lf ) 6932261571697 (Btree.nd (Btree.nd Btree.lf 6932887549973 Btree.lf )
  6991689459788 Btree.lf )) 6993028934353 (Btree.nd (Btree.nd (Btree.nd Btree.lf 6993764977034
  Btree.lf ) 6994106615155 Btree.lf ) 7053496949312 (Btree.nd (Btree.nd Btree.lf 7053965691652
  Btree.lf ) 7054291183159 Btree.lf ))))) 7054748062362 (Btree.nd (Btree.nd (Btree.nd (Btree.nd
  (Btree.nd (Btree.nd Btree.lf 7115977917026 Btree.lf ) 7116371157313 (Btree.nd Btree.lf
  7117122893705 Btree.lf )) 7117590530776 (Btree.nd (Btree.nd Btree.lf 7178473853034 Btree.lf )
  7178919190322 Btree.lf )) 7179336364827 (Btree.nd (Btree.nd (Btree.nd Btree.lf 7180217321068
  Btree.lf ) 7243488117547 Btree.lf ) 7243517550038 (Btree.nd (Btree.nd Btree.lf 7243621344927
  Btree.lf ) 7243707612845 Btree.lf ))) 8111841385065 (Btree.nd (Btree.nd (Btree.nd (Btree.nd
  Btree.lf 8112194574957 Btree.lf ) 8113440113625 Btree.lf ) 8114475328641 (Btree.nd (Btree.nd
  Btree.lf 8117387427567 Btree.lf ) 8117697216354 Btree.lf )) 8118722354798 (Btree.nd (Btree.nd
  (Btree.nd Btree.lf 8119045821425 Btree.lf ) 8122114126324 Btree.lf ) 8123322124434 (Btree.nd
  (Btree.nd Btree.lf 8124099154171 Btree.lf ) 8124807293713 Btree.lf )))) 8126706366812 (Btree.nd
  (Btree.nd (Btree.nd (Btree.nd (Btree.nd Btree.lf 8127228022518 Btree.lf ) 8128558049546 Btree.lf
  ) 8128818037615 (Btree.nd (Btree.nd Btree.lf 8132050414268 Btree.lf ) 8132710572954 Btree.lf ))
  8133290853985 (Btree.nd (Btree.nd (Btree.nd Btree.lf 8135119516205 Btree.lf ) 8137056508328
  Btree.lf ) 8137838874319 (Btree.nd (Btree.nd Btree.lf 8138931840171 Btree.lf ) 8139723108913
  Btree.lf ))) 8143450519171 (Btree.nd (Btree.nd (Btree.nd (Btree.nd Btree.lf 8143952028377
  Btree.lf ) 8144348004232 Btree.lf ) 8145457314819 (Btree.nd (Btree.nd Btree.lf 8147627983220
  Btree.lf ) 8148051685829 Btree.lf )) 8148922044076 (Btree.nd (Btree.nd (Btree.nd Btree.lf
  8150220216050 Btree.lf ) 8156365695159 Btree.lf ) 8156407279537 (Btree.nd (Btree.nd Btree.lf
  8156433783388 Btree.lf ) 8156475481022 Btree.lf ))))))))

lemma TX_closed : ConjClosed TX := by decide +kernel

lemma TX_mem_x0 : TX.mem (φ12 x0) = true := by rw [x0_code]; decide +kernel

/-! ### Order three with a fixed point, in codes

`3A` and `3B` are the two classes of elements of order `3` in `M₁₂`.  They are told apart by
their cycle types, `3³1³` against `3⁴`: an element of `3A` fixes a point and an element of `3B`
does not.  Both tests are conjugation-invariant, and only the easy implication is needed below,
namely that a conjugate of `y` passes them. -/

/-- The fixed-point test on a code: some base-`12` digit equals its index. -/
def hasFix (n : ℕ) : Bool := (List.range 12).any (fun i => dg12 n i == i)

/-- The membership test for `3A` on a code: the cube is the identity and there is a fixed
point. -/
def testY (q : ℕ) : Bool := (mulC12 (mulC12 q q) q == idCode12) && hasFix q

/-- The keys of the involution tree whose product with `z⁻¹` passes the `3A` test: an
over-approximation of the structure-constant fibre. -/
noncomputable def fibreList : List ℕ := TX.toList.filter (fun k => testY (mulC12 k cAi))

lemma fibreList_length : fibreList.length = 11 := by decide +kernel

/-! ### The structure constant -/

/-- Every element of the class of `x` squares to one. -/
lemma sq_eq_one_of_conj {w : ↥M12} (hw : ConjClasses.mk w = ConjClasses.mk xEl) : w⁻¹ = w := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hw)
  have h1 : c * (w * w) * c⁻¹ = 1 := by
    rw [show c * (w * w) * c⁻¹ = (c * w * c⁻¹) * (c * w * c⁻¹) by group, hc, xEl_sq]
  have h2 : w * w = c⁻¹ * (c * (w * w) * c⁻¹) * c := by group
  rw [h1] at h2
  simp only [mul_one, inv_mul_cancel] at h2
  exact inv_eq_of_mul_eq_one_right h2

/-- The cube of `y` is the identity. -/
lemma y0_pow_three :
    ((x0⁻¹ * m12a⁻¹) * (x0⁻¹ * m12a⁻¹)) * (x0⁻¹ * m12a⁻¹) = 1 := by decide

/-- `y` fixes the point `1`. -/
lemma y0_fix : (x0⁻¹ * m12a⁻¹) (1 : Fin 12) = 1 := by decide

/-- Every element of the class of `y` passes the `3A` test on codes. -/
lemma testY_of_conj {u : ↥M12} (hu : ConjClasses.mk u = ConjClasses.mk yEl) :
    testY (φ12 ((u : Perm (Fin 12)))) = true := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hu)
  set p : Perm (Fin 12) := (u : Perm (Fin 12)) with hp
  set d : Perm (Fin 12) := (c : Perm (Fin 12)) with hd
  have hcp : d * p * d⁻¹ = x0⁻¹ * m12a⁻¹ := congrArg Subtype.val hc
  have hpd : p = d⁻¹ * (x0⁻¹ * m12a⁻¹) * d := by rw [← hcp]; group
  have hp3 : (p * p) * p = 1 := by
    rw [hpd]
    calc d⁻¹ * (x0⁻¹ * m12a⁻¹) * d * (d⁻¹ * (x0⁻¹ * m12a⁻¹) * d) *
          (d⁻¹ * (x0⁻¹ * m12a⁻¹) * d)
        = d⁻¹ * (((x0⁻¹ * m12a⁻¹) * (x0⁻¹ * m12a⁻¹)) * (x0⁻¹ * m12a⁻¹)) * d := by group
      _ = 1 := by rw [y0_pow_three]; group
  have hdi : d (d⁻¹ (1 : Fin 12)) = 1 := by
    have h := Equiv.Perm.mul_apply d d⁻¹ (1 : Fin 12)
    rw [mul_inv_cancel, Equiv.Perm.one_apply] at h
    exact h.symm
  have hfix : p (d⁻¹ (1 : Fin 12)) = d⁻¹ (1 : Fin 12) := by
    have hstep : (d⁻¹ * (x0⁻¹ * m12a⁻¹) * d) (d⁻¹ (1 : Fin 12)) = d⁻¹ (1 : Fin 12) := by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hdi, y0_fix]
    rw [hpd]; exact hstep
  have hmul : mulC12 (φ12 p) (φ12 p) = φ12 (p * p) := mulC12_φ12 p p
  have hmul2 : mulC12 (φ12 (p * p)) (φ12 p) = φ12 ((p * p) * p) := mulC12_φ12 _ _
  have hcube : mulC12 (mulC12 (φ12 p) (φ12 p)) (φ12 p) = idCode12 := by
    rw [hmul, hmul2, hp3, φ12_one]
  have hhf : hasFix (φ12 p) = true := by
    unfold hasFix
    rw [List.any_eq_true]
    refine ⟨(d⁻¹ (1 : Fin 12)).val, List.mem_range.mpr (d⁻¹ (1 : Fin 12)).isLt, ?_⟩
    simp only [beq_iff_eq]
    rw [← dg12_φ12 p (d⁻¹ (1 : Fin 12)), hfix]
  unfold testY
  rw [hcube, hhf, beq_self_eq_true, Bool.and_true]

theorem card_prodOneFibre_le :
    Nat.card (prodOneFibre (classTriple 0) (classTriple 1) zEl) ≤ 11 := by
  classical
  have hmap : ∀ w : ↥(prodOneFibre (classTriple 0) (classTriple 1) zEl),
      φ12 (((w : ↥M12) : Perm (Fin 12))) ∈ fibreList := by
    rintro ⟨w, hw0, hw1⟩
    rw [classTriple_zero] at hw0
    rw [classTriple_one] at hw1
    have hinv : w⁻¹ = w := sq_eq_one_of_conj hw0
    have hX : TX.mem (φ12 ((w : Perm (Fin 12)))) = true :=
      key_of_conjClass TX_closed TX_mem_x0 (u := xEl) rfl hw0
    have hY : testY (φ12 (((w⁻¹ * zEl⁻¹ : ↥M12) : Perm (Fin 12)))) = true := testY_of_conj hw1
    have hcoe : (((w⁻¹ * zEl⁻¹ : ↥M12) : Perm (Fin 12)))
        = ((w : Perm (Fin 12)))⁻¹ * m12a⁻¹ := rfl
    rw [hcoe, show ((w : Perm (Fin 12)))⁻¹ = (w : Perm (Fin 12)) from congrArg Subtype.val hinv]
      at hY
    have hmul : mulC12 (φ12 ((w : Perm (Fin 12)))) cAi = φ12 ((w : Perm (Fin 12)) * m12a⁻¹) := by
      rw [← cAi_eq, mulC12_φ12]
    refine List.mem_filter.mpr ⟨Btree.mem_toList hX, ?_⟩
    rw [hmul]
    exact hY
  let f : ↥(prodOneFibre (classTriple 0) (classTriple 1) zEl) → ↥fibreList.toFinset :=
    fun w => ⟨φ12 (((w : ↥M12) : Perm (Fin 12))), List.mem_toFinset.mpr (hmap w)⟩
  have hf : Function.Injective f := by
    intro u v huv
    have h1 : φ12 (((u : ↥M12) : Perm (Fin 12))) = φ12 (((v : ↥M12) : Perm (Fin 12))) :=
      congrArg Subtype.val huv
    exact Subtype.ext (Subtype.ext (φ12_injective h1))
  calc Nat.card ↥(prodOneFibre (classTriple 0) (classTriple 1) zEl)
      ≤ Nat.card ↥fibreList.toFinset := Nat.card_le_card_of_injective f hf
    _ = fibreList.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ fibreList.length := List.toFinset_card_le _
    _ = 11 := fibreList_length

/-! ### The centralizer of the `11`-cycle -/

theorem eleven_le_centralizer :
    11 ≤ Nat.card ↥(Subgroup.centralizer ({zEl} : Set ↥M12)) := by
  have hz11 : zEl ^ 11 = 1 := by
    apply Subtype.ext
    show m12a ^ 11 = 1
    exact m12a_pow_eq_one
  have hzne : zEl ≠ 1 := fun h => m12a_ne_one (congrArg Subtype.val h)
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have horder : orderOf zEl = 11 := orderOf_eq_prime hz11 hzne
  have hle : Subgroup.zpowers zEl ≤ Subgroup.centralizer ({zEl} : Set ↥M12) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.mpr (by rintro m rfl; rfl)
  have hcard : Nat.card ↥(Subgroup.zpowers zEl)
      ≤ Nat.card ↥(Subgroup.centralizer ({zEl} : Set ↥M12)) :=
    Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle)
  rwa [Nat.card_zpowers, horder] at hcard

/-! ### Rigidity -/

theorem xEl_mem_prodOneFibre :
    xEl ∈ prodOneFibre (classTriple 0) (classTriple 1) zEl := ⟨rfl, rfl⟩

/-- **The class triple `(2A, 3A, 11A)` is rigid in `M₁₂`.**  The product-one triples with entries
in these three classes form a single orbit under simultaneous conjugation, of full size
`|M₁₂| = 95040`, and every one of them generates. -/
theorem rigid_triple : Nat.card ↥(rigidTuples classTriple) = Nat.card ↥M12 :=
  rigid_of_card_prodOneFibre center_eq_bot gen_top xEl_mem_prodOneFibre classTriple_two
    (le_trans card_prodOneFibre_le eleven_le_centralizer)

/-! ### The mirror triple `(2A, 3A, 11B)`

Inversion does not preserve the class of the `11`-cycle: `z` and `z⁻¹` lie in the two distinct
classes `11A` and `11B`, which the cyclotomic action interchanges.  Everything above therefore has
a mirror image, obtained by replacing `z` by `z⁻¹`; both triples are needed below, because the
cyclotomic orbit of `(2A, 3A, 11A)` consists of exactly these two triples. -/

/-- The remaining entry of the mirror triple, forced by the product-one relation. -/
def yEl' : ↥M12 := xEl⁻¹ * zEl

/-- The triple of conjugacy classes `(2A, 3A, 11B)` of `M₁₂`. -/
def classTriple' : Fin 3 → ConjClasses ↥M12 :=
  ![ConjClasses.mk xEl, ConjClasses.mk yEl', ConjClasses.mk zEl⁻¹]

lemma classTriple'_zero : classTriple' 0 = ConjClasses.mk xEl := rfl
lemma classTriple'_one : classTriple' 1 = ConjClasses.mk yEl' := rfl
lemma classTriple'_two : classTriple' 2 = ConjClasses.mk zEl⁻¹ := rfl

theorem gen_top' : Subgroup.closure ({xEl, zEl⁻¹} : Set ↥M12) = ⊤ := by
  have hxK : xEl ∈ Subgroup.closure ({xEl, zEl⁻¹} : Set ↥M12) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hiK : zEl⁻¹ ∈ Subgroup.closure ({xEl, zEl⁻¹} : Set ↥M12) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hzK : zEl ∈ Subgroup.closure ({xEl, zEl⁻¹} : Set ↥M12) := by
    simpa using inv_mem hiK
  refine eq_top_of_gens_mem _ hzK ?_ ?_
  · have hval : (⟨m12b, m12b_mem⟩ : ↥M12) =
        zEl⁻¹ * zEl⁻¹ * zEl⁻¹ * zEl⁻¹ * zEl⁻¹ * xEl * zEl * zEl * xEl * zEl⁻¹ * zEl⁻¹ * xEl *
          zEl * xEl * zEl⁻¹ := by
      apply Subtype.ext
      show m12b = m12a⁻¹ * m12a⁻¹ * m12a⁻¹ * m12a⁻¹ * m12a⁻¹ * x0 * m12a * m12a * x0 * m12a⁻¹ *
        m12a⁻¹ * x0 * m12a * x0 * m12a⁻¹
      decide
    rw [hval]
    exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
      (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem hiK hiK) hiK) hiK) hiK) hxK) hzK) hzK) hxK)
      hiK) hiK) hxK) hzK) hxK) hiK
  · have hval : (⟨m12c, m12c_mem⟩ : ↥M12) =
        xEl * zEl * zEl * zEl * zEl * xEl * zEl⁻¹ * zEl⁻¹ * zEl⁻¹ * zEl⁻¹ * xEl := by
      apply Subtype.ext
      show m12c = x0 * m12a * m12a * m12a * m12a * x0 * m12a⁻¹ * m12a⁻¹ * m12a⁻¹ * m12a⁻¹ * x0
      decide
    rw [hval]
    exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
      (mul_mem hxK hzK) hzK) hzK) hzK) hxK) hiK) hiK) hiK) hiK) hxK

/-- The keys of the involution tree whose product with `z` passes the `3A` test: an
over-approximation of the mirror structure-constant fibre. -/
noncomputable def fibreList' : List ℕ := TX.toList.filter (fun k => testY (mulC12 k cA))

lemma fibreList'_length : fibreList'.length = 11 := by decide +kernel

/-- The cube of the mirror entry is the identity. -/
lemma y0'_pow_three :
    ((x0⁻¹ * m12a) * (x0⁻¹ * m12a)) * (x0⁻¹ * m12a) = 1 := by decide

/-- The mirror entry fixes the point `0`. -/
lemma y0'_fix : (x0⁻¹ * m12a) (0 : Fin 12) = 0 := by decide

/-- Every element of the class of the mirror entry passes the `3A` test on codes. -/
lemma testY_of_conj' {u : ↥M12} (hu : ConjClasses.mk u = ConjClasses.mk yEl') :
    testY (φ12 ((u : Perm (Fin 12)))) = true := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hu)
  set p : Perm (Fin 12) := (u : Perm (Fin 12)) with hp
  set d : Perm (Fin 12) := (c : Perm (Fin 12)) with hd
  have hcp : d * p * d⁻¹ = x0⁻¹ * m12a := congrArg Subtype.val hc
  have hpd : p = d⁻¹ * (x0⁻¹ * m12a) * d := by rw [← hcp]; group
  have hp3 : (p * p) * p = 1 := by
    rw [hpd]
    calc d⁻¹ * (x0⁻¹ * m12a) * d * (d⁻¹ * (x0⁻¹ * m12a) * d) * (d⁻¹ * (x0⁻¹ * m12a) * d)
        = d⁻¹ * (((x0⁻¹ * m12a) * (x0⁻¹ * m12a)) * (x0⁻¹ * m12a)) * d := by group
      _ = 1 := by rw [y0'_pow_three]; group
  have hdi : d (d⁻¹ (0 : Fin 12)) = 0 := by
    have h := Equiv.Perm.mul_apply d d⁻¹ (0 : Fin 12)
    rw [mul_inv_cancel, Equiv.Perm.one_apply] at h
    exact h.symm
  have hfix : p (d⁻¹ (0 : Fin 12)) = d⁻¹ (0 : Fin 12) := by
    have hstep : (d⁻¹ * (x0⁻¹ * m12a) * d) (d⁻¹ (0 : Fin 12)) = d⁻¹ (0 : Fin 12) := by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hdi, y0'_fix]
    rw [hpd]; exact hstep
  have hmul : mulC12 (φ12 p) (φ12 p) = φ12 (p * p) := mulC12_φ12 p p
  have hmul2 : mulC12 (φ12 (p * p)) (φ12 p) = φ12 ((p * p) * p) := mulC12_φ12 _ _
  have hcube : mulC12 (mulC12 (φ12 p) (φ12 p)) (φ12 p) = idCode12 := by
    rw [hmul, hmul2, hp3, φ12_one]
  have hhf : hasFix (φ12 p) = true := by
    unfold hasFix
    rw [List.any_eq_true]
    refine ⟨(d⁻¹ (0 : Fin 12)).val, List.mem_range.mpr (d⁻¹ (0 : Fin 12)).isLt, ?_⟩
    simp only [beq_iff_eq]
    rw [← dg12_φ12 p (d⁻¹ (0 : Fin 12)), hfix]
  unfold testY
  rw [hcube, hhf, beq_self_eq_true, Bool.and_true]

theorem card_prodOneFibre_le' :
    Nat.card (prodOneFibre (classTriple' 0) (classTriple' 1) zEl⁻¹) ≤ 11 := by
  classical
  have hmap : ∀ w : ↥(prodOneFibre (classTriple' 0) (classTriple' 1) zEl⁻¹),
      φ12 (((w : ↥M12) : Perm (Fin 12))) ∈ fibreList' := by
    rintro ⟨w, hw0, hw1⟩
    rw [classTriple'_zero] at hw0
    rw [classTriple'_one] at hw1
    have hinv : w⁻¹ = w := sq_eq_one_of_conj hw0
    have hX : TX.mem (φ12 ((w : Perm (Fin 12)))) = true :=
      key_of_conjClass TX_closed TX_mem_x0 (u := xEl) rfl hw0
    have hY : testY (φ12 (((w⁻¹ * zEl⁻¹⁻¹ : ↥M12) : Perm (Fin 12)))) = true := testY_of_conj' hw1
    have hcoe : (((w⁻¹ * zEl⁻¹⁻¹ : ↥M12) : Perm (Fin 12)))
        = ((w : Perm (Fin 12)))⁻¹ * m12a⁻¹⁻¹ := rfl
    rw [hcoe, show ((w : Perm (Fin 12)))⁻¹ = (w : Perm (Fin 12)) from congrArg Subtype.val hinv,
      inv_inv] at hY
    have hmul : mulC12 (φ12 ((w : Perm (Fin 12)))) cA = φ12 ((w : Perm (Fin 12)) * m12a) := by
      rw [← cA_eq, mulC12_φ12]
    refine List.mem_filter.mpr ⟨Btree.mem_toList hX, ?_⟩
    rw [hmul]
    exact hY
  let f : ↥(prodOneFibre (classTriple' 0) (classTriple' 1) zEl⁻¹) → ↥fibreList'.toFinset :=
    fun w => ⟨φ12 (((w : ↥M12) : Perm (Fin 12))), List.mem_toFinset.mpr (hmap w)⟩
  have hf : Function.Injective f := by
    intro u v huv
    have h1 : φ12 (((u : ↥M12) : Perm (Fin 12))) = φ12 (((v : ↥M12) : Perm (Fin 12))) :=
      congrArg Subtype.val huv
    exact Subtype.ext (Subtype.ext (φ12_injective h1))
  calc Nat.card ↥(prodOneFibre (classTriple' 0) (classTriple' 1) zEl⁻¹)
      ≤ Nat.card ↥fibreList'.toFinset := Nat.card_le_card_of_injective f hf
    _ = fibreList'.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ fibreList'.length := List.toFinset_card_le _
    _ = 11 := fibreList'_length

/-- The `11`-cycle has order dividing eleven. -/
lemma zEl_pow_eleven : zEl ^ 11 = 1 := by
  apply Subtype.ext
  show m12a ^ 11 = 1
  exact m12a_pow_eq_one

theorem eleven_le_centralizer' :
    11 ≤ Nat.card ↥(Subgroup.centralizer ({zEl⁻¹} : Set ↥M12)) := by
  have hz11 : zEl⁻¹ ^ 11 = 1 := by rw [inv_pow, zEl_pow_eleven, inv_one]
  have hzne : zEl⁻¹ ≠ 1 := fun h =>
    m12a_ne_one (congrArg Subtype.val (inv_eq_one.mp h))
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have horder : orderOf zEl⁻¹ = 11 := orderOf_eq_prime hz11 hzne
  have hle : Subgroup.zpowers zEl⁻¹ ≤ Subgroup.centralizer ({zEl⁻¹} : Set ↥M12) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.mpr (by rintro m rfl; rfl)
  have hcard : Nat.card ↥(Subgroup.zpowers zEl⁻¹)
      ≤ Nat.card ↥(Subgroup.centralizer ({zEl⁻¹} : Set ↥M12)) :=
    Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle)
  rwa [Nat.card_zpowers, horder] at hcard

theorem xEl_mem_prodOneFibre' :
    xEl ∈ prodOneFibre (classTriple' 0) (classTriple' 1) zEl⁻¹ := ⟨rfl, by rw [inv_inv]; rfl⟩

/-- **The class triple `(2A, 3A, 11B)` is rigid in `M₁₂`.** -/
theorem rigid_triple' : Nat.card ↥(rigidTuples classTriple') = Nat.card ↥M12 :=
  rigid_of_card_prodOneFibre center_eq_bot gen_top' xEl_mem_prodOneFibre' classTriple'_two
    (le_trans card_prodOneFibre_le' eleven_le_centralizer')

/-! ### The cyclotomic orbit of the triple

The exponents coprime to `66 = 2 · 3 · 11` act on the triple by raising each entry to that power.
The involution and the order-three entry are unmoved — `2A` and `3A` are rational classes of
`M₁₂` — while the `11`-cycle is carried to `z` or to `z⁻¹` according as the exponent is a
quadratic residue mod `11` or not.  Both possibilities are rigid, by `rigid_triple` and
`rigid_triple'`. -/

/-- A word in the standard generators conjugating the `11`-cycle to its cube. -/
def g0 : Perm (Fin 12) := m12c * m12b * m12c * m12b⁻¹

lemma g0_mem : g0 ∈ M12 :=
  mul_mem (mul_mem (mul_mem m12c_mem m12b_mem) m12c_mem) (inv_mem m12b_mem)

/-- The conjugator cubing the `11`-cycle, as an element of `M₁₂`. -/
def gEl : ↥M12 := ⟨g0, g0_mem⟩

/-- A word in the standard generators conjugating the order-three entry to its inverse. -/
def gy0 : Perm (Fin 12) := m12b * m12a * m12b⁻¹ * m12a * m12a * m12b⁻¹

lemma gy0_mem : gy0 ∈ M12 :=
  mul_mem (mul_mem (mul_mem (mul_mem (mul_mem m12b_mem m12a_mem) (inv_mem m12b_mem))
    m12a_mem) m12a_mem) (inv_mem m12b_mem)

/-- The conjugator inverting the order-three entry, as an element of `M₁₂`. -/
def gyEl : ↥M12 := ⟨gy0, gy0_mem⟩

/-- A word in the standard generators conjugating the mirror entry to the original one. -/
def gp0 : Perm (Fin 12) := m12a⁻¹ * m12b⁻¹ * m12a⁻¹ * m12c * m12a⁻¹ * m12b

lemma gp0_mem : gp0 ∈ M12 :=
  mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (inv_mem m12a_mem) (inv_mem m12b_mem))
    (inv_mem m12a_mem)) m12c_mem) (inv_mem m12a_mem)) m12b_mem

/-- The conjugator matching the two order-three entries, as an element of `M₁₂`. -/
def gpEl : ↥M12 := ⟨gp0, gp0_mem⟩

lemma conj_zEl_cube : gEl * zEl * gEl⁻¹ = zEl ^ 3 := by
  apply Subtype.ext
  show g0 * m12a * g0⁻¹ = m12a ^ 3
  decide

lemma conj_yEl_inv : gyEl * yEl * gyEl⁻¹ = yEl⁻¹ := by
  apply Subtype.ext
  show gy0 * (x0⁻¹ * m12a⁻¹) * gy0⁻¹ = (x0⁻¹ * m12a⁻¹)⁻¹
  decide

lemma conj_yEl' : gpEl * yEl' * gpEl⁻¹ = yEl := by
  apply Subtype.ext
  show gp0 * (x0⁻¹ * m12a) * gp0⁻¹ = x0⁻¹ * m12a⁻¹
  decide

/-- The two order-three entries are conjugate. -/
lemma mk_yEl'_eq : ConjClasses.mk yEl' = ConjClasses.mk yEl :=
  ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨gpEl, conj_yEl'⟩)

/-- An exponent may be reduced modulo any exponent of the element. -/
lemma pow_mod_of_pow_eq_one {g : ↥M12} {m : ℕ} (hm : g ^ m = 1) (u : ℕ) : g ^ u = g ^ (u % m) := by
  conv_lhs => rw [← Nat.div_add_mod u m]
  rw [pow_add, pow_mul, hm, one_pow, one_mul]

/-- The involution has order dividing two. -/
lemma xEl_pow_two : xEl ^ 2 = 1 := by rw [pow_two]; exact xEl_sq

/-- The order-three entry has order dividing three. -/
lemma yEl_pow_three : yEl ^ 3 = 1 := by
  have h : yEl * yEl * yEl = 1 := Subtype.ext y0_pow_three
  calc yEl ^ 3 = yEl * yEl * yEl := by
        rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two]
    _ = 1 := h

/-- The square of the order-three entry is its inverse, hence in its own class. -/
lemma mk_yEl_sq : ConjClasses.mk (yEl ^ 2) = ConjClasses.mk yEl := by
  have h2 : yEl ^ 2 = yEl⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    calc yEl ^ 2 * yEl = yEl ^ 3 := by group
      _ = 1 := yEl_pow_three
  rw [h2]
  exact (ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨gyEl, conj_yEl_inv⟩)).symm

/-- Conjugating by `g` triples the exponent of the `11`-cycle. -/
lemma mk_zEl_conj (k : ℕ) : ConjClasses.mk (zEl ^ (3 * k)) = ConjClasses.mk (zEl ^ k) := by
  refine (ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨gEl, ?_⟩)).symm
  have h : ∀ n : ℕ, gEl * zEl ^ n * gEl⁻¹ = (gEl * zEl * gEl⁻¹) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ m ih => rw [pow_succ, pow_succ, ← ih]; group
  rw [h k, conj_zEl_cube, ← pow_mul]

/-- The `11`-cycle may be reduced modulo eleven. -/
lemma zEl_pow_mod (u : ℕ) : zEl ^ u = zEl ^ (u % 11) := pow_mod_of_pow_eq_one zEl_pow_eleven u

/-- Tripling the exponent modulo eleven does not change the class of the power. -/
lemma mk_zEl_step {j k : ℕ} (h : j % 11 = (3 * k) % 11) :
    ConjClasses.mk (zEl ^ j) = ConjClasses.mk (zEl ^ k) := by
  rw [zEl_pow_mod j, h, ← zEl_pow_mod (3 * k)]
  exact mk_zEl_conj k

/-- The tenth power of the `11`-cycle is its inverse. -/
lemma zEl_pow_ten : zEl ^ 10 = zEl⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  calc zEl ^ 10 * zEl = zEl ^ 11 := by group
    _ = 1 := zEl_pow_eleven

/-- **Every power of the `11`-cycle by an exponent prime to eleven lies in one of the two
classes `11A`, `11B`.** -/
lemma mk_zEl_pow_cases {k : ℕ} (hk : ¬ (11 ∣ k)) :
    ConjClasses.mk (zEl ^ k) = ConjClasses.mk zEl ∨
      ConjClasses.mk (zEl ^ k) = ConjClasses.mk zEl⁻¹ := by
  have e1 : ConjClasses.mk (zEl ^ 1) = ConjClasses.mk zEl := by rw [pow_one]
  have e10 : ConjClasses.mk (zEl ^ 10) = ConjClasses.mk zEl⁻¹ := by rw [zEl_pow_ten]
  have e3 : ConjClasses.mk (zEl ^ 3) = ConjClasses.mk zEl :=
    (mk_zEl_step (j := 3) (k := 1) (by norm_num)).trans e1
  have e9 : ConjClasses.mk (zEl ^ 9) = ConjClasses.mk zEl :=
    (mk_zEl_step (j := 9) (k := 3) (by norm_num)).trans e3
  have e5 : ConjClasses.mk (zEl ^ 5) = ConjClasses.mk zEl :=
    (mk_zEl_step (j := 5) (k := 9) (by norm_num)).trans e9
  have e4 : ConjClasses.mk (zEl ^ 4) = ConjClasses.mk zEl :=
    (mk_zEl_step (j := 4) (k := 5) (by norm_num)).trans e5
  have e8 : ConjClasses.mk (zEl ^ 8) = ConjClasses.mk zEl⁻¹ :=
    (mk_zEl_step (j := 8) (k := 10) (by norm_num)).trans e10
  have e2 : ConjClasses.mk (zEl ^ 2) = ConjClasses.mk zEl⁻¹ :=
    (mk_zEl_step (j := 2) (k := 8) (by norm_num)).trans e8
  have e6 : ConjClasses.mk (zEl ^ 6) = ConjClasses.mk zEl⁻¹ :=
    (mk_zEl_step (j := 6) (k := 2) (by norm_num)).trans e2
  have e7 : ConjClasses.mk (zEl ^ 7) = ConjClasses.mk zEl⁻¹ :=
    (mk_zEl_step (j := 7) (k := 6) (by norm_num)).trans e6
  obtain ⟨j, hj1, hj2, hjk⟩ : ∃ j, 1 ≤ j ∧ j < 11 ∧ k % 11 = j :=
    ⟨k % 11, by omega, Nat.mod_lt _ (by norm_num), rfl⟩
  rw [zEl_pow_mod k, hjk]
  interval_cases j
  exacts [Or.inl e1, Or.inr e2, Or.inl e3, Or.inl e4, Or.inl e5, Or.inr e6, Or.inr e7,
    Or.inr e8, Or.inl e9, Or.inr e10]

/-- No prime dividing `66` divides an exponent prime to `66`. -/
lemma not_dvd_of_coprime {u p : ℕ} (hp : p.Prime) (hpd : p ∣ 66) (h : Nat.Coprime u 66) :
    ¬ p ∣ u :=
  hp.coprime_iff_not_dvd.mp (Nat.Coprime.coprime_dvd_right hpd h).symm

/-- **Every cyclotomic twist of the triple `(2A, 3A, 11A)` is rigid.**  The twist by an exponent
prime to `66` is either the triple itself or its mirror image. -/
theorem orbit_rigid (u : Fin 3 → ℕ) (hu : ∀ i, Nat.Coprime (u i) 66) :
    Nat.card ↥(rigidTuples fun i => ConjClasses.powClass (u i) (classTriple i))
      = Nat.card ↥M12 := by
  have hx : ConjClasses.powClass (u 0) (classTriple 0) = ConjClasses.mk xEl := by
    rw [classTriple_zero, ConjClasses.powClass_mk, pow_mod_of_pow_eq_one xEl_pow_two (u 0)]
    have h2 : ¬ (2 ∣ u 0) := not_dvd_of_coprime Nat.prime_two (by norm_num) (hu 0)
    rw [show u 0 % 2 = 1 by omega, pow_one]
  have hy : ConjClasses.powClass (u 1) (classTriple 1) = ConjClasses.mk yEl := by
    rw [classTriple_one, ConjClasses.powClass_mk, pow_mod_of_pow_eq_one yEl_pow_three (u 1)]
    have h3 : ¬ (3 ∣ u 1) := not_dvd_of_coprime Nat.prime_three (by norm_num) (hu 1)
    rcases (by omega : u 1 % 3 = 1 ∨ u 1 % 3 = 2) with h | h
    · rw [h, pow_one]
    · rw [h]; exact mk_yEl_sq
  have hz : ConjClasses.powClass (u 2) (classTriple 2) = ConjClasses.mk zEl ∨
      ConjClasses.powClass (u 2) (classTriple 2) = ConjClasses.mk zEl⁻¹ := by
    rw [classTriple_two, ConjClasses.powClass_mk]
    exact mk_zEl_pow_cases (not_dvd_of_coprime (by norm_num) (by norm_num) (hu 2))
  rcases hz with hz | hz
  · rw [show (fun i => ConjClasses.powClass (u i) (classTriple i)) = classTriple from ?_]
    · exact rigid_triple
    · funext i; fin_cases i
      exacts [hx, hy, hz]
  · rw [show (fun i => ConjClasses.powClass (u i) (classTriple i)) = classTriple' from ?_]
    · exact rigid_triple'
    · funext i; fin_cases i
      exacts [hx, hy.trans mk_yEl'_eq.symm, hz]

/-! ### `M₁₂` is a regular Galois group over a number field -/

/-- The prescribed classes are made of elements of order dividing `66`. -/
theorem order_dvd_sixtySix (i : Fin 3) (g : ↥M12) (hg : ConjClasses.mk g = classTriple i) :
    orderOf g ∣ 66 := by
  fin_cases i
  · rw [ConjClasses.orderOf_eq_of_mk_eq (h := xEl) hg]
    exact dvd_trans (orderOf_dvd_of_pow_eq_one xEl_pow_two) (by norm_num)
  · rw [ConjClasses.orderOf_eq_of_mk_eq (h := yEl) hg]
    exact dvd_trans (orderOf_dvd_of_pow_eq_one yEl_pow_three) (by norm_num)
  · rw [ConjClasses.orderOf_eq_of_mk_eq (h := zEl) hg]
    exact dvd_trans (orderOf_dvd_of_pow_eq_one zEl_pow_eleven) (by norm_num)

/-- The prescribed classes carry a generating product-one triple. -/
theorem rigidTuples_nonempty : (rigidTuples classTriple).Nonempty := by
  rcases Set.eq_empty_or_nonempty (rigidTuples classTriple) with h | h
  · exfalso
    have hcard := rigid_triple
    haveI : IsEmpty ↥(rigidTuples classTriple) := by rw [h]; infer_instance
    rw [Nat.card_of_isEmpty, M12_card] at hcard
    exact absurd hcard.symm (by norm_num)
  · exact h

/-- **`M₁₂` is a regular Galois group over a number field.**

The triple `(2A, 3A, 11A)` is rigid and generating and `M₁₂` is centerless, but the two classes of
`11`-cycles are irrational: the exponents prime to `11` interchange them.  The classes are
therefore stable only under an index-two subgroup of the cyclotomic action, and the rigidity method
descends the geometric cover not to `ℚ(T)` but to `K(T)` for the number field `K` that subgroup
cuts out. -/
theorem exists_regular_numberField :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K), IsRegularGaloisGroupOver K ↥M12 :=
  Rigidity.RET.Descent.exists_regular_numberField_of_orbitRigid (n := 66) classTriple
    (center_triv_iff_center_eq_bot.mpr center_eq_bot) order_dvd_sixtySix rigidTuples_nonempty
    orbit_rigid

end MathieuM12

end Rigidity

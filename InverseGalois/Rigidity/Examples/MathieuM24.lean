/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Rigidity.StructureCount
import InverseGalois.Rigidity.RET.Descent
import InverseGalois.Rigidity.Examples.MathieuM24Class
import Mathieu.M24Simple

/-!
# A rigid class triple in the Mathieu group `M₂₄`

`M₂₄` has twenty-six conjugacy classes, and exactly four unordered triples of them are **rigid**:
`(2A, 3B, 23A/B)`, `(2B, 3A, 23A/B)`, `(2A, 4A, 21A/B)` and `(2B, 3A, 21A/B)`.  This file
certifies one of them in the Lean kernel:

`(2A, 3B, 23A)` — an involution of cycle type `1⁸2⁸`, a fixed-point-free element of order `3`
(cycle type `3⁸`), and the standard `23`-cycle generator `m24a`.

Concretely, with `z = m24a` and the involution

`x = m24a⁻³ · m24c · m24b⁻² · m24a⁻¹ · m24b · m24a⁻¹ · m24b⁻¹ · m24a · m24c · m24b⁻²`

the pair `x, z` generates `M₂₄`, and the structure constant `#{w ∈ 2A : w z⁻¹ ∈ 3B}` equals
`23 = |C_{M₂₄}(z)|`.  By `Rigidity.rigid_of_card_prodOneFibre` that single count forces
`Nat.card (rigidTuples classTriple) = Nat.card M₂₄`: the product-one triples in these three
classes form a single simultaneous-conjugacy orbit, which is rigidity.

The kernel-checked half of the count — the class `2A` as a conjugation-closed tree of base-`24`
codes, and the two filtered lists of `23` keys — is
`InverseGalois.Rigidity.Examples.MathieuM24Class`.  Nothing here uses `native_decide`.

## Main results

* `Rigidity.MathieuM24.center_eq_bot` — `M₂₄` is centerless.
* `Rigidity.MathieuM24.gen_top` — the pair `x, z` generates `M₂₄`.
* `Rigidity.MathieuM24.card_prodOneFibre_le` — the structure constant is at most `23`.
* `Rigidity.MathieuM24.rigid_triple` — `Nat.card (rigidTuples classTriple) = Nat.card M₂₄`.
* `Rigidity.MathieuM24.orbit_rigid` — every cyclotomic twist of the triple is rigid too.
* `Rigidity.MathieuM24.exists_regular_numberField` — `M₂₄` is the Galois group of a regular
  extension of `K(T)` for a number field `K`.

The classes `23A` and `23B` are not rational (`m24a` is not conjugate to `m24a ^ 5` inside
`M₂₄`), so this triple does not assemble into a `RigidityCertificate M₂₄`, whose classes must
each be fixed by the whole cyclotomic action; the field cut out by the stabiliser of the triple
is `ℚ(√-23)`.
-/

namespace Rigidity

namespace MathieuM24

open Equiv Mathieu Mathieu.EnumM11

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

/-! ### The three elements of the triple -/

/-- The `23`-cycle of the triple is nontrivial. -/
lemma m24a_ne_one : m24a ≠ 1 := by decide

/-- The involution of the triple, as an element of `M₂₄`. -/
def xEl : ↥M24 := ⟨x0, x0_mem⟩

/-- The `23`-cycle of the triple: the standard generator `m24a`. -/
def zEl : ↥M24 := ⟨m24a, m24a_mem⟩

/-- The remaining entry of the triple, forced by the product-one relation. -/
def yEl : ↥M24 := xEl⁻¹ * zEl⁻¹

/-- The triple of conjugacy classes `(2A, 3B, 23A)` of `M₂₄`. -/
def classTriple : Fin 3 → ConjClasses ↥M24 :=
  ![ConjClasses.mk xEl, ConjClasses.mk yEl, ConjClasses.mk zEl]

lemma classTriple_zero : classTriple 0 = ConjClasses.mk xEl := rfl
lemma classTriple_one : classTriple 1 = ConjClasses.mk yEl := rfl
lemma classTriple_two : classTriple 2 = ConjClasses.mk zEl := rfl

lemma xEl_sq : xEl * xEl = 1 := Subtype.ext x0_sq

lemma xEl_inv : xEl⁻¹ = xEl := inv_eq_of_mul_eq_one_right xEl_sq

/-! ### `M₂₄` is centerless -/

theorem center_eq_bot : Subgroup.center (↥M24) = ⊥ := by
  rcases M24_isSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥M24)
    inferInstance with h | h
  · exact h
  · exfalso
    haveI : IsMulCommutative ↥M24 := by
      constructor
      constructor
      intro x y
      have hy : y ∈ Subgroup.center ↥M24 := by rw [h]; exact Subgroup.mem_top y
      exact Subgroup.mem_center_iff.mp hy x
    have hp : (Nat.card ↥M24).Prime :=
      (Group.is_simple_iff_prime_card (α := ↥M24)).mp M24_isSimpleGroup
    rw [M24_card] at hp
    exact absurd hp (by norm_num)

/-! ### The pair generates -/

/-- If a subgroup of `M₂₄` contains all three standard generators, it is everything. -/
theorem eq_top_of_gens_mem (K : Subgroup ↥M24)
    (ha : (⟨m24a, m24a_mem⟩ : ↥M24) ∈ K) (hb : (⟨m24b, m24b_mem⟩ : ↥M24) ∈ K)
    (hcg : (⟨m24c, m24c_mem⟩ : ↥M24) ∈ K) : K = ⊤ := by
  have key : ∀ (p : Perm (Fin 24)) (hp : p ∈ M24), (⟨p, hp⟩ : ↥M24) ∈ K := by
    intro p hp
    have hp' : p ∈ Subgroup.closure ({m24a, m24b, m24c} : Set (Perm (Fin 24))) := hp
    refine Subgroup.closure_induction_left
      (p := fun q hq => (⟨q, hq⟩ : ↥M24) ∈ K) ?_ ?_ ?_ hp'
    · exact one_mem K
    · intro g hg y hy ih
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      have hgm : g ∈ M24 := by
        rcases hg with rfl | rfl | rfl; exacts [m24a_mem, m24b_mem, m24c_mem]
      have hgK : (⟨g, hgm⟩ : ↥M24) ∈ K := by rcases hg with rfl | rfl | rfl; exacts [ha, hb, hcg]
      exact (show (⟨g, hgm⟩ : ↥M24) * ⟨y, hy⟩ ∈ K from mul_mem hgK ih)
    · intro g hg y hy ih
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      have hgm : g ∈ M24 := by
        rcases hg with rfl | rfl | rfl; exacts [m24a_mem, m24b_mem, m24c_mem]
      have hgK : (⟨g, hgm⟩ : ↥M24) ∈ K := by rcases hg with rfl | rfl | rfl; exacts [ha, hb, hcg]
      exact (show (⟨g, hgm⟩ : ↥M24)⁻¹ * ⟨y, hy⟩ ∈ K from mul_mem (inv_mem hgK) ih)
  rw [Subgroup.eq_top_iff']
  rintro ⟨p, hp⟩
  exact key p hp

theorem gen_top : Subgroup.closure ({xEl, zEl} : Set ↥M24) = ⊤ := by
  have hxK : xEl ∈ Subgroup.closure ({xEl, zEl} : Set ↥M24) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hzK : zEl ∈ Subgroup.closure ({xEl, zEl} : Set ↥M24) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hiK : zEl⁻¹ ∈ Subgroup.closure ({xEl, zEl} : Set ↥M24) := inv_mem hzK
  refine eq_top_of_gens_mem _ hzK ?_ ?_
  · have hval : (⟨m24b, m24b_mem⟩ : ↥M24) =
        xEl * zEl * zEl * zEl * zEl * zEl * xEl * zEl⁻¹ * zEl⁻¹ * xEl * zEl * zEl * xEl * zEl⁻¹ *
          zEl⁻¹ * zEl⁻¹ * zEl⁻¹ * xEl * zEl * xEl * zEl⁻¹ * xEl * zEl * zEl * xEl * zEl⁻¹ * xEl *
          zEl * zEl * zEl * zEl * xEl * zEl⁻¹ * zEl⁻¹ * zEl⁻¹ := by
      apply Subtype.ext
      show m24b =
        x0 * m24a * m24a * m24a * m24a * m24a * x0 * m24a⁻¹ * m24a⁻¹ * x0 * m24a * m24a * x0 *
        m24a⁻¹ * m24a⁻¹ * m24a⁻¹ * m24a⁻¹ * x0 * m24a * x0 * m24a⁻¹ * x0 * m24a * m24a * x0 *
        m24a⁻¹ * x0 * m24a * m24a * m24a * m24a * x0 * m24a⁻¹ * m24a⁻¹ * m24a⁻¹
      decide
    rw [hval]
    exact
      mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
      (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
      (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
      (mul_mem (mul_mem (mul_mem (mul_mem hxK hzK) hzK) hzK) hzK) hzK) hxK) hiK) hiK) hxK) hzK)
      hzK) hxK) hiK) hiK) hiK) hiK) hxK) hzK) hxK) hiK) hxK) hzK) hzK) hxK) hiK) hxK) hzK) hzK)
      hzK) hzK) hxK) hiK) hiK) hiK
  · have hval : (⟨m24c, m24c_mem⟩ : ↥M24) =
        xEl * zEl * zEl * zEl * xEl * zEl⁻¹ * xEl * zEl * zEl * xEl * zEl⁻¹ * zEl⁻¹ * zEl⁻¹ *
          zEl⁻¹ * xEl * zEl * xEl * zEl⁻¹ * zEl⁻¹ * xEl * zEl * xEl * zEl⁻¹ * xEl * zEl * zEl *
          zEl * zEl * xEl * zEl⁻¹ * zEl⁻¹ * xEl * zEl * xEl * zEl⁻¹ * zEl⁻¹ * xEl * zEl * xEl := by
      apply Subtype.ext
      show m24c =
        x0 * m24a * m24a * m24a * x0 * m24a⁻¹ * x0 * m24a * m24a * x0 * m24a⁻¹ * m24a⁻¹ * m24a⁻¹ *
        m24a⁻¹ * x0 * m24a * x0 * m24a⁻¹ * m24a⁻¹ * x0 * m24a * x0 * m24a⁻¹ * x0 * m24a * m24a *
        m24a * m24a * x0 * m24a⁻¹ * m24a⁻¹ * x0 * m24a * x0 * m24a⁻¹ * m24a⁻¹ * x0 * m24a * x0
      decide
    rw [hval]
    exact
      mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
      (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
      (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
      (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem hxK hzK) hzK) hzK)
      hxK) hiK) hxK) hzK) hzK) hxK) hiK) hiK) hiK) hiK) hxK) hzK) hxK) hiK) hiK) hxK) hzK) hxK)
      hiK) hxK) hzK) hzK) hzK) hzK) hxK) hiK) hiK) hxK) hzK) hxK) hiK) hiK) hxK) hzK) hxK

/-! ### The structure constant -/

/-- A set whose members carry distinct keys, all of them entries of a list, is no larger than the
list.  Keeping the list abstract is what makes the count cheap: the elaborator never has to look
inside the twenty-three-element list of keys. -/
theorem card_le_length_of_key {α : Type} {S : Set α} {L : List ℕ} (g : α → ℕ)
    (hg : Function.Injective g) (hmem : ∀ a : S, g (a : α) ∈ L) : Nat.card S ≤ L.length := by
  classical
  calc Nat.card S ≤ Nat.card ↥L.toFinset :=
        Nat.card_le_card_of_injective (fun a => ⟨g a, List.mem_toFinset.mpr (hmem a)⟩)
          (fun u v huv => Subtype.ext (hg (congrArg Subtype.val huv)))
    _ = L.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ L.length := List.toFinset_card_le _

/-- The key attached to an element of `M₂₄` determines it. -/
theorem key_injective : Function.Injective (fun w : ↥M24 => φ24 ((w : Perm (Fin 24)))) :=
  fun _ _ h => Subtype.ext (φ24_injective h)

/-- Membership in the filtered list of keys, stated so that the two defining conditions can be
supplied separately. -/
theorem mem_fibreList {k : ℕ} (h1 : TX.mem k = true) (h2 : testY (mulC24 k cAi) = true) :
    k ∈ fibreList := by
  unfold fibreList
  exact List.mem_filter.mpr ⟨Btree.mem_toList h1, h2⟩

/-- Membership in the mirror list of keys. -/
theorem mem_fibreList' {k : ℕ} (h1 : TX.mem k = true) (h2 : testY (mulC24 k cA) = true) :
    k ∈ fibreList' := by
  unfold fibreList'
  exact List.mem_filter.mpr ⟨Btree.mem_toList h1, h2⟩

/-- Every element of the class of `x` squares to one. -/
lemma sq_eq_one_of_conj {w : ↥M24} (hw : ConjClasses.mk w = ConjClasses.mk xEl) : w⁻¹ = w := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hw)
  have h1 : c * (w * w) * c⁻¹ = 1 := by
    rw [show c * (w * w) * c⁻¹ = (c * w * c⁻¹) * (c * w * c⁻¹) by group, hc, xEl_sq]
  have h2 : w * w = c⁻¹ * (c * (w * w) * c⁻¹) * c := by group
  rw [h1] at h2
  simp only [mul_one, inv_mul_cancel] at h2
  exact inv_eq_of_mul_eq_one_right h2

/-- The cube of `y` is the identity. -/
lemma y0_pow_three :
    ((x0⁻¹ * m24a⁻¹) * (x0⁻¹ * m24a⁻¹)) * (x0⁻¹ * m24a⁻¹) = 1 := by decide

/-- `y` moves every point. -/
lemma y0_nofix : ∀ i : Fin 24, (x0⁻¹ * m24a⁻¹) i ≠ i := by decide

/-- Every element of the class of `y` passes the `3B` test on codes. -/
lemma testY_of_conj {u : ↥M24} (hu : ConjClasses.mk u = ConjClasses.mk yEl) :
    testY (φ24 ((u : Perm (Fin 24)))) = true := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hu)
  set p : Perm (Fin 24) := (u : Perm (Fin 24)) with hp
  set d : Perm (Fin 24) := (c : Perm (Fin 24)) with hd
  have hcp : d * p * d⁻¹ = x0⁻¹ * m24a⁻¹ := congrArg Subtype.val hc
  have hpd : p = d⁻¹ * (x0⁻¹ * m24a⁻¹) * d := by rw [← hcp]; group
  have hp3 : (p * p) * p = 1 := by
    rw [hpd]
    calc d⁻¹ * (x0⁻¹ * m24a⁻¹) * d * (d⁻¹ * (x0⁻¹ * m24a⁻¹) * d) *
          (d⁻¹ * (x0⁻¹ * m24a⁻¹) * d)
        = d⁻¹ * (((x0⁻¹ * m24a⁻¹) * (x0⁻¹ * m24a⁻¹)) * (x0⁻¹ * m24a⁻¹)) * d := by group
      _ = 1 := by rw [y0_pow_three]; group
  have hnf : ∀ i : Fin 24, p i ≠ i := by
    intro i hi
    rw [hpd, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at hi
    have hcancel : d (d⁻¹ ((x0⁻¹ * m24a⁻¹) (d i))) = (x0⁻¹ * m24a⁻¹) (d i) := by
      have h := Equiv.Perm.mul_apply d d⁻¹ ((x0⁻¹ * m24a⁻¹) (d i))
      rw [mul_inv_cancel, Equiv.Perm.one_apply] at h
      exact h.symm
    have h2 := congrArg d hi
    rw [hcancel] at h2
    exact y0_nofix (d i) h2
  have hmul : mulC24 (φ24 p) (φ24 p) = φ24 (p * p) := mulC24_φ24 p p
  have hmul2 : mulC24 (φ24 (p * p)) (φ24 p) = φ24 ((p * p) * p) := mulC24_φ24 _ _
  have hcube : mulC24 (mulC24 (φ24 p) (φ24 p)) (φ24 p) = idCode24 := by
    rw [hmul, hmul2, hp3, φ24_one]
  have hhf : hasFix (φ24 p) = false := hasFix_eq_false_of_noFix hnf
  unfold testY
  rw [hcube, hhf]
  simp

theorem card_prodOneFibre_le :
    Nat.card (prodOneFibre (classTriple 0) (classTriple 1) zEl) ≤ 23 := by
  classical
  have hmap : ∀ w : ↥(prodOneFibre (classTriple 0) (classTriple 1) zEl),
      φ24 (((w : ↥M24) : Perm (Fin 24))) ∈ fibreList := by
    rintro ⟨w, hw0, hw1⟩
    rw [classTriple_zero] at hw0
    rw [classTriple_one] at hw1
    have hinv : w⁻¹ = w := sq_eq_one_of_conj hw0
    have hX : TX.mem (φ24 ((w : Perm (Fin 24)))) = true :=
      key_of_conjClass TX_closed TX_mem_x0 (u := xEl) rfl hw0
    have hY : testY (φ24 (((w⁻¹ * zEl⁻¹ : ↥M24) : Perm (Fin 24)))) = true := testY_of_conj hw1
    have hcoe : (((w⁻¹ * zEl⁻¹ : ↥M24) : Perm (Fin 24)))
        = ((w : Perm (Fin 24)))⁻¹ * m24a⁻¹ := rfl
    rw [hcoe, show ((w : Perm (Fin 24)))⁻¹ = (w : Perm (Fin 24)) from congrArg Subtype.val hinv]
      at hY
    have hmul : mulC24 (φ24 ((w : Perm (Fin 24)))) cAi = φ24 ((w : Perm (Fin 24)) * m24a⁻¹) := by
      rw [← cAi_eq, mulC24_φ24]
    refine mem_fibreList hX ?_
    rw [hmul]
    exact hY
  have hle := card_le_length_of_key (S := prodOneFibre (classTriple 0) (classTriple 1) zEl)
    (L := fibreList) _ key_injective hmap
  rwa [fibreList_length] at hle

/-! ### The centralizer of the `23`-cycle -/

/-- The `23`-cycle has order dividing twenty-three. -/
lemma zEl_pow_twentyThree : zEl ^ 23 = 1 := by
  apply Subtype.ext
  show m24a ^ 23 = 1
  exact m24a_pow_eq_one

theorem twentyThree_le_centralizer :
    23 ≤ Nat.card ↥(Subgroup.centralizer ({zEl} : Set ↥M24)) := by
  have hzne : zEl ≠ 1 := by
    intro h
    rw [Subtype.ext_iff] at h
    exact m24a_ne_one h
  haveI : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  have horder : orderOf zEl = 23 := orderOf_eq_prime zEl_pow_twentyThree hzne
  have hle : Subgroup.zpowers zEl ≤ Subgroup.centralizer ({zEl} : Set ↥M24) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.mpr (by rintro m rfl; rfl)
  have hcard : Nat.card ↥(Subgroup.zpowers zEl)
      ≤ Nat.card ↥(Subgroup.centralizer ({zEl} : Set ↥M24)) :=
    Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle)
  rwa [Nat.card_zpowers, horder] at hcard

/-! ### Rigidity -/

theorem xEl_mem_prodOneFibre :
    xEl ∈ prodOneFibre (classTriple 0) (classTriple 1) zEl := ⟨rfl, rfl⟩

/-- **The class triple `(2A, 3B, 23A)` is rigid in `M₂₄`.**  The product-one triples with entries
in these three classes form a single orbit under simultaneous conjugation, of full size
`|M₂₄| = 244823040`, and every one of them generates. -/
theorem rigid_triple : Nat.card ↥(rigidTuples classTriple) = Nat.card ↥M24 :=
  rigid_of_card_prodOneFibre center_eq_bot gen_top xEl_mem_prodOneFibre classTriple_two
    (le_trans card_prodOneFibre_le twentyThree_le_centralizer)

/-! ### The mirror triple `(2A, 3B, 23B)`

Inversion does not preserve the class of the `23`-cycle: `z` and `z⁻¹` lie in the two distinct
classes `23A` and `23B`, which the cyclotomic action interchanges.  Everything above therefore has
a mirror image, obtained by replacing `z` by `z⁻¹`; both triples are needed below, because the
cyclotomic orbit of `(2A, 3B, 23A)` consists of exactly these two triples. -/

/-- The remaining entry of the mirror triple, forced by the product-one relation. -/
def yEl' : ↥M24 := xEl⁻¹ * zEl

/-- The triple of conjugacy classes `(2A, 3B, 23B)` of `M₂₄`. -/
def classTriple' : Fin 3 → ConjClasses ↥M24 :=
  ![ConjClasses.mk xEl, ConjClasses.mk yEl', ConjClasses.mk zEl⁻¹]

lemma classTriple'_zero : classTriple' 0 = ConjClasses.mk xEl := rfl
lemma classTriple'_one : classTriple' 1 = ConjClasses.mk yEl' := rfl
lemma classTriple'_two : classTriple' 2 = ConjClasses.mk zEl⁻¹ := rfl

theorem gen_top' : Subgroup.closure ({xEl, zEl⁻¹} : Set ↥M24) = ⊤ := by
  have hxK : xEl ∈ Subgroup.closure ({xEl, zEl⁻¹} : Set ↥M24) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hiK : zEl⁻¹ ∈ Subgroup.closure ({xEl, zEl⁻¹} : Set ↥M24) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hzK : zEl ∈ Subgroup.closure ({xEl, zEl⁻¹} : Set ↥M24) := by
    simpa using inv_mem hiK
  refine eq_top_of_gens_mem _ hzK ?_ ?_
  · have hval : (⟨m24b, m24b_mem⟩ : ↥M24) =
        xEl * zEl * zEl * zEl * zEl * zEl * xEl * zEl⁻¹ * zEl⁻¹ * xEl * zEl * zEl * xEl * zEl⁻¹ *
          zEl⁻¹ * zEl⁻¹ * zEl⁻¹ * xEl * zEl * xEl * zEl⁻¹ * xEl * zEl * zEl * xEl * zEl⁻¹ * xEl *
          zEl * zEl * zEl * zEl * xEl * zEl⁻¹ * zEl⁻¹ * zEl⁻¹ := by
      apply Subtype.ext
      show m24b =
        x0 * m24a * m24a * m24a * m24a * m24a * x0 * m24a⁻¹ * m24a⁻¹ * x0 * m24a * m24a * x0 *
        m24a⁻¹ * m24a⁻¹ * m24a⁻¹ * m24a⁻¹ * x0 * m24a * x0 * m24a⁻¹ * x0 * m24a * m24a * x0 *
        m24a⁻¹ * x0 * m24a * m24a * m24a * m24a * x0 * m24a⁻¹ * m24a⁻¹ * m24a⁻¹
      decide
    rw [hval]
    exact
      mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
      (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
      (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
      (mul_mem (mul_mem (mul_mem (mul_mem hxK hzK) hzK) hzK) hzK) hzK) hxK) hiK) hiK) hxK) hzK)
      hzK) hxK) hiK) hiK) hiK) hiK) hxK) hzK) hxK) hiK) hxK) hzK) hzK) hxK) hiK) hxK) hzK) hzK)
      hzK) hzK) hxK) hiK) hiK) hiK
  · have hval : (⟨m24c, m24c_mem⟩ : ↥M24) =
        xEl * zEl * zEl * zEl * xEl * zEl⁻¹ * xEl * zEl * zEl * xEl * zEl⁻¹ * zEl⁻¹ * zEl⁻¹ *
          zEl⁻¹ * xEl * zEl * xEl * zEl⁻¹ * zEl⁻¹ * xEl * zEl * xEl * zEl⁻¹ * xEl * zEl * zEl *
          zEl * zEl * xEl * zEl⁻¹ * zEl⁻¹ * xEl * zEl * xEl * zEl⁻¹ * zEl⁻¹ * xEl * zEl * xEl := by
      apply Subtype.ext
      show m24c =
        x0 * m24a * m24a * m24a * x0 * m24a⁻¹ * x0 * m24a * m24a * x0 * m24a⁻¹ * m24a⁻¹ * m24a⁻¹ *
        m24a⁻¹ * x0 * m24a * x0 * m24a⁻¹ * m24a⁻¹ * x0 * m24a * x0 * m24a⁻¹ * x0 * m24a * m24a *
        m24a * m24a * x0 * m24a⁻¹ * m24a⁻¹ * x0 * m24a * x0 * m24a⁻¹ * m24a⁻¹ * x0 * m24a * x0
      decide
    rw [hval]
    exact
      mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
      (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
      (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
      (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem hxK hzK) hzK) hzK)
      hxK) hiK) hxK) hzK) hzK) hxK) hiK) hiK) hiK) hiK) hxK) hzK) hxK) hiK) hiK) hxK) hzK) hxK)
      hiK) hxK) hzK) hzK) hzK) hzK) hxK) hiK) hiK) hxK) hzK) hxK) hiK) hiK) hxK) hzK) hxK

/-- The cube of the mirror entry is the identity. -/
lemma y0'_pow_three : ((x0⁻¹ * m24a) * (x0⁻¹ * m24a)) * (x0⁻¹ * m24a) = 1 := by decide

/-- The mirror entry moves every point. -/
lemma y0'_nofix : ∀ i : Fin 24, (x0⁻¹ * m24a) i ≠ i := by decide

/-- Every element of the class of the mirror entry passes the `3B` test on codes. -/
lemma testY_of_conj' {u : ↥M24} (hu : ConjClasses.mk u = ConjClasses.mk yEl') :
    testY (φ24 ((u : Perm (Fin 24)))) = true := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hu)
  set p : Perm (Fin 24) := (u : Perm (Fin 24)) with hp
  set d : Perm (Fin 24) := (c : Perm (Fin 24)) with hd
  have hcp : d * p * d⁻¹ = x0⁻¹ * m24a := congrArg Subtype.val hc
  have hpd : p = d⁻¹ * (x0⁻¹ * m24a) * d := by rw [← hcp]; group
  have hp3 : (p * p) * p = 1 := by
    rw [hpd]
    calc d⁻¹ * (x0⁻¹ * m24a) * d * (d⁻¹ * (x0⁻¹ * m24a) * d) * (d⁻¹ * (x0⁻¹ * m24a) * d)
        = d⁻¹ * (((x0⁻¹ * m24a) * (x0⁻¹ * m24a)) * (x0⁻¹ * m24a)) * d := by group
      _ = 1 := by rw [y0'_pow_three]; group
  have hnf : ∀ i : Fin 24, p i ≠ i := by
    intro i hi
    rw [hpd, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at hi
    have hcancel : d (d⁻¹ ((x0⁻¹ * m24a) (d i))) = (x0⁻¹ * m24a) (d i) := by
      have h := Equiv.Perm.mul_apply d d⁻¹ ((x0⁻¹ * m24a) (d i))
      rw [mul_inv_cancel, Equiv.Perm.one_apply] at h
      exact h.symm
    have h2 := congrArg d hi
    rw [hcancel] at h2
    exact y0'_nofix (d i) h2
  have hmul : mulC24 (φ24 p) (φ24 p) = φ24 (p * p) := mulC24_φ24 p p
  have hmul2 : mulC24 (φ24 (p * p)) (φ24 p) = φ24 ((p * p) * p) := mulC24_φ24 _ _
  have hcube : mulC24 (mulC24 (φ24 p) (φ24 p)) (φ24 p) = idCode24 := by
    rw [hmul, hmul2, hp3, φ24_one]
  have hhf : hasFix (φ24 p) = false := hasFix_eq_false_of_noFix hnf
  unfold testY
  rw [hcube, hhf]
  simp

theorem card_prodOneFibre_le' :
    Nat.card (prodOneFibre (classTriple' 0) (classTriple' 1) zEl⁻¹) ≤ 23 := by
  classical
  have hmap : ∀ w : ↥(prodOneFibre (classTriple' 0) (classTriple' 1) zEl⁻¹),
      φ24 (((w : ↥M24) : Perm (Fin 24))) ∈ fibreList' := by
    rintro ⟨w, hw0, hw1⟩
    rw [classTriple'_zero] at hw0
    rw [classTriple'_one] at hw1
    have hinv : w⁻¹ = w := sq_eq_one_of_conj hw0
    have hX : TX.mem (φ24 ((w : Perm (Fin 24)))) = true :=
      key_of_conjClass TX_closed TX_mem_x0 (u := xEl) rfl hw0
    have hY : testY (φ24 (((w⁻¹ * zEl⁻¹⁻¹ : ↥M24) : Perm (Fin 24)))) = true := testY_of_conj' hw1
    have hcoe : (((w⁻¹ * zEl⁻¹⁻¹ : ↥M24) : Perm (Fin 24)))
        = ((w : Perm (Fin 24)))⁻¹ * m24a⁻¹⁻¹ := rfl
    rw [hcoe, show ((w : Perm (Fin 24)))⁻¹ = (w : Perm (Fin 24)) from congrArg Subtype.val hinv,
      inv_inv] at hY
    have hmul : mulC24 (φ24 ((w : Perm (Fin 24)))) cA = φ24 ((w : Perm (Fin 24)) * m24a) := by
      rw [← cA_eq, mulC24_φ24]
    refine mem_fibreList' hX ?_
    rw [hmul]
    exact hY
  have hle := card_le_length_of_key (S := prodOneFibre (classTriple' 0) (classTriple' 1) zEl⁻¹)
    (L := fibreList') _ key_injective hmap
  rwa [fibreList'_length] at hle

theorem twentyThree_le_centralizer' :
    23 ≤ Nat.card ↥(Subgroup.centralizer ({zEl⁻¹} : Set ↥M24)) := by
  have hz23 : zEl⁻¹ ^ 23 = 1 := by rw [inv_pow, zEl_pow_twentyThree, inv_one]
  have hzne : zEl⁻¹ ≠ 1 := by
    intro h
    rw [inv_eq_one, Subtype.ext_iff] at h
    exact m24a_ne_one h
  haveI : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  have horder : orderOf zEl⁻¹ = 23 := orderOf_eq_prime hz23 hzne
  have hle : Subgroup.zpowers zEl⁻¹ ≤ Subgroup.centralizer ({zEl⁻¹} : Set ↥M24) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.mpr (by rintro m rfl; rfl)
  have hcard : Nat.card ↥(Subgroup.zpowers zEl⁻¹)
      ≤ Nat.card ↥(Subgroup.centralizer ({zEl⁻¹} : Set ↥M24)) :=
    Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle)
  rwa [Nat.card_zpowers, horder] at hcard

theorem xEl_mem_prodOneFibre' :
    xEl ∈ prodOneFibre (classTriple' 0) (classTriple' 1) zEl⁻¹ := ⟨rfl, by rw [inv_inv]; rfl⟩

/-- **The class triple `(2A, 3B, 23B)` is rigid in `M₂₄`.** -/
theorem rigid_triple' : Nat.card ↥(rigidTuples classTriple') = Nat.card ↥M24 :=
  rigid_of_card_prodOneFibre center_eq_bot gen_top' xEl_mem_prodOneFibre' classTriple'_two
    (le_trans card_prodOneFibre_le' twentyThree_le_centralizer')

/-! ### The cyclotomic orbit of the triple

The exponents coprime to `138 = 2 · 3 · 23` act on the triple by raising each entry to that power.
The involution and the order-three entry are unmoved — `2A` and `3B` are rational classes of
`M₂₄` — while the `23`-cycle is carried to `z` or to `z⁻¹` according as the exponent is a
quadratic residue mod `23` or not.  Both possibilities are rigid, by `rigid_triple` and
`rigid_triple'`. -/

/-- A word in the standard generators conjugating the `23`-cycle to its square. -/
def g0 : Perm (Fin 24) := m24c * m24b⁻¹ * m24c * m24b

lemma g0_mem : g0 ∈ M24 :=
  mul_mem (mul_mem (mul_mem m24c_mem (inv_mem m24b_mem)) m24c_mem) m24b_mem

/-- The conjugator squaring the `23`-cycle, as an element of `M₂₄`. -/
def gEl : ↥M24 := ⟨g0, g0_mem⟩

/-- A word in the standard generators conjugating the order-three entry to its inverse. -/
def gy0 : Perm (Fin 24) := 
  m24b * m24c⁻¹ * m24b * m24a⁻¹ * m24a⁻¹ * m24a⁻¹ * m24b⁻¹ * m24c⁻¹ * m24b * m24a

lemma gy0_mem : gy0 ∈ M24 :=
  mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem m24b_mem
    (inv_mem m24c_mem)) m24b_mem) (inv_mem m24a_mem)) (inv_mem m24a_mem)) (inv_mem m24a_mem))
    (inv_mem m24b_mem)) (inv_mem m24c_mem)) m24b_mem) m24a_mem

/-- The conjugator inverting the order-three entry, as an element of `M₂₄`. -/
def gyEl : ↥M24 := ⟨gy0, gy0_mem⟩

/-- A word in the standard generators conjugating the mirror entry to the original one. -/
def gp0 : Perm (Fin 24) := 
  m24c * m24a⁻¹ * m24b⁻¹ * m24c * m24a⁻¹ * m24b⁻¹ * m24a * m24a * m24a * m24b⁻¹

lemma gp0_mem : gp0 ∈ M24 :=
  mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem m24c_mem
    (inv_mem m24a_mem)) (inv_mem m24b_mem)) m24c_mem) (inv_mem m24a_mem)) (inv_mem m24b_mem))
    m24a_mem) m24a_mem) m24a_mem) (inv_mem m24b_mem)

/-- The conjugator matching the two order-three entries, as an element of `M₂₄`. -/
def gpEl : ↥M24 := ⟨gp0, gp0_mem⟩

lemma conj_zEl_sq : gEl * zEl * gEl⁻¹ = zEl ^ 2 := by
  apply Subtype.ext
  show g0 * m24a * g0⁻¹ = m24a ^ 2
  decide

lemma conj_yEl_inv : gyEl * yEl * gyEl⁻¹ = yEl⁻¹ := by
  apply Subtype.ext
  show gy0 * (x0⁻¹ * m24a⁻¹) * gy0⁻¹ = (x0⁻¹ * m24a⁻¹)⁻¹
  decide

lemma conj_yEl' : gpEl * yEl' * gpEl⁻¹ = yEl := by
  apply Subtype.ext
  show gp0 * (x0⁻¹ * m24a) * gp0⁻¹ = x0⁻¹ * m24a⁻¹
  decide

/-- The two order-three entries are conjugate. -/
lemma mk_yEl'_eq : ConjClasses.mk yEl' = ConjClasses.mk yEl :=
  ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨gpEl, conj_yEl'⟩)

/-- An exponent may be reduced modulo any exponent of the element. -/
lemma pow_mod_of_pow_eq_one {g : ↥M24} {m : ℕ} (hm : g ^ m = 1) (u : ℕ) : g ^ u = g ^ (u % m) := by
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

/-- Conjugating by `g` doubles the exponent of the `23`-cycle. -/
lemma mk_zEl_conj (k : ℕ) : ConjClasses.mk (zEl ^ (2 * k)) = ConjClasses.mk (zEl ^ k) := by
  refine (ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨gEl, ?_⟩)).symm
  have h : ∀ n : ℕ, gEl * zEl ^ n * gEl⁻¹ = (gEl * zEl * gEl⁻¹) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ m ih => rw [pow_succ, pow_succ, ← ih]; group
  rw [h k, conj_zEl_sq, ← pow_mul]

/-- The `23`-cycle may be reduced modulo twenty-three. -/
lemma zEl_pow_mod (u : ℕ) : zEl ^ u = zEl ^ (u % 23) := pow_mod_of_pow_eq_one zEl_pow_twentyThree u

/-- Doubling the exponent modulo twenty-three does not change the class of the power. -/
lemma mk_zEl_step {j k : ℕ} (h : j % 23 = (2 * k) % 23) :
    ConjClasses.mk (zEl ^ j) = ConjClasses.mk (zEl ^ k) := by
  rw [zEl_pow_mod j, h, ← zEl_pow_mod (2 * k)]
  exact mk_zEl_conj k

/-- The twenty-second power of the `23`-cycle is its inverse. -/
lemma zEl_pow_twentyTwo : zEl ^ 22 = zEl⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  calc zEl ^ 22 * zEl = zEl ^ 23 := by group
    _ = 1 := zEl_pow_twentyThree

/-- **Every power of the `23`-cycle by an exponent prime to twenty-three lies in one of the two
classes `23A`, `23B`.** -/
lemma mk_zEl_pow_cases {k : ℕ} (hk : ¬ (23 ∣ k)) :
    ConjClasses.mk (zEl ^ k) = ConjClasses.mk zEl ∨
      ConjClasses.mk (zEl ^ k) = ConjClasses.mk zEl⁻¹ := by
  have e1 : ConjClasses.mk (zEl ^ 1) = ConjClasses.mk zEl := by rw [pow_one]
  have e22 : ConjClasses.mk (zEl ^ 22) = ConjClasses.mk zEl⁻¹ := by rw [zEl_pow_twentyTwo]
  have e2 : ConjClasses.mk (zEl ^ 2) = ConjClasses.mk zEl :=
    (mk_zEl_step (j := 2) (k := 1) (by norm_num)).trans e1
  have e4 : ConjClasses.mk (zEl ^ 4) = ConjClasses.mk zEl :=
    (mk_zEl_step (j := 4) (k := 2) (by norm_num)).trans e2
  have e8 : ConjClasses.mk (zEl ^ 8) = ConjClasses.mk zEl :=
    (mk_zEl_step (j := 8) (k := 4) (by norm_num)).trans e4
  have e16 : ConjClasses.mk (zEl ^ 16) = ConjClasses.mk zEl :=
    (mk_zEl_step (j := 16) (k := 8) (by norm_num)).trans e8
  have e9 : ConjClasses.mk (zEl ^ 9) = ConjClasses.mk zEl :=
    (mk_zEl_step (j := 9) (k := 16) (by norm_num)).trans e16
  have e18 : ConjClasses.mk (zEl ^ 18) = ConjClasses.mk zEl :=
    (mk_zEl_step (j := 18) (k := 9) (by norm_num)).trans e9
  have e13 : ConjClasses.mk (zEl ^ 13) = ConjClasses.mk zEl :=
    (mk_zEl_step (j := 13) (k := 18) (by norm_num)).trans e18
  have e3 : ConjClasses.mk (zEl ^ 3) = ConjClasses.mk zEl :=
    (mk_zEl_step (j := 3) (k := 13) (by norm_num)).trans e13
  have e6 : ConjClasses.mk (zEl ^ 6) = ConjClasses.mk zEl :=
    (mk_zEl_step (j := 6) (k := 3) (by norm_num)).trans e3
  have e12 : ConjClasses.mk (zEl ^ 12) = ConjClasses.mk zEl :=
    (mk_zEl_step (j := 12) (k := 6) (by norm_num)).trans e6
  have e21 : ConjClasses.mk (zEl ^ 21) = ConjClasses.mk zEl⁻¹ :=
    (mk_zEl_step (j := 21) (k := 22) (by norm_num)).trans e22
  have e19 : ConjClasses.mk (zEl ^ 19) = ConjClasses.mk zEl⁻¹ :=
    (mk_zEl_step (j := 19) (k := 21) (by norm_num)).trans e21
  have e15 : ConjClasses.mk (zEl ^ 15) = ConjClasses.mk zEl⁻¹ :=
    (mk_zEl_step (j := 15) (k := 19) (by norm_num)).trans e19
  have e7 : ConjClasses.mk (zEl ^ 7) = ConjClasses.mk zEl⁻¹ :=
    (mk_zEl_step (j := 7) (k := 15) (by norm_num)).trans e15
  have e14 : ConjClasses.mk (zEl ^ 14) = ConjClasses.mk zEl⁻¹ :=
    (mk_zEl_step (j := 14) (k := 7) (by norm_num)).trans e7
  have e5 : ConjClasses.mk (zEl ^ 5) = ConjClasses.mk zEl⁻¹ :=
    (mk_zEl_step (j := 5) (k := 14) (by norm_num)).trans e14
  have e10 : ConjClasses.mk (zEl ^ 10) = ConjClasses.mk zEl⁻¹ :=
    (mk_zEl_step (j := 10) (k := 5) (by norm_num)).trans e5
  have e20 : ConjClasses.mk (zEl ^ 20) = ConjClasses.mk zEl⁻¹ :=
    (mk_zEl_step (j := 20) (k := 10) (by norm_num)).trans e10
  have e17 : ConjClasses.mk (zEl ^ 17) = ConjClasses.mk zEl⁻¹ :=
    (mk_zEl_step (j := 17) (k := 20) (by norm_num)).trans e20
  have e11 : ConjClasses.mk (zEl ^ 11) = ConjClasses.mk zEl⁻¹ :=
    (mk_zEl_step (j := 11) (k := 17) (by norm_num)).trans e17
  obtain ⟨j, hj1, hj2, hjk⟩ : ∃ j, 1 ≤ j ∧ j < 23 ∧ k % 23 = j :=
    ⟨k % 23, by omega, Nat.mod_lt _ (by norm_num), rfl⟩
  rw [zEl_pow_mod k, hjk]
  interval_cases j
  exacts [Or.inl e1, Or.inl e2, Or.inl e3, Or.inl e4, Or.inr e5, Or.inl e6, Or.inr e7, Or.inl e8,
    Or.inl e9, Or.inr e10, Or.inr e11, Or.inl e12, Or.inl e13, Or.inr e14, Or.inr e15, Or.inl e16,
    Or.inr e17, Or.inl e18, Or.inr e19, Or.inr e20, Or.inr e21, Or.inr e22]

/-- No prime dividing `138` divides an exponent prime to `138`. -/
lemma not_dvd_of_coprime {u p : ℕ} (hp : p.Prime) (hpd : p ∣ 138) (h : Nat.Coprime u 138) :
    ¬ p ∣ u :=
  hp.coprime_iff_not_dvd.mp (Nat.Coprime.coprime_dvd_right hpd h).symm

/-- **Every cyclotomic twist of the triple `(2A, 3B, 23A)` is rigid.**  The twist by an exponent
prime to `138` is either the triple itself or its mirror image. -/
theorem orbit_rigid (u : Fin 3 → ℕ) (hu : ∀ i, Nat.Coprime (u i) 138) :
    Nat.card ↥(rigidTuples fun i => ConjClasses.powClass (u i) (classTriple i))
      = Nat.card ↥M24 := by
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

/-! ### `M₂₄` is a regular Galois group over a number field -/

/-- The prescribed classes are made of elements of order dividing `138`. -/
theorem order_dvd_oneThirtyEight (i : Fin 3) (g : ↥M24) (hg : ConjClasses.mk g = classTriple i) :
    orderOf g ∣ 138 := by
  fin_cases i
  · rw [ConjClasses.orderOf_eq_of_mk_eq (h := xEl) hg]
    exact dvd_trans (orderOf_dvd_of_pow_eq_one xEl_pow_two) (by norm_num)
  · rw [ConjClasses.orderOf_eq_of_mk_eq (h := yEl) hg]
    exact dvd_trans (orderOf_dvd_of_pow_eq_one yEl_pow_three) (by norm_num)
  · rw [ConjClasses.orderOf_eq_of_mk_eq (h := zEl) hg]
    exact dvd_trans (orderOf_dvd_of_pow_eq_one zEl_pow_twentyThree) (by norm_num)

/-- The prescribed classes carry a generating product-one triple. -/
theorem rigidTuples_nonempty : (rigidTuples classTriple).Nonempty := by
  rcases Set.eq_empty_or_nonempty (rigidTuples classTriple) with h | h
  · exfalso
    have hcard := rigid_triple
    haveI : IsEmpty ↥(rigidTuples classTriple) := by rw [h]; infer_instance
    rw [Nat.card_of_isEmpty, M24_card] at hcard
    exact absurd hcard.symm (by norm_num)
  · exact h

/-- **`M₂₄` is a regular Galois group over a number field.**

The triple `(2A, 3B, 23A)` is rigid and generating and `M₂₄` is centerless, but the two classes of
`23`-cycles are irrational: the exponents that are not quadratic residues mod `23` interchange
them.  The classes are therefore stable only under an index-two subgroup of the cyclotomic action,
and the rigidity method descends the geometric cover not to `ℚ(T)` but to `K(T)` for the number
field `K` that subgroup cuts out. -/
theorem exists_regular_numberField :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K), IsRegularGaloisGroupOver K ↥M24 :=
  Rigidity.RET.Descent.exists_regular_numberField_of_orbitRigid (n := 138) classTriple
    (center_triv_iff_center_eq_bot.mpr center_eq_bot) order_dvd_oneThirtyEight
    rigidTuples_nonempty orbit_rigid

end MathieuM24

end Rigidity

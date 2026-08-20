/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Rigidity.StructureCount
import InverseGalois.Rigidity.RET.Descent
import Mathieu.EnumM11
import Mathieu.M11Simple

/-!
# A rigid class triple in the Mathieu group `M₁₁`

`M₁₁` has ten conjugacy classes, and exactly four unordered triples of them are **rigid**:
`(2A, 4A, 11A)`, `(2A, 4A, 11B)`, `(2A, 11A, 11A)` and `(2A, 11B, 11B)`.  This file certifies
one of them in the Lean kernel:

`(2A, 4A, 11B)` — an involution, an element of cycle type `(4,4,1,1,1)`, and the standard
`11`-cycle generator `m11a`.

Concretely, with `z = m11a` and the involution

`x = m11a · m11b⁻¹ · m11a⁻³ · m11b² · m11a²`

the pair `x, z` generates `M₁₁`, and the structure constant `#{w ∈ 2A : w z⁻¹ ∈ 4A}` equals
`11 = |C_{M₁₁}(z)|`.  By `Rigidity.rigid_of_card_prodOneFibre` that single count forces
`Nat.card (rigidTuples classTriple) = Nat.card M₁₁`: the product-one triples in these three
classes form a single simultaneous-conjugacy orbit, which is rigidity.

## How the count is certified

Permutations are handled in the base-`11` integer encoding of `Mathieu.EnumM11` (`enc`, `dec`,
`φ`).  On top of it we need one new primitive, `mulC`, multiplying two encoded permutations; it
is `stepImg` applied to the digit function of the left factor, so `EnumM11.stepImg_bridge` gives
`mulC (φ g) (φ p) = φ (g * p)` immediately.

The class `2A` is stored as a binary search-tree literal `TX` (`165` keys).  The kernel checks
by `decide` that it is closed under conjugation by the two generators and their inverses; since
`Btree.mem` is one-sidedly sound, that alone gives the containment *class ⊆ tree*, which is what
an upper bound on the fibre needs.  For the second class no tree is required: `4A` consists of
the elements of order `4`, and a conjugate of `y` visibly satisfies `q² ≠ 1` and `q⁴ = 1`, a
test that is three code multiplications.  Filtering `TX` by that test applied to `w z⁻¹` leaves
exactly `11` keys, and the fibre injects into that list by `w ↦ φ w`, using that every element
of `2A` is an involution.

Nothing here uses `native_decide`.

## Main results

* `Rigidity.MathieuM11.center_eq_bot` — `M₁₁` is centerless.
* `Rigidity.MathieuM11.gen_top` — the pair `x, z` generates `M₁₁`.
* `Rigidity.MathieuM11.card_prodOneFibre_le` — the structure constant is at most `11`.
* `Rigidity.MathieuM11.rigid_triple` — `Nat.card (rigidTuples classTriple) = Nat.card M₁₁`.

The classes `11A` and `11B` are not rational (`m11a` is not conjugate to `m11a ^ 2` inside
`M₁₁`), so this triple does not assemble into a `RigidityCertificate M₁₁`, whose classes must
each be fixed by the whole cyclotomic action; the field cut out by the stabiliser of the triple
is `ℚ(√-11)`.
-/

namespace Rigidity

namespace MathieuM11

open Equiv Mathieu Mathieu.EnumM11

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

/-! ### Multiplication of encoded permutations -/

/-- The `j`-th base-`11` digit of a code. -/
def dg (a j : ℕ) : ℕ := a / 11 ^ j % 11

/-- Product of two encoded permutations: permute the digits of the right factor by the digit
table of the left factor. -/
def mulC (a b : ℕ) : ℕ := stepImg (dg a) b

lemma dg_φ (g : Perm (Fin 11)) (i : Fin 11) : (g i).val = dg (φ g) i.val := by
  have h : dec (φ g) = fun i => g i := dec_enc _
  exact (congrArg Fin.val (congrFun h i)).symm

lemma mulC_φ (g p : Perm (Fin 11)) : mulC (φ g) (φ p) = φ (g * p) := by
  rw [mulC, stepImg_bridge g (dg (φ g)) (dg_φ g), applyGenF_φ]

lemma mulC_conj (g q : Perm (Fin 11)) :
    mulC (φ g) (mulC (φ q) (φ g⁻¹)) = φ (g * q * g⁻¹) := by
  rw [mulC_φ, mulC_φ, mul_assoc]

lemma mulC_conj' (g q : Perm (Fin 11)) :
    mulC (φ g⁻¹) (mulC (φ q) (φ g)) = φ (g⁻¹ * q * g) := by
  rw [mulC_φ, mulC_φ, mul_assoc]

/-! ### The three elements of the triple -/

/-- The involution of the triple, as an explicit word in the two standard generators. -/
def x0 : Perm (Fin 11) :=
  m11a * m11b⁻¹ * m11a⁻¹ * m11a⁻¹ * m11a⁻¹ * m11b * m11b * m11a * m11a

lemma x0_mem : x0 ∈ M11 := by
  unfold x0
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
    m11a_mem (inv_mem m11b_mem)) (inv_mem m11a_mem)) (inv_mem m11a_mem)) (inv_mem m11a_mem))
    m11b_mem) m11b_mem) m11a_mem) m11a_mem

lemma x0_sq : x0 * x0 = 1 := by decide

/-- The involution of the triple, as an element of `M₁₁`. -/
def xEl : ↥M11 := ⟨x0, x0_mem⟩

/-- The `11`-cycle of the triple: the standard generator `m11a`. -/
def zEl : ↥M11 := ⟨m11a, m11a_mem⟩

/-- The remaining entry of the triple, forced by the product-one relation. -/
def yEl : ↥M11 := xEl⁻¹ * zEl⁻¹

/-- The triple of conjugacy classes `(2A, 4A, 11B)` of `M₁₁`. -/
def classTriple : Fin 3 → ConjClasses ↥M11 :=
  ![ConjClasses.mk xEl, ConjClasses.mk yEl, ConjClasses.mk zEl]

lemma classTriple_zero : classTriple 0 = ConjClasses.mk xEl := rfl
lemma classTriple_one : classTriple 1 = ConjClasses.mk yEl := rfl
lemma classTriple_two : classTriple 2 = ConjClasses.mk zEl := rfl

lemma xEl_sq : xEl * xEl = 1 := Subtype.ext x0_sq

lemma xEl_inv : xEl⁻¹ = xEl := inv_eq_of_mul_eq_one_right xEl_sq

/-! ### Codes of the generators -/

/-- Code of `m11a`. -/
def cA : ℕ := 25678050355
/-- Code of `m11a⁻¹`. -/
def cAi : ℕ := 253927386855
/-- Code of `m11b`. -/
def cB : ℕ := 192765893045
/-- Code of `m11b⁻¹`. -/
def cBi : ℕ := 164612460045

lemma cA_eq : φ m11a = cA := by decide
lemma cAi_eq : φ m11a⁻¹ = cAi := by decide
lemma cB_eq : φ m11b = cB := by decide
lemma cBi_eq : φ m11b⁻¹ = cBi := by decide

lemma x0_code : φ x0 = 126637611815 := by decide

/-! ### Conjugation-closed sets of codes

A tree of codes closed under conjugation by the two generators and their inverses contains the
whole `M₁₁`-conjugacy class of each of its keys.  Only the one-sided soundness of `Btree.mem` is
used, so no search-tree invariant is needed. -/

/-- The conjugation-closure test for a tree of codes. -/
abbrev ConjClosed (T : Btree) : Prop :=
  T.all (fun k => T.mem (mulC cA (mulC k cAi)) && T.mem (mulC cAi (mulC k cA)) &&
    T.mem (mulC cB (mulC k cBi)) && T.mem (mulC cBi (mulC k cB))) = true

lemma conj_gen_key {T : Btree} (hcl : ConjClosed T) {q : Perm (Fin 11)}
    (hq : T.mem (φ q) = true) :
    T.mem (φ (m11a * q * m11a⁻¹)) = true ∧ T.mem (φ (m11a⁻¹ * q * m11a)) = true ∧
      T.mem (φ (m11b * q * m11b⁻¹)) = true ∧ T.mem (φ (m11b⁻¹ * q * m11b)) = true := by
  have h := Btree.all_toList hcl _ (Btree.mem_toList hq)
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← cA_eq, ← cAi_eq, mulC_conj] at h1; exact h1
  · rw [← cAi_eq, ← cA_eq, mulC_conj'] at h2; exact h2
  · rw [← cB_eq, ← cBi_eq, mulC_conj] at h3; exact h3
  · rw [← cBi_eq, ← cB_eq, mulC_conj'] at h4; exact h4

/-- Closure under conjugation by the generators propagates to all of `M₁₁`. -/
theorem conj_key {T : Btree} (hcl : ConjClosed T) {c : Perm (Fin 11)} (hc : c ∈ M11)
    {p : Perm (Fin 11)} (hp : T.mem (φ p) = true) : T.mem (φ (c * p * c⁻¹)) = true := by
  have hc' : c ∈ Subgroup.closure ({m11a, m11b} : Set (Perm (Fin 11))) := hc
  refine Subgroup.closure_induction_left
    (p := fun c _ => ∀ q : Perm (Fin 11), T.mem (φ q) = true → T.mem (φ (c * q * c⁻¹)) = true)
    ?_ ?_ ?_ hc' p hp
  · intro q hq; simpa using hq
  · intro g hg y _ ih q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    have hstep : g * y * q * (g * y)⁻¹ = g * (y * q * y⁻¹) * g⁻¹ := by group
    rw [hstep]
    rcases hg with rfl | rfl
    · exact (conj_gen_key hcl (ih q hq)).1
    · exact (conj_gen_key hcl (ih q hq)).2.2.1
  · intro g hg y _ ih q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    have hstep : g⁻¹ * y * q * (g⁻¹ * y)⁻¹ = g⁻¹ * (y * q * y⁻¹) * g := by group
    rw [hstep]
    rcases hg with rfl | rfl
    · exact (conj_gen_key hcl (ih q hq)).2.1
    · exact (conj_gen_key hcl (ih q hq)).2.2.2

/-- Every member of the conjugacy class of a key is again a key. -/
theorem key_of_conjClass {T : Btree} (hcl : ConjClosed T) {p : Perm (Fin 11)}
    (hp : T.mem (φ p) = true) {u w : ↥M11} (hu : (u : Perm (Fin 11)) = p)
    (hw : ConjClasses.mk w = ConjClasses.mk u) : T.mem (φ (w : Perm (Fin 11))) = true := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hw)
  have hval : (c : Perm (Fin 11)) * (w : Perm (Fin 11)) * ((c : Perm (Fin 11)))⁻¹ = p := by
    rw [← hu, ← hc]; rfl
  have hw' : (w : Perm (Fin 11)) = ((c : Perm (Fin 11)))⁻¹ * p * (((c : Perm (Fin 11)))⁻¹)⁻¹ := by
    rw [← hval]; group
  rw [hw']
  exact conj_key hcl (inv_mem c.2) hp

/-! ### `M₁₁` is centerless -/

theorem center_eq_bot : Subgroup.center (↥M11) = ⊥ := by
  rcases M11_isSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥M11)
    inferInstance with h | h
  · exact h
  · exfalso
    haveI : IsMulCommutative ↥M11 := by
      constructor
      constructor
      intro x y
      have hy : y ∈ Subgroup.center ↥M11 := by rw [h]; exact Subgroup.mem_top y
      exact Subgroup.mem_center_iff.mp hy x
    have hp : (Nat.card ↥M11).Prime :=
      (Group.is_simple_iff_prime_card (α := ↥M11)).mp M11_isSimpleGroup
    rw [M11_card] at hp
    exact absurd hp (by norm_num)

/-! ### The pair generates -/

/-- If a subgroup of `M₁₁` contains both standard generators, it is everything. -/
theorem eq_top_of_gens_mem (K : Subgroup ↥M11)
    (ha : (⟨m11a, m11a_mem⟩ : ↥M11) ∈ K) (hb : (⟨m11b, m11b_mem⟩ : ↥M11) ∈ K) : K = ⊤ := by
  have key : ∀ (p : Perm (Fin 11)) (hp : p ∈ M11), (⟨p, hp⟩ : ↥M11) ∈ K := by
    intro p hp
    have hp' : p ∈ Subgroup.closure ({m11a, m11b} : Set (Perm (Fin 11))) := hp
    refine Subgroup.closure_induction_left
      (p := fun q hq => (⟨q, hq⟩ : ↥M11) ∈ K) ?_ ?_ ?_ hp'
    · exact one_mem K
    · intro g hg y hy ih
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      have hgm : g ∈ M11 := by rcases hg with rfl | rfl; exacts [m11a_mem, m11b_mem]
      have hgK : (⟨g, hgm⟩ : ↥M11) ∈ K := by rcases hg with rfl | rfl; exacts [ha, hb]
      exact (show (⟨g, hgm⟩ : ↥M11) * ⟨y, hy⟩ ∈ K from mul_mem hgK ih)
    · intro g hg y hy ih
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      have hgm : g ∈ M11 := by rcases hg with rfl | rfl; exacts [m11a_mem, m11b_mem]
      have hgK : (⟨g, hgm⟩ : ↥M11) ∈ K := by rcases hg with rfl | rfl; exacts [ha, hb]
      exact (show (⟨g, hgm⟩ : ↥M11)⁻¹ * ⟨y, hy⟩ ∈ K from mul_mem (inv_mem hgK) ih)
  rw [Subgroup.eq_top_iff']
  rintro ⟨p, hp⟩
  exact key p hp

theorem gen_top : Subgroup.closure ({xEl, zEl} : Set ↥M11) = ⊤ := by
  have hxK : xEl ∈ Subgroup.closure ({xEl, zEl} : Set ↥M11) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hzK : zEl ∈ Subgroup.closure ({xEl, zEl} : Set ↥M11) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  refine eq_top_of_gens_mem _ hzK ?_
  have hval : (⟨m11b, m11b_mem⟩ : ↥M11) =
      zEl⁻¹ * zEl⁻¹ * xEl * zEl * zEl * xEl * zEl * zEl * zEl * xEl * zEl * zEl * xEl := by
    apply Subtype.ext
    show m11b = m11a⁻¹ * m11a⁻¹ * x0 * m11a * m11a * x0 * m11a * m11a * m11a * x0 * m11a *
      m11a * x0
    decide
  have hiK : zEl⁻¹ ∈ Subgroup.closure ({xEl, zEl} : Set ↥M11) := inv_mem hzK
  rw [hval]
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
    (mul_mem (mul_mem (mul_mem hiK hiK) hxK) hzK) hzK) hxK) hzK) hzK) hzK) hxK) hzK) hzK) hxK

/-! ### The class trees -/

/-- The `165` codes of the class `2A` of `M₁₁` (involutions of cycle type
`(2,2,2,2,1,1,1)`). -/
noncomputable def TX : Btree :=
  (Btree.nd (Btree.nd (Btree.nd (Btree.nd (Btree.nd (Btree.nd (Btree.nd (Btree.nd Btree.lf
  3148909675 Btree.lf) 6378492515 Btree.lf) 7397465415 (Btree.nd (Btree.nd Btree.lf 11276926935
  Btree.lf) 12786926635 Btree.lf)) 16015134145 (Btree.nd (Btree.nd (Btree.nd Btree.lf 18403553585
  Btree.lf) 20843137435 Btree.lf) 21796531525 (Btree.nd Btree.lf 22317705695 Btree.lf)))
  22581146015 (Btree.nd (Btree.nd (Btree.nd (Btree.nd Btree.lf 23025404885 Btree.lf) 27798563835
  Btree.lf) 32438097685 (Btree.nd Btree.lf 33155669555 Btree.lf)) 37188104415 (Btree.nd (Btree.nd
  (Btree.nd Btree.lf 38246015885 Btree.lf) 41757527245 Btree.lf) 43919635705 (Btree.nd Btree.lf
  46877657005 Btree.lf)))) 47942712675 (Btree.nd (Btree.nd (Btree.nd (Btree.nd (Btree.nd Btree.lf
  48056291025 Btree.lf) 48242715605 Btree.lf) 49003697305 (Btree.nd (Btree.nd Btree.lf 53542713255
  Btree.lf) 55375039775 Btree.lf)) 60683927585 (Btree.nd (Btree.nd (Btree.nd Btree.lf 63169173365
  Btree.lf) 65510282585 Btree.lf) 67033248725 (Btree.nd Btree.lf 68565755475 Btree.lf)))
  72811411255 (Btree.nd (Btree.nd (Btree.nd (Btree.nd Btree.lf 73394917695 Btree.lf) 73848659515
  Btree.lf) 74533175535 (Btree.nd Btree.lf 74813743715 Btree.lf)) 78167463955 (Btree.nd (Btree.nd
  (Btree.nd Btree.lf 81932060485 Btree.lf) 84380182255 Btree.lf) 88911571265 (Btree.nd Btree.lf
  90903859625 Btree.lf))))) 93185425245 (Btree.nd (Btree.nd (Btree.nd (Btree.nd (Btree.nd
  (Btree.nd Btree.lf 96218864615 Btree.lf) 98694584605 Btree.lf) 99163975325 (Btree.nd (Btree.nd
  Btree.lf 99562928465 Btree.lf) 100038569655 Btree.lf)) 100777998985 (Btree.nd (Btree.nd
  (Btree.nd Btree.lf 104952255835 Btree.lf) 107931860225 Btree.lf) 109903286505 (Btree.nd Btree.lf
  112677075445 Btree.lf))) 115688075335 (Btree.nd (Btree.nd (Btree.nd (Btree.nd Btree.lf
  119629152925 Btree.lf) 121084741195 Btree.lf) 124605476215 (Btree.nd Btree.lf 125322633255
  Btree.lf)) 125431014635 (Btree.nd (Btree.nd (Btree.nd Btree.lf 126637611815 Btree.lf)
  126730542955 Btree.lf) 131463905835 (Btree.nd Btree.lf 132611872795 Btree.lf)))) 134766077765
  (Btree.nd (Btree.nd (Btree.nd (Btree.nd (Btree.nd Btree.lf 138488118765 Btree.lf) 139150776905
  Btree.lf) 144534484765 (Btree.nd Btree.lf 148088185465 Btree.lf)) 150623278095 (Btree.nd
  (Btree.nd (Btree.nd Btree.lf 151897140945 Btree.lf) 152288643685 Btree.lf) 152577363225
  (Btree.nd Btree.lf 152768718215 Btree.lf))) 157435993735 (Btree.nd (Btree.nd (Btree.nd (Btree.nd
  Btree.lf 159851541745 Btree.lf) 161314279555 Btree.lf) 163925669855 (Btree.nd Btree.lf
  165640121295 Btree.lf)) 169187359925 (Btree.nd (Btree.nd (Btree.nd Btree.lf 172538450055
  Btree.lf) 176455110535 Btree.lf) 177000544025 (Btree.nd Btree.lf 177507743695 Btree.lf))))))
  178520919635 (Btree.nd (Btree.nd (Btree.nd (Btree.nd (Btree.nd (Btree.nd (Btree.nd Btree.lf
  178637325185 Btree.lf) 182196740405 Btree.lf) 185415839125 (Btree.nd (Btree.nd Btree.lf
  188197495475 Btree.lf) 189699686385 Btree.lf)) 191832659255 (Btree.nd (Btree.nd (Btree.nd
  Btree.lf 195273547175 Btree.lf) 197635671875 Btree.lf) 202552294815 (Btree.nd Btree.lf
  202983915725 Btree.lf))) 203203395235 (Btree.nd (Btree.nd (Btree.nd (Btree.nd Btree.lf
  204058633075 Btree.lf) 204697642535 Btree.lf) 209790744205 (Btree.nd Btree.lf 212131121425
  Btree.lf)) 214369735125 (Btree.nd (Btree.nd (Btree.nd Btree.lf 216804716205 Btree.lf)
  219214866205 Btree.lf) 221575965105 (Btree.nd Btree.lf 223826942075 Btree.lf)))) 226335487875
  (Btree.nd (Btree.nd (Btree.nd (Btree.nd (Btree.nd Btree.lf 230914623885 Btree.lf) 230923366955
  Btree.lf) 230970256375 (Btree.nd (Btree.nd Btree.lf 231003504945 Btree.lf) 257066768065
  Btree.lf)) 257360366505 (Btree.nd (Btree.nd (Btree.nd Btree.lf 257453000405 Btree.lf)
  257805678725 Btree.lf) 257942951425 (Btree.nd Btree.lf 258236424835 Btree.lf))) 258453553875
  (Btree.nd (Btree.nd (Btree.nd (Btree.nd Btree.lf 258675334225 Btree.lf) 258762006415 Btree.lf)
  258809385885 (Btree.nd Btree.lf 258833335005 Btree.lf)) 258873722175 (Btree.nd (Btree.nd
  (Btree.nd Btree.lf 260161240315 Btree.lf) 260257414085 Btree.lf) 260773197705 (Btree.nd Btree.lf
  261138931975 Btree.lf))))) 261814598075 (Btree.nd (Btree.nd (Btree.nd (Btree.nd (Btree.nd
  (Btree.nd Btree.lf 262735983785 Btree.lf) 263399722755 Btree.lf) 263452768795 (Btree.nd
  (Btree.nd Btree.lf 264228872685 Btree.lf) 264863373665 Btree.lf)) 265251905845 (Btree.nd
  (Btree.nd (Btree.nd Btree.lf 265831678865 Btree.lf) 267023874045 Btree.lf) 267788207295
  (Btree.nd Btree.lf 268108274115 Btree.lf))) 268293013715 (Btree.nd (Btree.nd (Btree.nd (Btree.nd
  Btree.lf 269031965165 Btree.lf) 269920002165 Btree.lf) 270243065865 (Btree.nd Btree.lf
  270589334545 Btree.lf)) 271445438055 (Btree.nd (Btree.nd (Btree.nd Btree.lf 271838696395
  Btree.lf) 272821877235 Btree.lf) 273020260385 (Btree.nd Btree.lf 273636488925 Btree.lf))))
  273889366775 (Btree.nd (Btree.nd (Btree.nd (Btree.nd (Btree.nd Btree.lf 274025929585 Btree.lf)
  275331288375 Btree.lf) 276490023205 (Btree.nd Btree.lf 276923773105 Btree.lf)) 277128407375
  (Btree.nd (Btree.nd (Btree.nd Btree.lf 277772742085 Btree.lf) 280176900505 Btree.lf)
  280276281175 (Btree.nd Btree.lf 280296443025 Btree.lf))) 280304322315 (Btree.nd (Btree.nd
  (Btree.nd (Btree.nd Btree.lf 280665592985 Btree.lf) 280858992065 Btree.lf) 281153983015
  (Btree.nd Btree.lf 281318685565 Btree.lf)) 281457361555 (Btree.nd (Btree.nd (Btree.nd Btree.lf
  281810620675 Btree.lf) 281915960205 Btree.lf) 282260165475 (Btree.nd Btree.lf 282409227205
  Btree.lf)))))))

lemma TX_closed : ConjClosed TX := by decide +kernel

lemma TX_mem_x0 : TX.mem (φ x0) = true := by rw [x0_code]; decide +kernel

/-! ### Order four, in codes

`4A` is the only class of `M₁₁` of elements of order `4`, so membership in it can be tested
without a second class tree: an element `q` lies in `4A` exactly when `q² ≠ 1` and `q⁴ = 1`.
Only the easy implication is needed below, namely that a conjugate of `y` satisfies the test. -/

/-- The order-four test on a code: the square is not the identity, the fourth power is. -/
def ord4 (q : ℕ) : Bool :=
  (mulC q q != idCode) && (mulC (mulC q q) (mulC q q) == idCode)

/-- The keys of the involution tree whose product with `z⁻¹` has order four: an
over-approximation of the structure-constant fibre. -/
noncomputable def fibreList : List ℕ := TX.toList.filter (fun k => ord4 (mulC k cAi))

lemma fibreList_length : fibreList.length = 11 := by decide +kernel

/-! ### The structure constant -/

/-- Every element of the class of `x` squares to one. -/
lemma sq_eq_one_of_conj {w : ↥M11} (hw : ConjClasses.mk w = ConjClasses.mk xEl) : w⁻¹ = w := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hw)
  have h1 : c * (w * w) * c⁻¹ = 1 := by
    rw [show c * (w * w) * c⁻¹ = (c * w * c⁻¹) * (c * w * c⁻¹) by group, hc, xEl_sq]
  have h2 : w * w = c⁻¹ * (c * (w * w) * c⁻¹) * c := by group
  rw [h1] at h2
  simp only [mul_one, inv_mul_cancel] at h2
  exact inv_eq_of_mul_eq_one_right h2

/-- Conjugation commutes with squaring. -/
lemma sq_conj {c p y : Perm (Fin 11)} (h : c * p * c⁻¹ = y) : c * (p * p) * c⁻¹ = y * y := by
  rw [← h]; group

/-- The square of `y` is not the identity. -/
lemma y0_sq_ne_one : (x0⁻¹ * m11a⁻¹) * (x0⁻¹ * m11a⁻¹) ≠ 1 := by decide

/-- The fourth power of `y` is the identity. -/
lemma y0_pow_four :
    ((x0⁻¹ * m11a⁻¹) * (x0⁻¹ * m11a⁻¹)) * ((x0⁻¹ * m11a⁻¹) * (x0⁻¹ * m11a⁻¹)) = 1 := by decide

/-- Every element of the class of `y` passes the order-four test on codes. -/
lemma ord4_of_conj {u : ↥M11} (hu : ConjClasses.mk u = ConjClasses.mk yEl) :
    ord4 (φ ((u : Perm (Fin 11)))) = true := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hu)
  set p : Perm (Fin 11) := (u : Perm (Fin 11)) with hp
  set d : Perm (Fin 11) := (c : Perm (Fin 11)) with hd
  have hcp : d * p * d⁻¹ = x0⁻¹ * m11a⁻¹ := congrArg Subtype.val hc
  have h2 : d * (p * p) * d⁻¹ = (x0⁻¹ * m11a⁻¹) * (x0⁻¹ * m11a⁻¹) := sq_conj hcp
  have h4 : d * ((p * p) * (p * p)) * d⁻¹ = 1 := by
    rw [sq_conj h2, y0_pow_four]
  have hp4 : (p * p) * (p * p) = 1 := by
    calc (p * p) * (p * p) = d⁻¹ * (d * ((p * p) * (p * p)) * d⁻¹) * d := by group
      _ = 1 := by rw [h4]; group
  have hp2 : p * p ≠ 1 := fun h => y0_sq_ne_one (by rw [← h2, h]; group)
  have hne : φ (p * p) ≠ idCode := fun h => hp2 (φ_injective (h.trans φ_one.symm))
  have hmul : mulC (φ p) (φ p) = φ (p * p) := mulC_φ p p
  have hmul2 : mulC (φ (p * p)) (φ (p * p)) = φ ((p * p) * (p * p)) := mulC_φ _ _
  unfold ord4
  rw [hmul, hmul2, hp4, φ_one]
  simp only [beq_self_eq_true, Bool.and_true, bne_iff_ne, ne_eq]
  exact hne

theorem card_prodOneFibre_le :
    Nat.card (prodOneFibre (classTriple 0) (classTriple 1) zEl) ≤ 11 := by
  classical
  have hmap : ∀ w : ↥(prodOneFibre (classTriple 0) (classTriple 1) zEl),
      φ (((w : ↥M11) : Perm (Fin 11))) ∈ fibreList := by
    rintro ⟨w, hw0, hw1⟩
    rw [classTriple_zero] at hw0
    rw [classTriple_one] at hw1
    have hinv : w⁻¹ = w := sq_eq_one_of_conj hw0
    have hX : TX.mem (φ ((w : Perm (Fin 11)))) = true :=
      key_of_conjClass TX_closed TX_mem_x0 (u := xEl) rfl hw0
    have hY : ord4 (φ (((w⁻¹ * zEl⁻¹ : ↥M11) : Perm (Fin 11)))) = true := ord4_of_conj hw1
    have hcoe : (((w⁻¹ * zEl⁻¹ : ↥M11) : Perm (Fin 11)))
        = ((w : Perm (Fin 11)))⁻¹ * m11a⁻¹ := rfl
    rw [hcoe, show ((w : Perm (Fin 11)))⁻¹ = (w : Perm (Fin 11)) from congrArg Subtype.val hinv]
      at hY
    have hmul : mulC (φ ((w : Perm (Fin 11)))) cAi = φ ((w : Perm (Fin 11)) * m11a⁻¹) := by
      rw [← cAi_eq, mulC_φ]
    refine List.mem_filter.mpr ⟨Btree.mem_toList hX, ?_⟩
    rw [hmul]
    exact hY
  let f : ↥(prodOneFibre (classTriple 0) (classTriple 1) zEl) → ↥fibreList.toFinset :=
    fun w => ⟨φ (((w : ↥M11) : Perm (Fin 11))), List.mem_toFinset.mpr (hmap w)⟩
  have hf : Function.Injective f := by
    intro u v huv
    have h1 : φ (((u : ↥M11) : Perm (Fin 11))) = φ (((v : ↥M11) : Perm (Fin 11))) :=
      congrArg Subtype.val huv
    exact Subtype.ext (Subtype.ext (φ_injective h1))
  calc Nat.card ↥(prodOneFibre (classTriple 0) (classTriple 1) zEl)
      ≤ Nat.card ↥fibreList.toFinset := Nat.card_le_card_of_injective f hf
    _ = fibreList.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ fibreList.length := List.toFinset_card_le _
    _ = 11 := fibreList_length

/-! ### The centralizer of the `11`-cycle -/

theorem eleven_le_centralizer :
    11 ≤ Nat.card ↥(Subgroup.centralizer ({zEl} : Set ↥M11)) := by
  have hz11 : zEl ^ 11 = 1 := by
    apply Subtype.ext
    show m11a ^ 11 = 1
    exact m11a_pow_eq_one
  have hzne : zEl ≠ 1 := fun h => m11a_ne_one (congrArg Subtype.val h)
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have horder : orderOf zEl = 11 := orderOf_eq_prime hz11 hzne
  have hle : Subgroup.zpowers zEl ≤ Subgroup.centralizer ({zEl} : Set ↥M11) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.mpr (by rintro m rfl; rfl)
  have hcard : Nat.card ↥(Subgroup.zpowers zEl)
      ≤ Nat.card ↥(Subgroup.centralizer ({zEl} : Set ↥M11)) :=
    Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle)
  rwa [Nat.card_zpowers, horder] at hcard

/-! ### Rigidity -/

theorem xEl_mem_prodOneFibre :
    xEl ∈ prodOneFibre (classTriple 0) (classTriple 1) zEl := ⟨rfl, rfl⟩

/-- **The class triple `(2A, 4A, 11B)` is rigid in `M₁₁`.**  The product-one triples with entries
in these three classes form a single orbit under simultaneous conjugation, of full size
`|M₁₁| = 7920`, and every one of them generates. -/
theorem rigid_triple : Nat.card ↥(rigidTuples classTriple) = Nat.card ↥M11 :=
  rigid_of_card_prodOneFibre center_eq_bot gen_top xEl_mem_prodOneFibre classTriple_two
    (le_trans card_prodOneFibre_le eleven_le_centralizer)

/-! ### The mirror triple `(2A, 4A, 11A)`

Inversion does not preserve the class of the `11`-cycle: `z` and `z⁻¹` lie in the two distinct
classes `11B` and `11A`, which the cyclotomic action interchanges.  Everything above therefore has
a mirror image, obtained by replacing `z` by `z⁻¹`; both triples are needed below, because the
cyclotomic orbit of `(2A, 4A, 11B)` consists of exactly these two triples. -/

/-- The remaining entry of the mirror triple, forced by the product-one relation. -/
def yEl' : ↥M11 := xEl⁻¹ * zEl

/-- The triple of conjugacy classes `(2A, 4A, 11A)` of `M₁₁`. -/
def classTriple' : Fin 3 → ConjClasses ↥M11 :=
  ![ConjClasses.mk xEl, ConjClasses.mk yEl', ConjClasses.mk zEl⁻¹]

lemma classTriple'_zero : classTriple' 0 = ConjClasses.mk xEl := rfl
lemma classTriple'_one : classTriple' 1 = ConjClasses.mk yEl' := rfl
lemma classTriple'_two : classTriple' 2 = ConjClasses.mk zEl⁻¹ := rfl

theorem gen_top' : Subgroup.closure ({xEl, zEl⁻¹} : Set ↥M11) = ⊤ := by
  have hxK : xEl ∈ Subgroup.closure ({xEl, zEl⁻¹} : Set ↥M11) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hiK : zEl⁻¹ ∈ Subgroup.closure ({xEl, zEl⁻¹} : Set ↥M11) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hzK : zEl ∈ Subgroup.closure ({xEl, zEl⁻¹} : Set ↥M11) := by
    simpa using inv_mem hiK
  refine eq_top_of_gens_mem _ hzK ?_
  have hval : (⟨m11b, m11b_mem⟩ : ↥M11) =
      zEl⁻¹ * zEl⁻¹ * xEl * zEl * zEl * xEl * zEl * zEl * zEl * xEl * zEl * zEl * xEl := by
    apply Subtype.ext
    show m11b = m11a⁻¹ * m11a⁻¹ * x0 * m11a * m11a * x0 * m11a * m11a * m11a * x0 * m11a *
      m11a * x0
    decide
  rw [hval]
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
    (mul_mem (mul_mem (mul_mem hiK hiK) hxK) hzK) hzK) hxK) hzK) hzK) hzK) hxK) hzK) hzK) hxK

/-- The keys of the involution tree whose product with `z` has order four: an over-approximation
of the mirror structure-constant fibre. -/
noncomputable def fibreList' : List ℕ := TX.toList.filter (fun k => ord4 (mulC k cA))

lemma fibreList'_length : fibreList'.length = 11 := by decide +kernel

/-- The square of the mirror entry is not the identity. -/
lemma y0'_sq_ne_one : (x0⁻¹ * m11a) * (x0⁻¹ * m11a) ≠ 1 := by decide

/-- The fourth power of the mirror entry is the identity. -/
lemma y0'_pow_four :
    ((x0⁻¹ * m11a) * (x0⁻¹ * m11a)) * ((x0⁻¹ * m11a) * (x0⁻¹ * m11a)) = 1 := by decide

/-- Every element of the class of the mirror entry passes the order-four test on codes. -/
lemma ord4_of_conj' {u : ↥M11} (hu : ConjClasses.mk u = ConjClasses.mk yEl') :
    ord4 (φ ((u : Perm (Fin 11)))) = true := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hu)
  set p : Perm (Fin 11) := (u : Perm (Fin 11)) with hp
  set d : Perm (Fin 11) := (c : Perm (Fin 11)) with hd
  have hcp : d * p * d⁻¹ = x0⁻¹ * m11a := congrArg Subtype.val hc
  have h2 : d * (p * p) * d⁻¹ = (x0⁻¹ * m11a) * (x0⁻¹ * m11a) := sq_conj hcp
  have h4 : d * ((p * p) * (p * p)) * d⁻¹ = 1 := by
    rw [sq_conj h2, y0'_pow_four]
  have hp4 : (p * p) * (p * p) = 1 := by
    calc (p * p) * (p * p) = d⁻¹ * (d * ((p * p) * (p * p)) * d⁻¹) * d := by group
      _ = 1 := by rw [h4]; group
  have hp2 : p * p ≠ 1 := fun h => y0'_sq_ne_one (by rw [← h2, h]; group)
  have hne : φ (p * p) ≠ idCode := fun h => hp2 (φ_injective (h.trans φ_one.symm))
  have hmul : mulC (φ p) (φ p) = φ (p * p) := mulC_φ p p
  have hmul2 : mulC (φ (p * p)) (φ (p * p)) = φ ((p * p) * (p * p)) := mulC_φ _ _
  unfold ord4
  rw [hmul, hmul2, hp4, φ_one]
  simp only [beq_self_eq_true, Bool.and_true, bne_iff_ne, ne_eq]
  exact hne

theorem card_prodOneFibre_le' :
    Nat.card (prodOneFibre (classTriple' 0) (classTriple' 1) zEl⁻¹) ≤ 11 := by
  classical
  have hmap : ∀ w : ↥(prodOneFibre (classTriple' 0) (classTriple' 1) zEl⁻¹),
      φ (((w : ↥M11) : Perm (Fin 11))) ∈ fibreList' := by
    rintro ⟨w, hw0, hw1⟩
    rw [classTriple'_zero] at hw0
    rw [classTriple'_one] at hw1
    have hinv : w⁻¹ = w := sq_eq_one_of_conj hw0
    have hX : TX.mem (φ ((w : Perm (Fin 11)))) = true :=
      key_of_conjClass TX_closed TX_mem_x0 (u := xEl) rfl hw0
    have hY : ord4 (φ (((w⁻¹ * zEl⁻¹⁻¹ : ↥M11) : Perm (Fin 11)))) = true := ord4_of_conj' hw1
    have hcoe : (((w⁻¹ * zEl⁻¹⁻¹ : ↥M11) : Perm (Fin 11)))
        = ((w : Perm (Fin 11)))⁻¹ * m11a⁻¹⁻¹ := rfl
    rw [hcoe, show ((w : Perm (Fin 11)))⁻¹ = (w : Perm (Fin 11)) from congrArg Subtype.val hinv,
      inv_inv] at hY
    have hmul : mulC (φ ((w : Perm (Fin 11)))) cA = φ ((w : Perm (Fin 11)) * m11a) := by
      rw [← cA_eq, mulC_φ]
    refine List.mem_filter.mpr ⟨Btree.mem_toList hX, ?_⟩
    rw [hmul]
    exact hY
  let f : ↥(prodOneFibre (classTriple' 0) (classTriple' 1) zEl⁻¹) → ↥fibreList'.toFinset :=
    fun w => ⟨φ (((w : ↥M11) : Perm (Fin 11))), List.mem_toFinset.mpr (hmap w)⟩
  have hf : Function.Injective f := by
    intro u v huv
    have h1 : φ (((u : ↥M11) : Perm (Fin 11))) = φ (((v : ↥M11) : Perm (Fin 11))) :=
      congrArg Subtype.val huv
    exact Subtype.ext (Subtype.ext (φ_injective h1))
  calc Nat.card ↥(prodOneFibre (classTriple' 0) (classTriple' 1) zEl⁻¹)
      ≤ Nat.card ↥fibreList'.toFinset := Nat.card_le_card_of_injective f hf
    _ = fibreList'.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ fibreList'.length := List.toFinset_card_le _
    _ = 11 := fibreList'_length

/-- The `11`-cycle has order dividing eleven. -/
lemma zEl_pow_eleven : zEl ^ 11 = 1 := by
  apply Subtype.ext
  show m11a ^ 11 = 1
  exact m11a_pow_eq_one

theorem eleven_le_centralizer' :
    11 ≤ Nat.card ↥(Subgroup.centralizer ({zEl⁻¹} : Set ↥M11)) := by
  have hz11 : zEl⁻¹ ^ 11 = 1 := by rw [inv_pow, zEl_pow_eleven, inv_one]
  have hzne : zEl⁻¹ ≠ 1 := fun h =>
    m11a_ne_one (congrArg Subtype.val (inv_eq_one.mp h))
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have horder : orderOf zEl⁻¹ = 11 := orderOf_eq_prime hz11 hzne
  have hle : Subgroup.zpowers zEl⁻¹ ≤ Subgroup.centralizer ({zEl⁻¹} : Set ↥M11) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.mpr (by rintro m rfl; rfl)
  have hcard : Nat.card ↥(Subgroup.zpowers zEl⁻¹)
      ≤ Nat.card ↥(Subgroup.centralizer ({zEl⁻¹} : Set ↥M11)) :=
    Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle)
  rwa [Nat.card_zpowers, horder] at hcard

theorem xEl_mem_prodOneFibre' :
    xEl ∈ prodOneFibre (classTriple' 0) (classTriple' 1) zEl⁻¹ := ⟨rfl, by rw [inv_inv]; rfl⟩

/-- **The class triple `(2A, 4A, 11A)` is rigid in `M₁₁`.** -/
theorem rigid_triple' : Nat.card ↥(rigidTuples classTriple') = Nat.card ↥M11 :=
  rigid_of_card_prodOneFibre center_eq_bot gen_top' xEl_mem_prodOneFibre' classTriple'_two
    (le_trans card_prodOneFibre_le' eleven_le_centralizer')

/-! ### The cyclotomic orbit of the triple

The exponents coprime to `44 = 4 · 11` act on the triple by raising each entry to that power.  The
involution and the order-four entry are unmoved — `4A` is a rational class of `M₁₁` — while the
`11`-cycle is carried to `z` or to `z⁻¹` according as the exponent is a quadratic residue mod `11`
or not.  Both possibilities are rigid, by `rigid_triple` and `rigid_triple'`. -/

/-- A word in the standard generators conjugating the `11`-cycle to its cube. -/
def g0 : Perm (Fin 11) := m11b * m11a⁻¹ * m11a⁻¹ * m11a⁻¹ * m11b * m11a⁻¹ * m11b

lemma g0_mem : g0 ∈ M11 :=
  mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem m11b_mem (inv_mem m11a_mem))
    (inv_mem m11a_mem)) (inv_mem m11a_mem)) m11b_mem) (inv_mem m11a_mem)) m11b_mem

/-- The conjugator cubing the `11`-cycle, as an element of `M₁₁`. -/
def gEl : ↥M11 := ⟨g0, g0_mem⟩

/-- A word in the standard generators conjugating the order-four entry to its inverse. -/
def gy0 : Perm (Fin 11) := m11a * m11a * m11a * m11a * m11b * m11a

lemma gy0_mem : gy0 ∈ M11 :=
  mul_mem (mul_mem (mul_mem (mul_mem (mul_mem m11a_mem m11a_mem) m11a_mem) m11a_mem)
    m11b_mem) m11a_mem

/-- The conjugator inverting the order-four entry, as an element of `M₁₁`. -/
def gyEl : ↥M11 := ⟨gy0, gy0_mem⟩

/-- A word in the standard generators conjugating the mirror entry to the original one. -/
def gp0 : Perm (Fin 11) := m11a⁻¹ * m11b⁻¹ * m11a⁻¹ * m11a⁻¹ * m11a⁻¹

lemma gp0_mem : gp0 ∈ M11 :=
  mul_mem (mul_mem (mul_mem (mul_mem (inv_mem m11a_mem) (inv_mem m11b_mem))
    (inv_mem m11a_mem)) (inv_mem m11a_mem)) (inv_mem m11a_mem)

/-- The conjugator matching the two order-four entries, as an element of `M₁₁`. -/
def gpEl : ↥M11 := ⟨gp0, gp0_mem⟩

lemma conj_zEl_cube : gEl * zEl * gEl⁻¹ = zEl ^ 3 := by
  apply Subtype.ext
  show g0 * m11a * g0⁻¹ = m11a ^ 3
  decide

lemma conj_yEl_inv : gyEl * yEl * gyEl⁻¹ = yEl⁻¹ := by
  apply Subtype.ext
  show gy0 * (x0⁻¹ * m11a⁻¹) * gy0⁻¹ = (x0⁻¹ * m11a⁻¹)⁻¹
  decide

lemma conj_yEl' : gpEl * yEl' * gpEl⁻¹ = yEl := by
  apply Subtype.ext
  show gp0 * (x0⁻¹ * m11a) * gp0⁻¹ = x0⁻¹ * m11a⁻¹
  decide

/-- The two order-four entries are conjugate: `M₁₁` has a single class of elements of order
four. -/
lemma mk_yEl'_eq : ConjClasses.mk yEl' = ConjClasses.mk yEl :=
  ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨gpEl, conj_yEl'⟩)

/-- An exponent may be reduced modulo any exponent of the element. -/
lemma pow_mod_of_pow_eq_one {g : ↥M11} {m : ℕ} (hm : g ^ m = 1) (u : ℕ) : g ^ u = g ^ (u % m) := by
  conv_lhs => rw [← Nat.div_add_mod u m]
  rw [pow_add, pow_mul, hm, one_pow, one_mul]

/-- The involution has order dividing two. -/
lemma xEl_pow_two : xEl ^ 2 = 1 := by rw [pow_two]; exact xEl_sq

/-- The order-four entry has order dividing four. -/
lemma yEl_pow_four : yEl ^ 4 = 1 := by
  have h : yEl * yEl * (yEl * yEl) = 1 := Subtype.ext y0_pow_four
  calc yEl ^ 4 = yEl * yEl * (yEl * yEl) := by
        rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    _ = 1 := h

/-- The cube of the order-four entry is its inverse, hence in its own class. -/
lemma mk_yEl_cube : ConjClasses.mk (yEl ^ 3) = ConjClasses.mk yEl := by
  have h3 : yEl ^ 3 = yEl⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    calc yEl ^ 3 * yEl = yEl ^ 4 := by group
      _ = 1 := yEl_pow_four
  rw [h3]
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
classes `11A`, `11B`.**  The residues fall into the five squares `1, 3, 9, 5, 4`, which conjugation
by `g` cycles, and the five non-squares `10, 8, 2, 6, 7`, which it cycles as well. -/
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

/-- No prime dividing `44` divides an exponent prime to `44`. -/
lemma not_dvd_of_coprime {u p : ℕ} (hp : p.Prime) (hpd : p ∣ 44) (h : Nat.Coprime u 44) :
    ¬ p ∣ u :=
  hp.coprime_iff_not_dvd.mp (Nat.Coprime.coprime_dvd_right hpd h).symm

/-- **Every cyclotomic twist of the triple `(2A, 4A, 11B)` is rigid.**  The twist by an exponent
prime to `44` is either the triple itself or its mirror image. -/
theorem orbit_rigid (u : Fin 3 → ℕ) (hu : ∀ i, Nat.Coprime (u i) 44) :
    Nat.card ↥(rigidTuples fun i => ConjClasses.powClass (u i) (classTriple i))
      = Nat.card ↥M11 := by
  have hx : ConjClasses.powClass (u 0) (classTriple 0) = ConjClasses.mk xEl := by
    rw [classTriple_zero, ConjClasses.powClass_mk, pow_mod_of_pow_eq_one xEl_pow_two (u 0)]
    have h2 : ¬ (2 ∣ u 0) := not_dvd_of_coprime Nat.prime_two (by norm_num) (hu 0)
    rw [show u 0 % 2 = 1 by omega, pow_one]
  have hy : ConjClasses.powClass (u 1) (classTriple 1) = ConjClasses.mk yEl := by
    rw [classTriple_one, ConjClasses.powClass_mk, pow_mod_of_pow_eq_one yEl_pow_four (u 1)]
    have h2 : ¬ (2 ∣ u 1) := not_dvd_of_coprime Nat.prime_two (by norm_num) (hu 1)
    rcases (by omega : u 1 % 4 = 1 ∨ u 1 % 4 = 3) with h | h
    · rw [h, pow_one]
    · rw [h]; exact mk_yEl_cube
  have hz : ConjClasses.powClass (u 2) (classTriple 2) = ConjClasses.mk zEl ∨
      ConjClasses.powClass (u 2) (classTriple 2) = ConjClasses.mk zEl⁻¹ := by
    rw [classTriple_two, ConjClasses.powClass_mk]
    exact mk_zEl_pow_cases
      (not_dvd_of_coprime (by norm_num) (by norm_num) (hu 2))
  rcases hz with hz | hz
  · rw [show (fun i => ConjClasses.powClass (u i) (classTriple i)) = classTriple from ?_]
    · exact rigid_triple
    · funext i; fin_cases i
      exacts [hx, hy, hz]
  · rw [show (fun i => ConjClasses.powClass (u i) (classTriple i)) = classTriple' from ?_]
    · exact rigid_triple'
    · funext i; fin_cases i
      exacts [hx, hy.trans mk_yEl'_eq.symm, hz]

/-! ### `M₁₁` is a regular Galois group over a number field -/

/-- The prescribed classes are made of elements of order dividing `44`. -/
theorem order_dvd_fortyFour (i : Fin 3) (g : ↥M11) (hg : ConjClasses.mk g = classTriple i) :
    orderOf g ∣ 44 := by
  fin_cases i
  · rw [ConjClasses.orderOf_eq_of_mk_eq (h := xEl) hg]
    exact dvd_trans (orderOf_dvd_of_pow_eq_one xEl_pow_two) (by norm_num)
  · rw [ConjClasses.orderOf_eq_of_mk_eq (h := yEl) hg]
    exact dvd_trans (orderOf_dvd_of_pow_eq_one yEl_pow_four) (by norm_num)
  · rw [ConjClasses.orderOf_eq_of_mk_eq (h := zEl) hg]
    exact dvd_trans (orderOf_dvd_of_pow_eq_one zEl_pow_eleven) (by norm_num)

/-- The prescribed classes carry a generating product-one triple. -/
theorem rigidTuples_nonempty : (rigidTuples classTriple).Nonempty := by
  rcases Set.eq_empty_or_nonempty (rigidTuples classTriple) with h | h
  · exfalso
    have hcard := rigid_triple
    haveI : IsEmpty ↥(rigidTuples classTriple) := by rw [h]; infer_instance
    rw [Nat.card_of_isEmpty, M11_card] at hcard
    exact absurd hcard.symm (by norm_num)
  · exact h

/-- **`M₁₁` is a regular Galois group over a number field.**

The triple `(2A, 4A, 11B)` is rigid and generating and `M₁₁` is centerless, but the two classes of
`11`-cycles are irrational: the exponents prime to `11` interchange them.  The classes are
therefore stable only under an index-two subgroup of the cyclotomic action, and the rigidity method
descends the geometric cover not to `ℚ(T)` but to `K(T)` for the number field `K` that subgroup
cuts out. -/
theorem exists_regular_numberField :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K), IsRegularGaloisGroupOver K ↥M11 :=
  Rigidity.RET.Descent.exists_regular_numberField_of_orbitRigid (n := 44) classTriple
    (center_triv_iff_center_eq_bot.mpr center_eq_bot) order_dvd_fortyFour rigidTuples_nonempty
    orbit_rigid

end MathieuM11

end Rigidity

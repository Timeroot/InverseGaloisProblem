/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Solvable.Shafarevich.PCentralSpan

/-!
# Words for the layers of the descending `p`-central series

The generators of a layer of the descending `p`-central series are words: starting from a generator
of the group one alternately raises to the `p`-th power and takes a commutator with a generator.
Recording those instructions as a syntactic object, rather than only the element they produce,
attaches two numbers to a word.  Its *level* counts the instructions, and so names the layer the
word lands in; its *degree* is the multiset of generators the word actually involves, and has size
at most the level plus one, because only the commutator steps consume a generator.

The point of the degree is the behaviour of a word under rescaling of the generators.  Replacing
each generator `x i` by a power `x i ^ c i` multiplies the value of a word by the product of the
`c i` over its degree, up to a correction in the next layer down.  A word of level `n` is therefore
a monomial in the exponents of total degree at most `n + 1`, which is the shape of input a
Chevalley–Warning count asks for.

## Main definitions

* `InverseGalois.Shafarevich.LayerWord` — the syntax of a layer word.
* `InverseGalois.Shafarevich.LayerWord.level`, `InverseGalois.Shafarevich.LayerWord.deg`,
  `InverseGalois.Shafarevich.LayerWord.eval` — the level, the degree and the value of a word.

## Main results

* `InverseGalois.Shafarevich.LayerWord.eval_mem` — a word of level `n` lands in the `n`-th layer.
* `InverseGalois.Shafarevich.LayerWord.eval_pow_div_mem` — rescaling the generators multiplies the
  value of a word by the product of the scaling exponents over its degree, modulo the next layer,
  and `InverseGalois.Shafarevich.LayerWord.eval_comp_pow_div_mem` for the same statement when the
  generators are also relabelled.
* `InverseGalois.Shafarevich.layerGen_range` — the values of the words of level `n` are exactly the
  generators of the `n`-th layer.
* `InverseGalois.Shafarevich.pCentral_eq_closure_eval_sup` — those values generate the layer.

## Tags

p-central series, commutator calculus, Shafarevich's theorem, embedding problem
-/

universe u

namespace InverseGalois.Shafarevich

/-! ### Central corrections -/

section Center

variable {G : Type*} [Group G]

/-- A central element whose `n`-th power is trivial disappears from an `n`-th power. -/
theorem mul_pow_eq_pow_of_mem_center {z b : G} {n : ℕ} (hz : z ∈ Subgroup.center G)
    (hzn : z ^ n = 1) : (z * b) ^ n = b ^ n := by
  rw [Commute.mul_pow (Subgroup.mem_center_iff.mp hz b).symm, hzn, one_mul]

/-- A central factor disappears from the first argument of a commutator. -/
theorem commutatorElement_mul_left_of_mem_center {z b y : G} (hz : z ∈ Subgroup.center G) :
    ⁅z * b, y⁆ = ⁅b, y⁆ := by
  rw [commutatorElement_mul_left_of_commute (Subgroup.mem_center_iff.mp hz ⁅b, y⁆).symm,
    commutatorElement_eq_one_iff_commute.mpr (Subgroup.mem_center_iff.mp hz y).symm, mul_one]

/-- When a commutator is central, the commutator of powers is the corresponding power of the
commutator. -/
theorem commutatorElement_pow_pow_of_mem_center {a y : G} (h : ⁅a, y⁆ ∈ Subgroup.center G)
    (k m : ℕ) : ⁅a ^ k, y ^ m⁆ = ⁅a, y⁆ ^ (k * m) := by
  have hk : ⁅a ^ k, y⁆ = ⁅a, y⁆ ^ k :=
    commutatorElement_pow_left_of_commute (Subgroup.mem_center_iff.mp h a) k
  have hcy : Commute y ⁅a, y⁆ := Subgroup.mem_center_iff.mp h y
  have hy : Commute y ⁅a ^ k, y⁆ := by
    rw [hk]
    exact hcy.pow_right k
  rw [commutatorElement_pow_right_of_commute hy m, hk, ← pow_mul]

end Center

/-! ### Congruences between consecutive layers -/

section Congr

variable {P : Type*} [Group P]

private theorem div_mem_iff_mk'_eq {N : Subgroup P} [N.Normal] {a b : P} :
    a / b ∈ N ↔ QuotientGroup.mk' N a = QuotientGroup.mk' N b :=
  QuotientGroup.eq_iff_div_mem.symm

variable (p : ℕ)

/-- Each layer of the descending `p`-central series becomes central in the quotient by the next
layer. -/
theorem mk'_mem_center {n : ℕ} {z : P} (hz : z ∈ pCentral p P n) :
    QuotientGroup.mk' (pCentral p P (n + 1)) z ∈ Subgroup.center (P ⧸ pCentral p P (n + 1)) :=
  map_pCentral_le_center p n ⟨z, hz, rfl⟩

/-- Two elements that agree modulo one layer have `p`-th powers that agree modulo the next. -/
theorem pow_div_pow_mem {n : ℕ} {a b : P} (h : a / b ∈ pCentral p P (n + 1)) :
    a ^ p / b ^ p ∈ pCentral p P (n + 1 + 1) := by
  rw [div_mem_iff_mk'_eq]
  set π := QuotientGroup.mk' (pCentral p P (n + 1 + 1)) with hπ
  have hz : π (a / b) ∈ Subgroup.center (P ⧸ pCentral p P (n + 1 + 1)) := mk'_mem_center p h
  have hzp : π (a / b) ^ p = 1 := by
    rw [← map_pow, hπ, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact pow_mem_pCentral_succ p h
  have key : π a = π (a / b) * π b := by
    rw [← map_mul]
    congr 1
    simp
  rw [map_pow, map_pow, key, mul_pow_eq_pow_of_mem_center hz hzp]

/-- Two elements that agree modulo one layer have commutators that agree modulo the next. -/
theorem commutatorElement_div_mem {n : ℕ} {a b : P} (h : a / b ∈ pCentral p P (n + 1)) (y : P) :
    ⁅a, y⁆ / ⁅b, y⁆ ∈ pCentral p P (n + 1 + 1) := by
  rw [div_mem_iff_mk'_eq]
  set π := QuotientGroup.mk' (pCentral p P (n + 1 + 1)) with hπ
  have hz : π (a / b) ∈ Subgroup.center (P ⧸ pCentral p P (n + 1 + 1)) := mk'_mem_center p h
  have key : π a = π (a / b) * π b := by
    rw [← map_mul]
    congr 1
    simp
  rw [map_commutatorElement, map_commutatorElement, key,
    commutatorElement_mul_left_of_mem_center hz]

/-- Inside a layer the commutator is bilinear modulo the layer two steps down: the commutator of a
power with a power is the corresponding power of the commutator. -/
theorem commutatorElement_pow_pow_div_mem {n : ℕ} {a : P} (ha : a ∈ pCentral p P n) (y : P)
    (k m : ℕ) : ⁅a ^ k, y ^ m⁆ / ⁅a, y⁆ ^ (k * m) ∈ pCentral p P (n + 1 + 1) := by
  rw [div_mem_iff_mk'_eq]
  set π := QuotientGroup.mk' (pCentral p P (n + 1 + 1)) with hπ
  have hz : ⁅π a, π y⁆ ∈ Subgroup.center (P ⧸ pCentral p P (n + 1 + 1)) := by
    rw [← map_commutatorElement]
    exact mk'_mem_center p (commutatorElement_mem_pCentral_succ p ha y)
  simp only [map_commutatorElement, map_pow]
  exact commutatorElement_pow_pow_of_mem_center hz k m

end Congr

/-! ### The syntax of a layer word -/

/-- A **layer word** is a recipe for an element of a layer of the descending `p`-central series: it
starts at a generator, and at each further step either raises the element built so far to the
`p`-th power or takes its commutator with a generator. -/
inductive LayerWord (ι : Type u) : Type u
  | gen (i : ι) : LayerWord ι
  | pow (w : LayerWord ι) : LayerWord ι
  | comm (w : LayerWord ι) (i : ι) : LayerWord ι

namespace LayerWord

variable {ι : Type*} {κ : Type*} {P : Type*} {Q : Type*} [Group P] [Group Q]

/-- The number of steps in a layer word, which is the layer of the descending `p`-central series
that the word lands in. -/
def level : LayerWord ι → ℕ
  | .gen _ => 0
  | .pow w => w.level + 1
  | .comm w _ => w.level + 1

/-- The multiset of generators a layer word involves: a power step involves none, and a commutator
step involves the generator it commutes with. -/
def deg : LayerWord ι → Multiset ι
  | .gen i => {i}
  | .pow w => w.deg
  | .comm w i => i ::ₘ w.deg

/-- Relabelling the generators of a layer word. -/
def map (σ : ι → κ) : LayerWord ι → LayerWord κ
  | .gen i => .gen (σ i)
  | .pow w => .pow (w.map σ)
  | .comm w i => .comm (w.map σ) (σ i)

/-- The element a layer word produces when its generators are given the values `x`. -/
def eval (p : ℕ) (x : ι → P) : LayerWord ι → P
  | .gen i => x i
  | .pow w => w.eval p x ^ p
  | .comm w i => ⁅w.eval p x, x i⁆

@[simp] theorem level_gen (i : ι) : (LayerWord.gen i).level = 0 := rfl

@[simp] theorem level_pow (w : LayerWord ι) : w.pow.level = w.level + 1 := rfl

@[simp] theorem level_comm (w : LayerWord ι) (i : ι) : (w.comm i).level = w.level + 1 := rfl

@[simp] theorem deg_gen (i : ι) : (LayerWord.gen i).deg = {i} := rfl

@[simp] theorem deg_pow (w : LayerWord ι) : w.pow.deg = w.deg := rfl

@[simp] theorem deg_comm (w : LayerWord ι) (i : ι) : (w.comm i).deg = i ::ₘ w.deg := rfl

@[simp] theorem map_gen (σ : ι → κ) (i : ι) : (LayerWord.gen i).map σ = .gen (σ i) := rfl

@[simp] theorem map_pow (σ : ι → κ) (w : LayerWord ι) : w.pow.map σ = (w.map σ).pow := rfl

@[simp] theorem map_comm (σ : ι → κ) (w : LayerWord ι) (i : ι) :
    (w.comm i).map σ = (w.map σ).comm (σ i) := rfl

@[simp] theorem eval_gen (p : ℕ) (x : ι → P) (i : ι) : (LayerWord.gen i).eval p x = x i := rfl

@[simp] theorem eval_pow (p : ℕ) (x : ι → P) (w : LayerWord ι) :
    w.pow.eval p x = w.eval p x ^ p := rfl

@[simp] theorem eval_comm (p : ℕ) (x : ι → P) (w : LayerWord ι) (i : ι) :
    (w.comm i).eval p x = ⁅w.eval p x, x i⁆ := rfl

/-! ### Relabelling -/

@[simp] theorem level_map (σ : ι → κ) (w : LayerWord ι) : (w.map σ).level = w.level := by
  induction w with
  | gen i => rfl
  | pow w ih => simpa using ih
  | comm w i ih => simpa using ih

@[simp] theorem deg_map (σ : ι → κ) (w : LayerWord ι) : (w.map σ).deg = w.deg.map σ := by
  induction w with
  | gen i => simp
  | pow w ih => simpa using ih
  | comm w i ih => simp [ih]

@[simp] theorem eval_map (p : ℕ) (σ : ι → κ) (y : κ → P) (w : LayerWord ι) :
    (w.map σ).eval p y = w.eval p (y ∘ σ) := by
  induction w with
  | gen i => rfl
  | pow w ih => simp [ih]
  | comm w i ih => simp [ih]

/-- Evaluating a layer word commutes with a group homomorphism. -/
theorem map_eval (p : ℕ) (x : ι → P) (f : P →* Q) (w : LayerWord ι) :
    f (w.eval p x) = w.eval p (f ∘ x) := by
  induction w with
  | gen i => rfl
  | pow w ih => simp [ih]
  | comm w i ih => simp [ih, map_commutatorElement]

/-! ### Level and degree -/

/-- A layer word of level `n` produces an element of the `n`-th layer. -/
theorem eval_mem (p : ℕ) (x : ι → P) (w : LayerWord ι) : w.eval p x ∈ pCentral p P w.level := by
  induction w with
  | gen i => simp
  | pow w ih => exact pow_mem_pCentral_succ p ih
  | comm w i ih => exact commutatorElement_mem_pCentral_succ p ih (x i)

/-- The size of the degree of a layer word is at most its level plus one: only the commutator steps
consume a generator. -/
theorem card_deg_le (w : LayerWord ι) : Multiset.card w.deg ≤ w.level + 1 := by
  induction w with
  | gen i => simp
  | pow w ih => simpa using ih.trans (Nat.le_succ _)
  | comm w i ih => simpa using ih

/-- **Rescaling the generators of a layer word multiplies its value by the product of the scaling
exponents over its degree**, modulo the next layer. -/
theorem eval_pow_div_mem (p : ℕ) (x : ι → P) (c : ι → ℕ) (w : LayerWord ι) :
    (w.eval p fun j => x j ^ c j) / w.eval p x ^ (w.deg.map c).prod
      ∈ pCentral p P (w.level + 1) := by
  induction w with
  | gen i =>
    simp only [eval_gen, deg_gen, level_gen, Multiset.map_singleton, Multiset.prod_singleton,
      div_self']
    exact one_mem _
  | pow w ih =>
    simp only [eval_pow, deg_pow, level_pow]
    have h := pow_div_pow_mem p ih
    rwa [pow_right_comm] at h
  | comm w i ih =>
    simp only [eval_comm, deg_comm, level_comm, Multiset.map_cons, Multiset.prod_cons]
    set A := w.eval p x with hA
    set B := w.eval p fun j => x j ^ c j with hB
    set C := (Multiset.map c w.deg).prod with hC
    have h1 : ⁅B, x i ^ c i⁆ / ⁅A ^ C, x i ^ c i⁆ ∈ pCentral p P (w.level + 1 + 1) :=
      commutatorElement_div_mem p ih (x i ^ c i)
    have h2 : ⁅A ^ C, x i ^ c i⁆ / ⁅A, x i⁆ ^ (C * c i) ∈ pCentral p P (w.level + 1 + 1) :=
      commutatorElement_pow_pow_div_mem p (eval_mem p x w) (x i) C (c i)
    have h3 := mul_mem h1 h2
    rwa [div_mul_div_cancel, Nat.mul_comm C (c i)] at h3

/-- **Rescaling a relabelled family of generators.**  Substituting `y (σ j) ^ c j` for the `j`-th
generator multiplies the value of the relabelled word by the product of the scaling exponents over
the degree, modulo the next layer. -/
theorem eval_comp_pow_div_mem (p : ℕ) (σ : ι → κ) (y : κ → P) (c : ι → ℕ) (w : LayerWord ι) :
    (w.eval p fun j => y (σ j) ^ c j) / (w.map σ).eval p y ^ (w.deg.map c).prod
      ∈ pCentral p P (w.level + 1) := by
  have h := eval_pow_div_mem p (y ∘ σ) c w
  rwa [← eval_map p σ y w] at h

end LayerWord

/-! ### Layer words generate the layers -/

variable {ι : Type*} {P : Type*} [Group P]

/-- The generators of the `n`-th layer built from a family of generators of the group are exactly
the values of the layer words of level `n`. -/
theorem layerGen_range (p : ℕ) (x : ι → P) (n : ℕ) :
    layerGen p (Set.range x) n = {g : P | ∃ w : LayerWord ι, w.level = n ∧ w.eval p x = g} := by
  induction n with
  | zero =>
    ext g
    rw [layerGen_zero, Set.mem_range, Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨.gen i, rfl, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      cases w with
      | gen i => exact ⟨i, rfl⟩
      | pow v => simp at hw
      | comm v i => simp at hw
  | succ n ih =>
    ext g
    rw [layerGen_succ, ih]
    simp only [Set.mem_union, Set.mem_image, Set.mem_setOf_eq, Set.mem_range]
    constructor
    · rintro (⟨_, ⟨w, hw, rfl⟩, rfl⟩ | ⟨_, ⟨w, hw, rfl⟩, _, ⟨i, rfl⟩, rfl⟩)
      · exact ⟨.pow w, by simp [hw], rfl⟩
      · exact ⟨.comm w i, by simp [hw], rfl⟩
    · rintro ⟨w, hw, rfl⟩
      cases w with
      | gen i => simp at hw
      | pow v => exact Or.inl ⟨_, ⟨v, by simpa using hw, rfl⟩, rfl⟩
      | comm v i => exact Or.inr ⟨_, ⟨v, by simpa using hw, rfl⟩, _, ⟨i, rfl⟩, rfl⟩

/-- **Each layer of the descending `p`-central series is generated by the values of the layer words
of that level, together with the next layer.** -/
theorem pCentral_eq_closure_eval_sup (p : ℕ) {x : ι → P} (hx : Subgroup.closure (Set.range x) = ⊤)
    (n : ℕ) : pCentral p P n =
      Subgroup.closure {g : P | ∃ w : LayerWord ι, w.level = n ∧ w.eval p x = g} ⊔
        pCentral p P (n + 1) := by
  rw [← layerGen_range p x n]
  exact pCentral_eq_closure_layerGen_sup p hx n

end InverseGalois.Shafarevich

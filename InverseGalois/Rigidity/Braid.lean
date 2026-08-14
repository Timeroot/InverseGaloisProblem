/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Rigidity.StructureConstant

/-!
# The Hurwitz braid moves on generating product-one tuples

The tuples counted by a rigidity certificate — generating tuples of a finite group whose entries
lie in prescribed conjugacy classes and whose product is `1` — carry an action of the braid group
of the punctured sphere, the **Hurwitz action**.  Its generators are the moves

```
(…, a, b, …) ↦ (…, a * b * a⁻¹, a, …)
```

acting on two adjacent entries.  Geometrically these are the monodromy of a loop in the
configuration space of the branch points, so they permute the covers with a given branch behaviour
and act on the corresponding Nielsen class.  Group-theoretically each move preserves everything a
certificate records: the product of the entries, the subgroup they generate, and the multiset of
their conjugacy classes (only the *order* of the classes changes, by the adjacent transposition).

This file develops the moves and their algebra.  To avoid index juggling they are defined first on
`List G`, where a move is "recurse `n` steps into the list, then act on the head", and are
transported to tuples `Fin r → G` afterwards along `List.ofFn`.

## Main definitions

* `Rigidity.braid n`, `Rigidity.braidInv n` — the `n`-th Hurwitz move on lists, and its inverse.
* `Rigidity.braidTuple n`, `Rigidity.braidTupleInv n` — the same on `r`-tuples.
* `Rigidity.classMultiset` — the multiset of conjugacy classes of the entries of a tuple.
* `Rigidity.nielsenTuples C` — the Nielsen class: generating product-one tuples whose entries have
  the classes `C` in some order.
* `Rigidity.BraidGroup n` — the braid group on `n + 1` strands, presented by the braid relations.
* `Rigidity.hurwitz` — the Hurwitz action of `Rigidity.BraidGroup n` on `Fin (n + 1) → G`.

## Main results

* `Rigidity.prod_braid`, `Rigidity.closure_braid`, `Rigidity.perm_map_mk_braid` — a move preserves
  the product, the generated subgroup, and the multiset of conjugacy classes.
* `Rigidity.braid_comm`, `Rigidity.braid_braid_braid` — the braid relations: moves at distance at
  least two commute, and adjacent moves satisfy `QᵢQᵢ₊₁Qᵢ = Qᵢ₊₁QᵢQᵢ₊₁`.
* `Rigidity.braid_map_conj` — the moves commute with simultaneous conjugation.
* `Rigidity.braidTuple_mem_nielsenTuples`, `Rigidity.hurwitz_mem_nielsenTuples` — the moves, and
  the whole braid group, act on the Nielsen class.
* `Rigidity.mem_nielsenTuples_iff` — membership in the Nielsen class in terms of the multiset of
  conjugacy classes, using `Rigidity.exists_perm_of_tupleMultiset_eq`.
* `Rigidity.braidConj_of_rigidityCertificate` — for a rigidity certificate the whole Nielsen class
  is a single orbit of the braid moves together with simultaneous conjugation.
-/

namespace Rigidity

variable {G : Type*} [Group G]

/-! ### The move on lists -/

/-- The Hurwitz move on the first two entries of a list: `a :: b :: t ↦ a * b * a⁻¹ :: a :: t`. -/
def braidHd : List G → List G
  | a :: b :: t => (a * b * a⁻¹) :: a :: t
  | l => l

/-- The inverse of `Rigidity.braidHd`. -/
def braidHdInv : List G → List G
  | a :: b :: t => b :: (b⁻¹ * a * b) :: t
  | l => l

@[simp] theorem braidHd_nil : braidHd ([] : List G) = [] := rfl

@[simp] theorem braidHd_singleton (a : G) : braidHd [a] = [a] := rfl

@[simp] theorem braidHd_cons_cons (a b : G) (t : List G) :
    braidHd (a :: b :: t) = (a * b * a⁻¹) :: a :: t := rfl

@[simp] theorem braidHdInv_nil : braidHdInv ([] : List G) = [] := rfl

@[simp] theorem braidHdInv_singleton (a : G) : braidHdInv [a] = [a] := rfl

@[simp] theorem braidHdInv_cons_cons (a b : G) (t : List G) :
    braidHdInv (a :: b :: t) = b :: (b⁻¹ * a * b) :: t := rfl

theorem length_braidHd (l : List G) : (braidHd l).length = l.length := by
  match l with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl

theorem length_braidHdInv (l : List G) : (braidHdInv l).length = l.length := by
  match l with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl

theorem prod_braidHd (l : List G) : (braidHd l).prod = l.prod := by
  match l with
  | [] => rfl
  | [_] => rfl
  | a :: b :: t => simp [mul_assoc]

theorem braidHdInv_braidHd (l : List G) : braidHdInv (braidHd l) = l := by
  match l with
  | [] => rfl
  | [_] => rfl
  | a :: b :: t => simp [mul_assoc]

theorem braidHd_braidHdInv (l : List G) : braidHd (braidHdInv l) = l := by
  match l with
  | [] => rfl
  | [_] => rfl
  | a :: b :: t => simp [mul_assoc]

/-- The `n`-th Hurwitz move: act on the entries in positions `n` and `n + 1`. -/
def braid (n : ℕ) (l : List G) : List G := l.take n ++ braidHd (l.drop n)

/-- The inverse of the `n`-th Hurwitz move. -/
def braidInv (n : ℕ) (l : List G) : List G := l.take n ++ braidHdInv (l.drop n)

@[simp] theorem braid_zero (l : List G) : braid 0 l = braidHd l := by simp [braid]

@[simp] theorem braidInv_zero (l : List G) : braidInv 0 l = braidHdInv l := by simp [braidInv]

@[simp] theorem braid_nil (n : ℕ) : braid n ([] : List G) = [] := by simp [braid]

@[simp] theorem braidInv_nil (n : ℕ) : braidInv n ([] : List G) = [] := by simp [braidInv]

theorem braid_succ_cons (n : ℕ) (a : G) (l : List G) :
    braid (n + 1) (a :: l) = a :: braid n l := by
  simp [braid]

theorem braidInv_succ_cons (n : ℕ) (a : G) (l : List G) :
    braidInv (n + 1) (a :: l) = a :: braidInv n l := by
  simp [braidInv]

theorem length_braid (n : ℕ) (l : List G) : (braid n l).length = l.length := by
  simp only [braid, List.length_append, length_braidHd, List.length_take, List.length_drop]
  omega

theorem length_braidInv (n : ℕ) (l : List G) : (braidInv n l).length = l.length := by
  simp only [braidInv, List.length_append, length_braidHdInv, List.length_take, List.length_drop]
  omega

theorem prod_braid (n : ℕ) (l : List G) : (braid n l).prod = l.prod := by
  rw [braid, List.prod_append, prod_braidHd, ← List.prod_append, List.take_append_drop]

theorem braidInv_braid (n : ℕ) (l : List G) : braidInv n (braid n l) = l := by
  induction n generalizing l with
  | zero => simpa using braidHdInv_braidHd l
  | succ n ih =>
      match l with
      | [] => simp
      | a :: l => rw [braid_succ_cons, braidInv_succ_cons, ih]

theorem braid_braidInv (n : ℕ) (l : List G) : braid n (braidInv n l) = l := by
  induction n generalizing l with
  | zero => simpa using braidHd_braidHdInv l
  | succ n ih =>
      match l with
      | [] => simp
      | a :: l => rw [braidInv_succ_cons, braid_succ_cons, ih]

theorem braid_injective (n : ℕ) : Function.Injective (braid n : List G → List G) :=
  Function.LeftInverse.injective (braidInv_braid n)

/-- A move beyond the end of a list does nothing. -/
theorem braid_of_length_le {n : ℕ} {l : List G} (h : l.length ≤ n + 1) : braid n l = l := by
  have hd : (l.drop n).length ≤ 1 := by simp; omega
  have : braidHd (l.drop n) = l.drop n := by
    match hl : l.drop n with
    | [] => rfl
    | [_] => rfl
    | _ :: _ :: _ => rw [hl] at hd; simp at hd
  rw [braid, this, List.take_append_drop]

theorem prod_braidInv (n : ℕ) (l : List G) : (braidInv n l).prod = l.prod := by
  conv_rhs => rw [← braid_braidInv n l]
  rw [prod_braid]

theorem braidInv_of_length_le {n : ℕ} {l : List G} (h : l.length ≤ n + 1) : braidInv n l = l := by
  conv_rhs => rw [← braid_braidInv n l]
  exact (braid_of_length_le (by rwa [length_braidInv])).symm

/-! ### Entries of a moved list -/

theorem getElem_braid_of_lt {n : ℕ} {l : List G} {i : ℕ} (hi : i < n)
    (h : i < (braid n l).length) : (braid n l)[i] = l[i]'(by rwa [length_braid] at h) := by
  induction n generalizing l i with
  | zero => omega
  | succ n ih =>
      match l, i with
      | [], _ => rw [length_braid] at h; simp at h
      | a :: l, 0 => simp only [braid_succ_cons, List.getElem_cons_zero]
      | a :: l, i + 1 =>
          simp only [braid_succ_cons, List.getElem_cons_succ]
          exact ih (by omega) _

theorem getElem_braid_of_gt {n : ℕ} {l : List G} {i : ℕ} (hi : n + 1 < i)
    (h : i < (braid n l).length) : (braid n l)[i] = l[i]'(by rwa [length_braid] at h) := by
  induction n generalizing l i with
  | zero =>
      match l, i with
      | [], _ => rw [length_braid] at h; simp at h
      | [_], _ => rw [length_braid] at h; simp at h; omega
      | _ :: _ :: _, 0 => omega
      | _ :: _ :: _, 1 => omega
      | a :: b :: t, i + 2 =>
          simp only [braid_zero, braidHd_cons_cons, List.getElem_cons_succ]
  | succ n ih =>
      match l, i with
      | [], _ => rw [length_braid] at h; simp at h
      | _ :: _, 0 => omega
      | a :: l, i + 1 =>
          simp only [braid_succ_cons, List.getElem_cons_succ]
          exact ih (by omega) _

theorem getElem_braid_self {n : ℕ} {l : List G} (h : n + 1 < l.length) :
    (braid n l)[n]'(by rw [length_braid]; omega) = l[n] * l[n + 1] * (l[n])⁻¹ := by
  induction n generalizing l with
  | zero =>
      match l with
      | [] => simp at h
      | [_] => simp at h
      | a :: b :: t =>
          simp only [braid_zero, braidHd_cons_cons, List.getElem_cons_zero,
            List.getElem_cons_succ]
  | succ n ih =>
      match l with
      | [] => simp at h
      | a :: l =>
          simp only [braid_succ_cons, List.getElem_cons_succ]
          exact ih (by simpa using h)

theorem getElem_braid_succ {n : ℕ} {l : List G} (h : n + 1 < l.length) :
    (braid n l)[n + 1]'(by rw [length_braid]; omega) = l[n] := by
  induction n generalizing l with
  | zero =>
      match l with
      | [] => simp at h
      | [_] => simp at h
      | a :: b :: t =>
          simp only [braid_zero, braidHd_cons_cons, List.getElem_cons_zero,
            List.getElem_cons_succ]
  | succ n ih =>
      match l with
      | [] => simp at h
      | a :: l =>
          simp only [braid_succ_cons, List.getElem_cons_succ]
          exact ih (by simpa using h)

/-! ### What a move preserves -/

omit [Group G] in
theorem setOf_mem_append (l₁ l₂ : List G) :
    {x : G | x ∈ l₁ ++ l₂} = {x | x ∈ l₁} ∪ {x | x ∈ l₂} := by
  ext x; simp

theorem closure_braidHd (l : List G) :
    Subgroup.closure {x : G | x ∈ braidHd l} = Subgroup.closure {x : G | x ∈ l} := by
  match l with
  | [] => rfl
  | [_] => rfl
  | a :: b :: t =>
      refine le_antisymm (Subgroup.closure_le _ |>.2 fun x hx => ?_)
        (Subgroup.closure_le _ |>.2 fun x hx => ?_)
      · simp only [braidHd_cons_cons, Set.mem_setOf_eq, List.mem_cons] at hx
        have ha : a ∈ Subgroup.closure {x : G | x ∈ a :: b :: t} :=
          Subgroup.subset_closure (by simp)
        have hb : b ∈ Subgroup.closure {x : G | x ∈ a :: b :: t} :=
          Subgroup.subset_closure (by simp)
        rcases hx with rfl | rfl | hx
        · exact mul_mem (mul_mem ha hb) (inv_mem ha)
        · exact ha
        · exact Subgroup.subset_closure (by simp [hx])
      · simp only [Set.mem_setOf_eq, List.mem_cons] at hx
        have ha : a ∈ Subgroup.closure {x : G | x ∈ braidHd (a :: b :: t)} :=
          Subgroup.subset_closure (by simp)
        have hc : a * b * a⁻¹ ∈ Subgroup.closure {x : G | x ∈ braidHd (a :: b :: t)} :=
          Subgroup.subset_closure (by simp)
        rcases hx with rfl | rfl | hx
        · exact ha
        · have hmem := mul_mem (mul_mem (inv_mem ha) hc) ha
          rwa [show a⁻¹ * (a * x * a⁻¹) * a = x by group] at hmem
        · exact Subgroup.subset_closure (by simp [hx])

theorem closure_braid (n : ℕ) (l : List G) :
    Subgroup.closure {x : G | x ∈ braid n l} = Subgroup.closure {x : G | x ∈ l} := by
  conv_rhs => rw [← List.take_append_drop n l]
  rw [braid, setOf_mem_append, setOf_mem_append, Subgroup.closure_union, Subgroup.closure_union,
    closure_braidHd]

theorem closure_braidInv (n : ℕ) (l : List G) :
    Subgroup.closure {x : G | x ∈ braidInv n l} = Subgroup.closure {x : G | x ∈ l} := by
  conv_rhs => rw [← braid_braidInv n l]
  rw [closure_braid]

theorem perm_map_mk_braidHd (l : List G) :
    ((braidHd l).map ConjClasses.mk).Perm (l.map ConjClasses.mk) := by
  match l with
  | [] => exact List.Perm.refl _
  | [_] => exact List.Perm.refl _
  | a :: b :: t =>
      have h : ConjClasses.mk (a * b * a⁻¹) = ConjClasses.mk b :=
        ConjClasses.mk_eq_mk_iff_isConj.2 (isConj_iff.2 ⟨a⁻¹, by group⟩)
      simp only [braidHd_cons_cons, List.map_cons, h]
      exact List.Perm.swap _ _ _

theorem perm_map_mk_braid (n : ℕ) (l : List G) :
    ((braid n l).map ConjClasses.mk).Perm (l.map ConjClasses.mk) := by
  conv_rhs => rw [← List.take_append_drop n l]
  rw [braid, List.map_append, List.map_append]
  exact (perm_map_mk_braidHd _).append_left _

theorem perm_map_mk_braidInv (n : ℕ) (l : List G) :
    ((braidInv n l).map ConjClasses.mk).Perm (l.map ConjClasses.mk) := by
  conv_rhs => rw [← braid_braidInv n l]
  exact (perm_map_mk_braid n (braidInv n l)).symm

theorem braidHd_map_conj (c : G) (l : List G) :
    braidHd (l.map fun x => c * x * c⁻¹) = (braidHd l).map fun x => c * x * c⁻¹ := by
  match l with
  | [] => rfl
  | [_] => rfl
  | a :: b :: t => simp only [List.map_cons, braidHd_cons_cons, List.cons.injEq, and_true]; group

theorem braid_map_conj (n : ℕ) (c : G) (l : List G) :
    braid n (l.map fun x => c * x * c⁻¹) = (braid n l).map fun x => c * x * c⁻¹ := by
  simp only [braid, List.map_append, ← List.map_take, ← List.map_drop, braidHd_map_conj]

/-! ### The braid relations -/

/-- Moves at distance at least two commute. -/
theorem braid_comm {m n : ℕ} (h : n + 2 ≤ m) (l : List G) :
    braid n (braid m l) = braid m (braid n l) := by
  induction n generalizing m l with
  | zero =>
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
      match l with
      | [] => simp
      | [a] => simp [braid_succ_cons]
      | a :: b :: t =>
          rw [braid_succ_cons, braid_succ_cons, braid_zero, braid_zero, braidHd_cons_cons,
            braidHd_cons_cons, braid_succ_cons, braid_succ_cons]
  | succ n ih =>
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      match l with
      | [] => simp
      | a :: l =>
          rw [braid_succ_cons, braid_succ_cons, braid_succ_cons, braid_succ_cons,
            ih (by omega)]

/-- The braid relation `QₙQₙ₊₁Qₙ = Qₙ₊₁QₙQₙ₊₁`. -/
theorem braid_braid_braid {n : ℕ} {l : List G} (hl : n + 3 ≤ l.length) :
    braid n (braid (n + 1) (braid n l)) = braid (n + 1) (braid n (braid (n + 1) l)) := by
  induction n generalizing l with
  | zero =>
      match l with
      | [] => simp at hl
      | [_] => simp at hl
      | [_, _] => simp at hl
      | a :: b :: c :: t =>
          simp only [Nat.zero_add, braid_zero, braidHd_cons_cons, braid_succ_cons,
            List.cons.injEq, and_true]
          group
  | succ n ih =>
      match l with
      | [] => simp at hl
      | a :: l =>
          rw [braid_succ_cons, braid_succ_cons, braid_succ_cons, braid_succ_cons,
            braid_succ_cons, braid_succ_cons, ih (by simpa using hl)]

/-! ### The move on tuples -/

/-- The multiset of entries of a tuple. -/
def tupleMultiset {α : Type*} {r : ℕ} (f : Fin r → α) : Multiset α := ↑(List.ofFn f)

/-- The multiset of conjugacy classes of the entries of a tuple. -/
def classMultiset {r : ℕ} (g : Fin r → G) : Multiset (ConjClasses G) :=
  (tupleMultiset g).map ConjClasses.mk

/-- The `n`-th Hurwitz move on `r`-tuples. -/
def braidTuple {r : ℕ} (n : ℕ) (g : Fin r → G) : Fin r → G := fun i =>
  (braid n (List.ofFn g))[(i : ℕ)]'(by rw [length_braid, List.length_ofFn]; exact i.2)

/-- The inverse of the `n`-th Hurwitz move on `r`-tuples. -/
def braidTupleInv {r : ℕ} (n : ℕ) (g : Fin r → G) : Fin r → G := fun i =>
  (braidInv n (List.ofFn g))[(i : ℕ)]'(by rw [length_braidInv, List.length_ofFn]; exact i.2)

@[simp] theorem ofFn_braidTuple {r : ℕ} (n : ℕ) (g : Fin r → G) :
    List.ofFn (braidTuple n g) = braid n (List.ofFn g) := by
  refine List.ext_getElem (by simp [length_braid]) fun i h₁ h₂ => ?_
  simp [braidTuple]

@[simp] theorem ofFn_braidTupleInv {r : ℕ} (n : ℕ) (g : Fin r → G) :
    List.ofFn (braidTupleInv n g) = braidInv n (List.ofFn g) := by
  refine List.ext_getElem (by simp [length_braidInv]) fun i h₁ h₂ => ?_
  simp [braidTupleInv]

theorem braidTupleInv_braidTuple {r : ℕ} (n : ℕ) (g : Fin r → G) :
    braidTupleInv n (braidTuple n g) = g :=
  List.ofFn_injective (by rw [ofFn_braidTupleInv, ofFn_braidTuple, braidInv_braid])

theorem braidTuple_braidTupleInv {r : ℕ} (n : ℕ) (g : Fin r → G) :
    braidTuple n (braidTupleInv n g) = g :=
  List.ofFn_injective (by rw [ofFn_braidTuple, ofFn_braidTupleInv, braid_braidInv])

theorem braidTuple_injective {r : ℕ} (n : ℕ) :
    Function.Injective (braidTuple n : (Fin r → G) → Fin r → G) :=
  Function.LeftInverse.injective (braidTupleInv_braidTuple n)

theorem prod_ofFn_braidTuple {r : ℕ} (n : ℕ) (g : Fin r → G) :
    (List.ofFn (braidTuple n g)).prod = (List.ofFn g).prod := by
  rw [ofFn_braidTuple, prod_braid]

theorem closure_range_braidTuple {r : ℕ} (n : ℕ) (g : Fin r → G) :
    Subgroup.closure (Set.range (braidTuple n g)) = Subgroup.closure (Set.range g) := by
  have h : ∀ f : Fin r → G, Set.range f = {x : G | x ∈ List.ofFn f} := by
    intro f; ext x; simp
  rw [h, h, ofFn_braidTuple, closure_braid]

theorem classMultiset_braidTuple {r : ℕ} (n : ℕ) (g : Fin r → G) :
    classMultiset (braidTuple n g) = classMultiset g := by
  rw [classMultiset, classMultiset, tupleMultiset, tupleMultiset, ofFn_braidTuple]
  exact Quot.sound (perm_map_mk_braid n (List.ofFn g))

theorem ofFn_conj {r : ℕ} (c : G) (g : Fin r → G) :
    List.ofFn (fun i => c * g i * c⁻¹) = (List.ofFn g).map fun x => c * x * c⁻¹ := by
  rw [List.map_ofFn]; rfl

/-- The moves commute with simultaneous conjugation. -/
theorem braidTuple_conj {r : ℕ} (n : ℕ) (c : G) (g : Fin r → G) :
    braidTuple n (fun i => c * g i * c⁻¹) = fun i => c * braidTuple n g i * c⁻¹ :=
  List.ofFn_injective (by
    rw [ofFn_braidTuple, ofFn_conj, ofFn_conj, ofFn_braidTuple, braid_map_conj])

theorem braidTuple_comm {r m n : ℕ} (h : n + 2 ≤ m) (g : Fin r → G) :
    braidTuple n (braidTuple m g) = braidTuple m (braidTuple n g) :=
  List.ofFn_injective (by
    rw [ofFn_braidTuple, ofFn_braidTuple, ofFn_braidTuple, ofFn_braidTuple, braid_comm h])

theorem braidTuple_braidTuple_braidTuple {r n : ℕ} (hr : n + 3 ≤ r) (g : Fin r → G) :
    braidTuple n (braidTuple (n + 1) (braidTuple n g))
      = braidTuple (n + 1) (braidTuple n (braidTuple (n + 1) g)) :=
  List.ofFn_injective (by
    simp only [ofFn_braidTuple]
    exact braid_braid_braid (by simpa using hr))

/-- A move beyond the end of a tuple does nothing. -/
theorem braidTuple_of_le {r n : ℕ} (hr : r ≤ n + 1) (g : Fin r → G) : braidTuple n g = g :=
  List.ofFn_injective (by
    rw [ofFn_braidTuple, braid_of_length_le (by simpa using hr)])

/-- Away from the two moved positions, `braidTuple n g` agrees with `g`. -/
theorem braidTuple_apply_of_ne {r n : ℕ} (g : Fin r → G) (i : Fin r)
    (h₁ : (i : ℕ) ≠ n) (h₂ : (i : ℕ) ≠ n + 1) : braidTuple n g i = g i := by
  rcases lt_or_gt_of_ne h₁ with hi | hi
  · rw [braidTuple, getElem_braid_of_lt hi]
    simp
  · rw [braidTuple, getElem_braid_of_gt (by omega)]
    simp

/-- At the position `n`, `braidTuple n g` is a conjugate of the next entry. -/
theorem braidTuple_apply_self {r n : ℕ} (g : Fin r → G) (hn : n + 1 < r) :
    braidTuple n g ⟨n, by omega⟩
      = g ⟨n, by omega⟩ * g ⟨n + 1, hn⟩ * (g ⟨n, by omega⟩)⁻¹ := by
  rw [braidTuple, getElem_braid_self (by simpa using hn)]
  simp

/-- At the position `n + 1`, `braidTuple n g` is the previous entry. -/
theorem braidTuple_apply_succ {r n : ℕ} (g : Fin r → G) (hn : n + 1 < r) :
    braidTuple n g ⟨n + 1, hn⟩ = g ⟨n, by omega⟩ := by
  rw [braidTuple, getElem_braid_succ (by simpa using hn)]
  simp

/-- A move transposes the two adjacent conjugacy classes and leaves the others alone. -/
theorem mk_braidTuple_apply {r n : ℕ} (hn : n + 1 < r) (g : Fin r → G) (i : Fin r) :
    ConjClasses.mk (braidTuple n g i)
      = ConjClasses.mk (g (Equiv.swap (⟨n, by omega⟩ : Fin r) ⟨n + 1, hn⟩ i)) := by
  have hnr : n < r := Nat.lt_of_succ_lt hn
  by_cases h₁ : (i : ℕ) = n
  · have hi : i = (⟨n, hnr⟩ : Fin r) := Fin.ext h₁
    subst hi
    rw [braidTuple_apply_self g hn, Equiv.swap_apply_left]
    exact ConjClasses.mk_eq_mk_iff_isConj.2 (isConj_iff.2 ⟨(g ⟨n, hnr⟩)⁻¹, by group⟩)
  · by_cases h₂ : (i : ℕ) = n + 1
    · have hi : i = (⟨n + 1, hn⟩ : Fin r) := Fin.ext h₂
      subst hi
      rw [braidTuple_apply_succ g hn, Equiv.swap_apply_right]
    · rw [braidTuple_apply_of_ne g i h₁ h₂,
        Equiv.swap_apply_of_ne_of_ne (fun h => h₁ (by rw [h])) (fun h => h₂ (by rw [h]))]

/-! ### The Nielsen class -/

/-- Two tuples with the same multiset of entries differ by a permutation of the positions. -/
theorem exists_perm_of_tupleMultiset_eq {α : Type*} {r : ℕ} {f g : Fin r → α}
    (h : tupleMultiset f = tupleMultiset g) : ∃ σ : Equiv.Perm (Fin r), ∀ i, f (σ i) = g i := by
  classical
  have hcard : ∀ a : α,
      Fintype.card {i : Fin r // g i = a} = Fintype.card {i : Fin r // f i = a} := by
    intro a
    have h' : Multiset.count a (Finset.univ.val.map f)
        = Multiset.count a (Finset.univ.val.map g) := by
      rw [Fin.univ_val_map, Fin.univ_val_map]
      exact congrArg (Multiset.count a) h
    rw [Multiset.count_map, Multiset.count_map] at h'
    simp only [Fintype.card_subtype, Finset.card, Finset.filter_val]
    rw [Multiset.filter_congr (fun i _ => eq_comm (a := g i) (b := a)),
      Multiset.filter_congr (fun i _ => eq_comm (a := f i) (b := a)), ← h']
  let e : ∀ a : α, {i : Fin r // g i = a} ≃ {i : Fin r // f i = a} := fun a =>
    Fintype.equivOfCardEq (hcard a)
  refine ⟨(Equiv.sigmaFiberEquiv g).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv f)), fun i => ?_⟩
  simpa using (e (g i) ⟨i, rfl⟩).2

/-- The **Nielsen class** of a tuple `C` of conjugacy classes: the generating product-one tuples
whose entries have the classes `C`, in some order. -/
def nielsenTuples {r : ℕ} (C : Fin r → ConjClasses G) : Set (Fin r → G) :=
  { g | (∃ σ : Equiv.Perm (Fin r), ∀ i, ConjClasses.mk (g i) = C (σ i)) ∧
        (List.ofFn g).prod = 1 ∧ Subgroup.closure (Set.range g) = ⊤ }

theorem rigidTuples_subset_nielsenTuples {r : ℕ} (C : Fin r → ConjClasses G) :
    rigidTuples C ⊆ nielsenTuples C := by
  rintro g ⟨hC, hp, hgen⟩
  exact ⟨⟨1, fun i => hC i⟩, hp, hgen⟩

theorem classMultiset_eq_of_mem_nielsenTuples {r : ℕ} {C : Fin r → ConjClasses G} {g : Fin r → G}
    (hg : g ∈ nielsenTuples C) : classMultiset g = tupleMultiset C := by
  obtain ⟨⟨σ, hσ⟩, -, -⟩ := hg
  have h : ((List.ofFn g).map ConjClasses.mk).Perm (List.ofFn C) := by
    have : (List.ofFn g).map ConjClasses.mk = List.ofFn (C ∘ σ) := by
      rw [List.map_ofFn]; exact congrArg List.ofFn (funext hσ)
    rw [this]
    exact σ.ofFn_comp_perm C
  exact Quot.sound h

/-- The Hurwitz moves act on the Nielsen class. -/
theorem braidTuple_mem_nielsenTuples {r : ℕ} {C : Fin r → ConjClasses G} (n : ℕ) {g : Fin r → G}
    (hg : g ∈ nielsenTuples C) : braidTuple n g ∈ nielsenTuples C := by
  obtain ⟨⟨σ, hσ⟩, hp, hgen⟩ := hg
  refine ⟨?_, (prod_ofFn_braidTuple n g).trans hp, (closure_range_braidTuple n g).trans hgen⟩
  by_cases hn : n + 1 < r
  · refine ⟨σ * Equiv.swap (⟨n, by omega⟩ : Fin r) ⟨n + 1, hn⟩, fun i => ?_⟩
    rw [mk_braidTuple_apply hn g i, hσ]
    rfl
  · rw [braidTuple_of_le (by omega) g]
    exact ⟨σ, hσ⟩

theorem prod_ofFn_braidTupleInv {r : ℕ} (n : ℕ) (g : Fin r → G) :
    (List.ofFn (braidTupleInv n g)).prod = (List.ofFn g).prod := by
  rw [ofFn_braidTupleInv, prod_braidInv]

theorem closure_range_braidTupleInv {r : ℕ} (n : ℕ) (g : Fin r → G) :
    Subgroup.closure (Set.range (braidTupleInv n g)) = Subgroup.closure (Set.range g) := by
  have h : ∀ f : Fin r → G, Set.range f = {x : G | x ∈ List.ofFn f} := by
    intro f; ext x; simp
  rw [h, h, ofFn_braidTupleInv, closure_braidInv]

theorem braidTupleInv_of_le {r n : ℕ} (hr : r ≤ n + 1) (g : Fin r → G) : braidTupleInv n g = g :=
  List.ofFn_injective (by
    rw [ofFn_braidTupleInv, braidInv_of_length_le (by simpa using hr)])

theorem mk_braidTupleInv_apply {r n : ℕ} (hn : n + 1 < r) (g : Fin r → G) (i : Fin r) :
    ConjClasses.mk (braidTupleInv n g i)
      = ConjClasses.mk (g (Equiv.swap (⟨n, by omega⟩ : Fin r) ⟨n + 1, hn⟩ i)) := by
  have h := mk_braidTuple_apply hn (braidTupleInv n g)
    (Equiv.swap (⟨n, by omega⟩ : Fin r) ⟨n + 1, hn⟩ i)
  rw [braidTuple_braidTupleInv, Equiv.swap_apply_self] at h
  exact h.symm

theorem braidTupleInv_mem_nielsenTuples {r : ℕ} {C : Fin r → ConjClasses G} (n : ℕ)
    {g : Fin r → G} (hg : g ∈ nielsenTuples C) : braidTupleInv n g ∈ nielsenTuples C := by
  obtain ⟨⟨σ, hσ⟩, hp, hgen⟩ := hg
  refine ⟨?_, (prod_ofFn_braidTupleInv n g).trans hp,
    (closure_range_braidTupleInv n g).trans hgen⟩
  by_cases hn : n + 1 < r
  · refine ⟨σ * Equiv.swap (⟨n, by omega⟩ : Fin r) ⟨n + 1, hn⟩, fun i => ?_⟩
    rw [mk_braidTupleInv_apply hn g i, hσ]
    rfl
  · rw [braidTupleInv_of_le (by omega) g]
    exact ⟨σ, hσ⟩


/-- Membership in the Nielsen class, in terms of the multiset of classes. -/
theorem mem_nielsenTuples_iff {r : ℕ} {C : Fin r → ConjClasses G} {g : Fin r → G} :
    g ∈ nielsenTuples C ↔ classMultiset g = tupleMultiset C ∧ (List.ofFn g).prod = 1 ∧
      Subgroup.closure (Set.range g) = ⊤ := by
  refine ⟨fun hg => ⟨classMultiset_eq_of_mem_nielsenTuples hg, hg.2.1, hg.2.2⟩, ?_⟩
  rintro ⟨hM, hp, hgen⟩
  have hM' : tupleMultiset (fun i => ConjClasses.mk (g i)) = tupleMultiset C := by
    rw [← hM, classMultiset, tupleMultiset, tupleMultiset, Multiset.map_coe, List.map_ofFn]
    rfl
  obtain ⟨σ, hσ⟩ := exists_perm_of_tupleMultiset_eq hM'
  refine ⟨⟨σ⁻¹, fun i => ?_⟩, hp, hgen⟩
  have := hσ (σ⁻¹ i)
  simpa using this

/-! ### The braid-and-conjugation equivalence -/

/-- One elementary move on tuples: a Hurwitz move, its inverse, or a simultaneous conjugation. -/
inductive BraidConjStep {r : ℕ} : (Fin r → G) → (Fin r → G) → Prop
  | braid (n : ℕ) (g : Fin r → G) : BraidConjStep g (braidTuple n g)
  | braidInv (n : ℕ) (g : Fin r → G) : BraidConjStep g (braidTupleInv n g)
  | conj (c : G) (g : Fin r → G) : BraidConjStep g fun i => c * g i * c⁻¹

/-- Two tuples are **braid-and-conjugation equivalent** if one can be reached from the other by
Hurwitz moves and simultaneous conjugations. -/
def BraidConj {r : ℕ} : (Fin r → G) → (Fin r → G) → Prop :=
  Relation.ReflTransGen BraidConjStep

theorem BraidConj.refl {r : ℕ} (g : Fin r → G) : BraidConj g g := Relation.ReflTransGen.refl

theorem BraidConj.trans {r : ℕ} {g h k : Fin r → G} (h₁ : BraidConj g h) (h₂ : BraidConj h k) :
    BraidConj g k := Relation.ReflTransGen.trans h₁ h₂

theorem BraidConj.single {r : ℕ} {g h : Fin r → G} (h₁ : BraidConjStep g h) : BraidConj g h :=
  Relation.ReflTransGen.single h₁

theorem BraidConj.braid {r : ℕ} (n : ℕ) (g : Fin r → G) : BraidConj g (braidTuple n g) :=
  .single (.braid n g)

theorem BraidConj.conj {r : ℕ} (c : G) (g : Fin r → G) :
    BraidConj g fun i => c * g i * c⁻¹ := .single (.conj c g)

theorem braidConjStep_symmetric {r : ℕ} : Symmetric (BraidConjStep : (Fin r → G) → _ → Prop) := by
  rintro g h (⟨n, g⟩ | ⟨n, g⟩ | ⟨c, g⟩)
  · have := BraidConjStep.braidInv n (braidTuple n g)
    rwa [braidTupleInv_braidTuple] at this
  · have := BraidConjStep.braid n (braidTupleInv n g)
    rwa [braidTuple_braidTupleInv] at this
  · have := BraidConjStep.conj c⁻¹ fun i => c * g i * c⁻¹
    have hfun : (fun i => c⁻¹ * (c * g i * c⁻¹) * c⁻¹⁻¹) = g := by
      funext i; group
    rwa [hfun] at this

theorem BraidConj.symm {r : ℕ} {g h : Fin r → G} (hgh : BraidConj g h) : BraidConj h g :=
  Relation.ReflTransGen.symmetric braidConjStep_symmetric hgh

/-- The action of a simultaneous conjugation, in the `ConjAct` form used by the structure-constant
soundness theorem. -/
theorem BraidConj.conjAct {r : ℕ} (x : ConjAct G) (g : Fin r → G) : BraidConj g (x • g) := by
  have : x • g = fun i => ConjAct.ofConjAct x * g i * (ConjAct.ofConjAct x)⁻¹ := by
    funext i; exact ConjAct.smul_def _ _
  rw [this]
  exact .conj _ _

/-! ### Invariance of the Nielsen class -/

theorem prod_map_conj (c : G) (l : List G) :
    ((l.map fun x => c * x * c⁻¹).prod) = c * l.prod * c⁻¹ := by
  induction l with
  | nil => simp
  | cons a t ih => rw [List.map_cons, List.prod_cons, ih, List.prod_cons]; group

theorem conj_mem_nielsenTuples {r : ℕ} {C : Fin r → ConjClasses G} (c : G) {g : Fin r → G}
    (hg : g ∈ nielsenTuples C) : (fun i => c * g i * c⁻¹) ∈ nielsenTuples C := by
  obtain ⟨⟨σ, hσ⟩, hp, hgen⟩ := hg
  refine ⟨⟨σ, fun i => ?_⟩, ?_, ?_⟩
  · rw [← hσ i]
    show ConjClasses.mk (c * g i * c⁻¹) = ConjClasses.mk (g i)
    exact ConjClasses.mk_eq_mk_iff_isConj.2 (isConj_iff.2 ⟨c⁻¹, by group⟩)
  · rw [ofFn_conj, prod_map_conj, hp, mul_one, mul_inv_cancel]
  · have hmap := MonoidHom.map_closure (MulAut.conj c).toMonoidHom (Set.range g)
    have himg : Set.range (fun i => c * g i * c⁻¹)
        = ⇑((MulAut.conj c).toMonoidHom) '' Set.range g := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨g i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
    rw [himg, ← hmap, hgen]
    exact Subgroup.map_top_of_surjective _ (MulAut.conj c).surjective

/-- Braid-and-conjugation equivalence preserves the Nielsen class. -/
theorem BraidConj.mem_nielsenTuples {r : ℕ} {C : Fin r → ConjClasses G} {g h : Fin r → G}
    (hgh : BraidConj g h) (hg : g ∈ nielsenTuples C) : h ∈ nielsenTuples C := by
  induction hgh with
  | refl => exact hg
  | tail _ hstep ih =>
      rcases hstep with ⟨n, k⟩ | ⟨n, k⟩ | ⟨c, k⟩
      · exact braidTuple_mem_nielsenTuples n ih
      · exact braidTupleInv_mem_nielsenTuples n ih
      · exact conj_mem_nielsenTuples c ih

/-! ### The braid moves reorder the classes arbitrarily -/

/-- Every permutation of the conjugacy classes of a tuple is realized by a sequence of Hurwitz
moves. -/
theorem exists_braidConj_perm {r : ℕ} (σ : Equiv.Perm (Fin r)) (g : Fin r → G) :
    ∃ h, BraidConj g h ∧ ∀ i, ConjClasses.mk (h i) = ConjClasses.mk (g (σ i)) := by
  match r with
  | 0 => exact ⟨g, .refl g, fun i => absurd i.2 (by omega)⟩
  | m + 1 =>
      have key : ∀ τ ∈ Submonoid.closure
          (Set.range fun i : Fin m ↦ Equiv.swap i.castSucc i.succ),
          ∀ g : Fin (m + 1) → G,
            ∃ h, BraidConj g h ∧ ∀ i, ConjClasses.mk (h i) = ConjClasses.mk (g (τ i)) := by
        intro τ hτ
        induction hτ using Submonoid.closure_induction with
        | mem x hx =>
            obtain ⟨j, rfl⟩ := hx
            intro g
            refine ⟨braidTuple (j : ℕ) g, .braid _ _, fun i => ?_⟩
            have hj : (j : ℕ) + 1 < m + 1 := by omega
            rw [mk_braidTuple_apply hj g i]
            congr 2
        | one => intro g; exact ⟨g, .refl g, fun i => rfl⟩
        | mul x y _ _ ihx ihy =>
            intro g
            obtain ⟨h, hgh, hh⟩ := ihx g
            obtain ⟨k, hhk, hk⟩ := ihy h
            exact ⟨k, hgh.trans hhk, fun i => (hk i).trans (hh (y i))⟩
      exact key σ (by rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial) g


/-! ### The braid group and its Hurwitz action -/

/-- The `n`-th Hurwitz move as a permutation of the `r`-tuples. -/
def braidEquiv {r : ℕ} (n : ℕ) : Equiv.Perm (Fin r → G) where
  toFun := braidTuple n
  invFun := braidTupleInv n
  left_inv := braidTupleInv_braidTuple n
  right_inv := braidTuple_braidTupleInv n

@[simp] theorem braidEquiv_apply {r : ℕ} (n : ℕ) (g : Fin r → G) :
    braidEquiv n g = braidTuple n g := rfl

theorem braidEquiv_comm {r m n : ℕ} (h : n + 2 ≤ m) :
    (braidEquiv n : Equiv.Perm (Fin r → G)) * braidEquiv m
      = braidEquiv m * braidEquiv n :=
  Equiv.ext fun g => braidTuple_comm h g

theorem braidEquiv_braid {r n : ℕ} (hr : n + 3 ≤ r) :
    (braidEquiv n : Equiv.Perm (Fin r → G)) * braidEquiv (n + 1) * braidEquiv n
      = braidEquiv (n + 1) * braidEquiv n * braidEquiv (n + 1) :=
  Equiv.ext fun g => braidTuple_braidTuple_braidTuple hr g

/-- The braid relations on `n` generators `σ₀, …, σₙ₋₁`: generators at distance at least two
commute, and adjacent ones satisfy `σᵢσᵢ₊₁σᵢ = σᵢ₊₁σᵢσᵢ₊₁`. -/
def braidRels (n : ℕ) : Set (FreeGroup (Fin n)) :=
  {x | ∃ i j : Fin n, (i : ℕ) + 2 ≤ (j : ℕ) ∧
      x = FreeGroup.of i * FreeGroup.of j * (FreeGroup.of i)⁻¹ * (FreeGroup.of j)⁻¹} ∪
  {x | ∃ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 ∧
      x = FreeGroup.of i * FreeGroup.of j * FreeGroup.of i *
        (FreeGroup.of j * FreeGroup.of i * FreeGroup.of j)⁻¹}

/-- The braid group on `n + 1` strands, with generators `σ₀, …, σₙ₋₁`. -/
abbrev BraidGroup (n : ℕ) := PresentedGroup (braidRels n)

theorem braidEquiv_rels (n : ℕ) : ∀ x ∈ braidRels n,
    FreeGroup.lift (fun i : Fin n => (braidEquiv (i : ℕ) : Equiv.Perm (Fin (n + 1) → G))) x = 1 := by
  rintro x (⟨i, j, hij, rfl⟩ | ⟨i, j, hij, rfl⟩)
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [braidEquiv_comm hij]
    group
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, hij]
    rw [braidEquiv_braid (r := n + 1) (by omega)]
    group

/-- The **Hurwitz action** of the braid group on the `(n + 1)`-tuples of a group. -/
def hurwitz (G : Type*) [Group G] (n : ℕ) : BraidGroup n →* Equiv.Perm (Fin (n + 1) → G) :=
  PresentedGroup.toGroup (braidEquiv_rels (G := G) n)

@[simp] theorem hurwitz_of (n : ℕ) (i : Fin n) (g : Fin (n + 1) → G) :
    hurwitz G n (PresentedGroup.of i) g = braidTuple (i : ℕ) g := by
  rw [hurwitz, PresentedGroup.toGroup.of]
  rfl

/-- Every element of the braid group moves a tuple within its braid-and-conjugation class. -/
theorem braidConj_hurwitz (n : ℕ) (b : BraidGroup n) (g : Fin (n + 1) → G) :
    BraidConj g (hurwitz G n b g) := by
  let H : Subgroup (BraidGroup n) :=
    { carrier := {b | ∀ g : Fin (n + 1) → G, BraidConj g (hurwitz G n b g)}
      one_mem' := by intro g; simpa using BraidConj.refl g
      mul_mem' := by
        intro a b ha hb g
        have h₁ : BraidConj g (hurwitz G n b g) := hb g
        have h₂ : BraidConj (hurwitz G n b g) (hurwitz G n a (hurwitz G n b g)) :=
          ha (hurwitz G n b g)
        simpa [map_mul] using h₁.trans h₂
      inv_mem' := by
        intro a ha g
        have h := ha (hurwitz G n a⁻¹ g)
        rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one] at h
        exact (by simpa using h : BraidConj (hurwitz G n a⁻¹ g) g).symm }
  have hgen : ∀ i : Fin n, PresentedGroup.of i ∈ H := by
    intro i g
    simpa using BraidConj.braid (i : ℕ) g
  exact PresentedGroup.generated_by _ H hgen b g

/-- The Hurwitz action preserves the Nielsen class. -/
theorem hurwitz_mem_nielsenTuples {n : ℕ} {C : Fin (n + 1) → ConjClasses G} (b : BraidGroup n)
    {g : Fin (n + 1) → G} (hg : g ∈ nielsenTuples C) : hurwitz G n b g ∈ nielsenTuples C :=
  (braidConj_hurwitz n b g).mem_nielsenTuples hg

/-! ### Weak rigidity -/

/-- **Rigidity implies weak rigidity**: if the generating product-one tuples with the exact classes
`C` form a single simultaneous-conjugacy orbit, then the whole Nielsen class — the tuples carrying
those classes in any order — is a single orbit of the braid moves together with simultaneous
conjugation. -/
theorem braidConj_of_mem_nielsenTuples {r : ℕ} {C : Fin r → ConjClasses G}
    (hrigid : ∀ g₁ ∈ rigidTuples C, ∀ g₂ ∈ rigidTuples C, ∃ x : ConjAct G, x • g₁ = g₂)
    {g h : Fin r → G} (hg : g ∈ rigidTuples C) (hh : h ∈ nielsenTuples C) : BraidConj g h := by
  obtain ⟨⟨σ, hσ⟩, hp, hgen⟩ := hh
  obtain ⟨k, hhk, hk⟩ := exists_braidConj_perm σ⁻¹ h
  have hkmem : k ∈ nielsenTuples C :=
    hhk.mem_nielsenTuples ⟨⟨σ, hσ⟩, hp, hgen⟩
  have hkrigid : k ∈ rigidTuples C := by
    refine ⟨fun i => ?_, hkmem.2.1, hkmem.2.2⟩
    rw [hk i, hσ (σ⁻¹ i)]
    simp
  obtain ⟨x, hx⟩ := hrigid g hg k hkrigid
  exact ((BraidConj.conjAct x g).trans (hx ▸ BraidConj.refl _)).trans hhk.symm

/-- The Nielsen class of a rigidity certificate is a single braid-and-conjugation orbit. -/
theorem braidConj_of_rigidityCertificate {G : Type*} [Group G] [Finite G]
    (cert : RigidityCertificate G) {g h : Fin cert.r → G} (hg : g ∈ rigidTuples cert.C)
    (hh : h ∈ nielsenTuples cert.C) : BraidConj g h :=
  braidConj_of_mem_nielsenTuples
    ((rigid_card_iff_single_orbit (center_triv_iff_center_eq_bot.1 cert.center_triv)
      cert.gen).1 cert.rigid) hg hh

end Rigidity

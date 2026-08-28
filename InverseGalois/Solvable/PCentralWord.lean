/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.PCentralGenerators

/-!
# Formal basic words

A basic element of weight `n` over a family of generators is obtained from a single generator by
`n` successive operations, each of which either forms the commutator with a generator or raises
to the `p`-th power.  Recording the sequence of operations instead of the resulting group element
turns the basic elements into a *formal* object, a `BasicWord`, which can be evaluated in any
group at any family of elements indexed by the same type; the basic elements of weight `n` over a
family of generators are exactly the values of the words of weight `n`.

Two features of the evaluation are what the words are for.  It commutes with homomorphisms, so
the basic elements of a quotient are the images of the basic elements upstairs.  And it only sees
the generators whose indices occur in the word, so substituting `1` for some of the generators
either leaves the value untouched or kills it outright, according to whether every index
occurring in the word was spared.  A word of weight `n` involves at most `n + 1` indices, which
bounds the number of generators that the second feature has to keep track of.

## Main definitions

* `InverseGalois.BasicWord`: a formal basic element of a given weight over a given index type.
* `InverseGalois.BasicWord.eval`: its value at a family of elements of a group.
* `InverseGalois.BasicWord.indices`: the indices of the generators it involves.

## Main results

* `InverseGalois.BasicWord.basicSet_eq_range_eval`: **the basic elements of weight `n` over a
  family of generators are exactly the values of the basic words of weight `n`.**
* `InverseGalois.BasicWord.map_eval`: evaluation commutes with group homomorphisms.
* `InverseGalois.BasicWord.eval_ite`: **substituting `1` for the generators outside a set of
  indices returns the original value if the word only involves spared indices, and `1`
  otherwise.**
* `InverseGalois.BasicWord.length_indices_le`: a word of weight `n` involves at most `n + 1`
  indices.

## Tags

basic element, commutator, lower central series, `p`-group
-/

namespace InverseGalois

universe u

/-- A formal basic element of weight `n` over the index type `ι`: a generator, to which `n`
operations have been applied, each of them either forming the commutator with a generator or
raising to a power. -/
inductive BasicWord (ι : Type u) : ℕ → Type u
  /-- The generator with index `i`, a basic word of weight `0`. -/
  | gen (i : ι) : BasicWord ι 0
  /-- The commutator of a basic word with the generator of index `i`. -/
  | comm {n : ℕ} (w : BasicWord ι n) (i : ι) : BasicWord ι (n + 1)
  /-- The power of a basic word. -/
  | pow {n : ℕ} (w : BasicWord ι n) : BasicWord ι (n + 1)

namespace BasicWord

variable {ι : Type u} {G : Type*} [Group G] {p : ℕ} {g : ι → G}

/-- The value of a basic word at a family of elements of a group, the powers being `p`-th
powers. -/
def eval (p : ℕ) (g : ι → G) {n : ℕ} (w : BasicWord ι n) : G :=
  match n, w with
  | _, .gen i => g i
  | _, .comm w i => ⁅eval p g w, g i⁆
  | _, .pow w => eval p g w ^ p

@[simp] theorem eval_gen (p : ℕ) (g : ι → G) (i : ι) : eval p g (.gen i) = g i := rfl

@[simp] theorem eval_comm (p : ℕ) (g : ι → G) {n : ℕ} (w : BasicWord ι n) (i : ι) :
    eval p g (.comm w i) = ⁅eval p g w, g i⁆ := rfl

@[simp] theorem eval_pow (p : ℕ) (g : ι → G) {n : ℕ} (w : BasicWord ι n) :
    eval p g (.pow w) = eval p g w ^ p := rfl

/-- The list of indices of the generators occurring in a basic word. -/
def indices {n : ℕ} (w : BasicWord ι n) : List ι :=
  match n, w with
  | _, .gen i => [i]
  | _, .comm w i => i :: indices w
  | _, .pow w => indices w

@[simp] theorem indices_gen (i : ι) : (BasicWord.gen i).indices = [i] := rfl

@[simp] theorem indices_comm {n : ℕ} (w : BasicWord ι n) (i : ι) :
    (w.comm i).indices = i :: w.indices := rfl

@[simp] theorem indices_pow {n : ℕ} (w : BasicWord ι n) : w.pow.indices = w.indices := rfl

/-- A basic word of weight `n` involves at most `n + 1` generators. -/
theorem length_indices_le {n : ℕ} (w : BasicWord ι n) : w.indices.length ≤ n + 1 := by
  induction w with
  | gen i => simp
  | comm w i ih =>
    simp only [indices_comm, List.length_cons]
    omega
  | pow w ih =>
    simp only [indices_pow]
    omega

/-! ## Evaluation -/

/-- Evaluation of a basic word commutes with group homomorphisms. -/
theorem map_eval {H : Type*} [Group H] (φ : G →* H) (p : ℕ) (g : ι → G) {n : ℕ}
    (w : BasicWord ι n) : φ (eval p g w) = eval p (fun i => φ (g i)) w := by
  induction w with
  | gen i => simp
  | comm w i ih => simp [ih, map_commutatorElement]
  | pow w ih => simp [ih]

/-- Two families of elements agreeing at every index occurring in a basic word give it the same
value. -/
theorem eval_congr (p : ℕ) {g g' : ι → G} : ∀ {n : ℕ} (w : BasicWord ι n),
    (∀ i ∈ w.indices, g i = g' i) → eval p g w = eval p g' w := by
  intro n w
  induction w with
  | gen i => intro h; exact h i (by simp)
  | comm w i ih =>
    intro h
    rw [eval_comm, eval_comm, ih fun j hj => h j (by simp [hj]), h i (by simp)]
  | pow w ih =>
    intro h
    rw [eval_pow, eval_pow, ih fun j hj => h j (by simp [hj])]

/-- A basic word one of whose generators is trivial has trivial value. -/
theorem eval_eq_one_of_mem_indices (p : ℕ) (g : ι → G) {i : ι} (hg : g i = 1) :
    ∀ {n : ℕ} (w : BasicWord ι n), i ∈ w.indices → eval p g w = 1 := by
  intro n w
  induction w with
  | gen j =>
    intro hi
    simp only [indices_gen, List.mem_singleton] at hi
    rw [eval_gen, ← hi, hg]
  | comm w j ih =>
    intro hi
    rw [indices_comm, List.mem_cons] at hi
    rcases hi with rfl | hi
    · rw [eval_comm, hg, commutatorElement_one_right]
    · rw [eval_comm, ih hi, commutatorElement_one_left]
  | pow w ih =>
    intro hi
    rw [eval_pow, ih (by rwa [indices_pow] at hi), one_pow]

/-- **Substituting `1` for the generators outside a set of indices** returns the original value
of a basic word if every index occurring in the word was spared, and `1` otherwise. -/
theorem eval_ite (p : ℕ) (g : ι → G) (P : ι → Prop) [DecidablePred P] {n : ℕ}
    (w : BasicWord ι n) :
    eval p (fun i => if P i then g i else 1) w
      = if ∀ i ∈ w.indices, P i then eval p g w else 1 := by
  by_cases h : ∀ i ∈ w.indices, P i
  · rw [if_pos h]
    exact eval_congr p w fun i hi => if_pos (h i hi)
  · rw [if_neg h]
    push_neg at h
    obtain ⟨i, hi, hPi⟩ := h
    exact eval_eq_one_of_mem_indices (i := i) p (fun j => if P j then g j else 1)
      (if_neg hPi) w hi

/-! ## The basic elements -/

theorem eval_mem_basicSet (p : ℕ) (g : ι → G) {n : ℕ} (w : BasicWord ι n) :
    eval p g w ∈ basicSet p (Set.range g) n := by
  induction w with
  | gen i => exact Set.mem_range_self i
  | comm w i ih => exact commutatorElement_mem_basicSet ih (Set.mem_range_self i)
  | pow w ih => exact pow_mem_basicSet ih

/-- **The basic elements of weight `n` over a family of generators are exactly the values of the
basic words of weight `n`.** -/
theorem basicSet_eq_range_eval (p : ℕ) (g : ι → G) (n : ℕ) :
    basicSet p (Set.range g) n = Set.range fun w : BasicWord ι n => eval p g w := by
  refine Set.Subset.antisymm ?_ ?_
  · induction n with
    | zero =>
      rintro _ ⟨i, rfl⟩
      exact ⟨.gen i, rfl⟩
    | succ n ih =>
      rintro x hx
      rcases hx with hx | hx
      · obtain ⟨y, hy, z, ⟨i, rfl⟩, rfl⟩ := hx
        obtain ⟨w, rfl⟩ := ih hy
        exact ⟨.comm w i, rfl⟩
      · obtain ⟨y, hy, rfl⟩ := hx
        obtain ⟨w, rfl⟩ := ih hy
        exact ⟨.pow w, rfl⟩
  · rintro _ ⟨w, rfl⟩
    exact eval_mem_basicSet p g w

end BasicWord

end InverseGalois

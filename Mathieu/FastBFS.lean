import Mathlib

/-!
# A fast, verified frontier breadth-first closure over `ℕ`-codes

Several enumeration files (`EnumM24Trans`, `EnumM22Classes`, ...) need to compute the closure
of a starting "code" `start : ℕ` under a finite list of "transformers" `fs : List (ℕ → ℕ)`
(the encoded generator actions), and to know that:

* the closure contains `start`;
* every element of the closure is *reachable* from `start` by applying transformers;
* if the breadth-first search has terminated, the closure is *closed* under the transformers;
* the closure is duplicate-free (so its length is its cardinality).

The naive approach (re-sorting and re-merging the whole accumulated set on every iteration) is
`O(iterations × |set|)` and blows the build budget for large orbits.  Here we use a **frontier
BFS**: `visited` and `frontier` are kept as strictly-sorted (hence duplicate-free) lists, and
each step only expands the frontier.  This is `O(#edges)` and evaluates in seconds even for
orbits with millions of elements.

The whole development is generic in `fs` and `start`; downstream files instantiate it and bridge
`Reach` to the relevant group.
-/

namespace Mathieu

namespace FastBFS

set_option maxRecDepth 10000

/-! ### Tail-recursive sorted-list primitives -/

/-- Remove adjacent duplicates from a list (tail-recursive; correct on sorted input). -/
def ddGo : List ℕ → List ℕ → List ℕ
  | acc, [] => acc.reverse
  | acc, x :: xs =>
      match acc with
      | [] => ddGo [x] xs
      | y :: _ => if x = y then ddGo acc xs else ddGo (x :: acc) xs

/-- Remove adjacent duplicates from a list (tail-recursive). -/
def dd (l : List ℕ) : List ℕ := ddGo [] l

/-- Tail-recursive **union merge** of two sorted lists, dropping duplicates. -/
def umrgGo : List ℕ → List ℕ → List ℕ → List ℕ
  | acc, [], l => acc.reverseAux l
  | acc, a :: as, [] => acc.reverseAux (a :: as)
  | acc, a :: as, b :: bs =>
      if a < b then umrgGo (a :: acc) as (b :: bs)
      else if b < a then umrgGo (b :: acc) (a :: as) bs
      else umrgGo (a :: acc) as bs
  termination_by _ l1 l2 => l1.length + l2.length

/-- Union of two sorted lists (duplicate-dropping). -/
def umrg (l1 l2 : List ℕ) : List ℕ := umrgGo [] l1 l2

/-- Tail-recursive **sorted difference** `l1 \ l2` (elements of `l1` not in `l2`). -/
def sdifGo : List ℕ → List ℕ → List ℕ → List ℕ
  | acc, [], _ => acc.reverse
  | acc, a :: as, [] => acc.reverseAux (a :: as)
  | acc, a :: as, b :: bs =>
      if a < b then sdifGo (a :: acc) as (b :: bs)
      else if b < a then sdifGo acc (a :: as) bs
      else sdifGo acc as bs
  termination_by _ l1 l2 => l1.length + l2.length

/-- Sorted difference `l1 \ l2`. -/
def sdif (l1 l2 : List ℕ) : List ℕ := sdifGo [] l1 l2

/-- The strictly-sorted, duplicate-free list of all images of `frontier` under a single `f`. -/
def oneImage (f : ℕ → ℕ) (frontier : List ℕ) : List ℕ :=
  dd ((frontier.map f).mergeSort (· ≤ ·))

/-- The strictly-sorted, duplicate-free list of all images of `frontier` under `fs`.
Computed per-transformer and merged, which evaluates far faster than sorting one big
concatenation. -/
def imagesSorted (fs : List (ℕ → ℕ)) (frontier : List ℕ) : List ℕ :=
  fs.foldl (fun acc f => umrg acc (oneImage f frontier)) []

/-! ### Membership and sortedness of the primitives -/

lemma mem_ddGo : ∀ (l acc : List ℕ) (x : ℕ), x ∈ ddGo acc l ↔ x ∈ acc ∨ x ∈ l := by
  intro l
  induction l with
  | nil => intro acc x; simp [ddGo]
  | cons a t ih =>
    intro acc x
    cases acc with
    | nil => simp only [ddGo]; rw [ih]; simp
    | cons y ys =>
      simp only [ddGo]
      split
      · rename_i hay
        rw [ih]; subst hay; constructor
        · rintro (h | h); exact Or.inl h; exact Or.inr (List.mem_cons_of_mem _ h)
        · rintro (h | h); exact Or.inl h
          rcases List.mem_cons.1 h with rfl | h
          exact Or.inl (List.mem_cons_self ..); exact Or.inr h
      · rw [ih]; simp; tauto

lemma mem_dd (l : List ℕ) (x : ℕ) : x ∈ dd l ↔ x ∈ l := by
  rw [dd, mem_ddGo]; simp

lemma ddGo_pairwise : ∀ (l acc : List ℕ), List.Pairwise (· ≤ ·) l →
    List.Pairwise (· > ·) acc → (∀ a ∈ acc, ∀ b ∈ l, a ≤ b) →
    List.Pairwise (· < ·) (ddGo acc l) := by
  intro l
  induction l with
  | nil =>
    intro acc _ hacc _
    simp only [ddGo, List.pairwise_reverse]
    exact hacc
  | cons a t ih =>
    intro acc hl hacc hle
    have hat : List.Pairwise (· ≤ ·) t := hl.tail
    have ha_le : ∀ b ∈ t, a ≤ b := by
      intro b hb; exact (List.pairwise_cons.1 hl).1 b hb
    cases acc with
    | nil =>
      simp only [ddGo]
      apply ih [a] hat
      · simp
      · intro x hx b hb
        simp only [List.mem_singleton] at hx; subst hx
        exact ha_le b hb
    | cons y ys =>
      simp only [ddGo]
      split
      · rename_i hay
        apply ih (y :: ys) hat hacc
        intro x hx b hb
        exact hle x hx b (List.mem_cons_of_mem _ hb)
      · rename_i hay
        apply ih (a :: y :: ys) hat
        · refine List.pairwise_cons.2 ⟨?_, hacc⟩
          intro z hz
          have hya0 : y ≤ a := hle y (List.mem_cons_self ..) a (List.mem_cons_self ..)
          have hya : y < a := lt_of_le_of_ne hya0 (fun h => hay h.symm)
          rcases List.mem_cons.1 hz with rfl | hz
          · exact hya
          · have hzy : z < y := (List.pairwise_cons.1 hacc).1 z hz
            exact lt_trans hzy hya
        · intro x hx b hb
          rcases List.mem_cons.1 hx with rfl | hx
          · exact ha_le b hb
          · exact hle x hx b (List.mem_cons_of_mem _ hb)

lemma dd_sorted {l : List ℕ} (hl : l.Pairwise (· ≤ ·)) : (dd l).Pairwise (· < ·) :=
  ddGo_pairwise l [] hl (by simp) (by simp)

lemma mem_umrgGo (x : ℕ) : ∀ acc l1 l2,
    x ∈ umrgGo acc l1 l2 ↔ x ∈ acc ∨ x ∈ l1 ∨ x ∈ l2 := by
  intros acc l1 l2; induction' n : l1.length + l2.length using Nat.strong_induction_on with n ih generalizing acc l1 l2; rcases l1 with ( _ | ⟨ a, as ⟩ ) <;> rcases l2 with ( _ | ⟨ b, bs ⟩ ) <;> simp_all +decide [ ] ;
  · unfold umrgGo; aesop;
  · unfold umrgGo; aesop;
  · unfold umrgGo; aesop;
  · unfold umrgGo;
    grind

lemma mem_umrg (x : ℕ) (l1 l2 : List ℕ) : x ∈ umrg l1 l2 ↔ x ∈ l1 ∨ x ∈ l2 := by
  rw [umrg, mem_umrgGo]; simp

lemma umrg_sorted {l1 l2 : List ℕ} (h1 : l1.Pairwise (· < ·)) (h2 : l2.Pairwise (· < ·)) :
    (umrg l1 l2).Pairwise (· < ·) := by
  revert l1 l2;
  -- We'll use induction on the length of the lists.
  have h_ind : ∀ (acc l1 l2 : List ℕ), List.Pairwise (· > ·) acc → (∀ x ∈ acc, ∀ y ∈ l1, x < y) → (∀ x ∈ acc, ∀ y ∈ l2, x < y) → List.Pairwise (· < ·) l1 → List.Pairwise (· < ·) l2 → List.Pairwise (· < ·) (umrgGo acc l1 l2) := by
    intros acc l1 l2 hacc hacc_l1 hacc_l2 hl1 hl2
    induction' hacc : l1.length + l2.length using Nat.strong_induction_on with n ih generalizing acc l1 l2;
    rcases l1 with ( _ | ⟨ x, l1 ⟩ ) <;> rcases l2 with ( _ | ⟨ y, l2 ⟩ ) <;> simp_all +decide [ List.pairwise_cons ];
    · unfold umrgGo;
      simp_all +decide [ List.pairwise_reverse ];
    · unfold umrgGo; simp +decide [ * ] ;
      simp_all +decide [ List.pairwise_append, List.pairwise_reverse ];
    · unfold umrgGo; simp +decide [ * ] ;
      simp_all +decide [ List.pairwise_append, List.pairwise_reverse ];
    · by_cases hxy : x < y;
      · specialize ih ( l1.length + l2.length + 1 ) ( by linarith ) ( x :: acc ) l1 ( y :: l2 ) ; simp_all +decide [ List.pairwise_cons ];
        convert ih ( fun a ha => by linarith [ hl2.1 a ha ] ) ( by linarith ) using 1;
        rw [ umrgGo ] ; aesop;
      · by_cases hyx : y < x;
        · specialize ih ( l1.length + ( l2.length + 1 ) ) ( by linarith ) ( y :: acc ) ( x :: l1 ) l2 ; simp_all +decide [ List.pairwise_cons ];
          unfold umrgGo; simp_all +decide [ add_comm, add_left_comm ] ;
          grind;
        · norm_num [ show x = y by linarith ] at *;
          specialize ih ( l1.length + l2.length ) ( by linarith ) ( y :: acc ) l1 l2 ; simp_all +decide [ List.pairwise_cons ];
          unfold umrgGo; aesop;
  exact fun { l1 l2 } h1 h2 => h_ind _ _ _ ( by simp +decide ) ( by simp +decide ) ( by simp +decide ) h1 h2

lemma mem_sdifGo (x : ℕ) : ∀ acc l1 l2, l1.Pairwise (· < ·) → l2.Pairwise (· < ·) →
    (x ∈ sdifGo acc l1 l2 ↔ x ∈ acc ∨ (x ∈ l1 ∧ x ∉ l2)) := by
  intros acc l1 l2 hl1 hl2;
  induction' n : l1.length + l2.length using Nat.strong_induction_on with n ih generalizing acc l1 l2;
  rcases l1 with ( _ | ⟨ a, as ⟩ ) <;> rcases l2 with ( _ | ⟨ b, bs ⟩ ) <;> simp_all +decide;
  · unfold sdifGo; aesop;
  · unfold sdifGo; aesop;
  · unfold sdifGo; aesop;
  · unfold sdifGo;
    split_ifs;
    · specialize ih ( as.length + ( bs.length + 1 ) ) ( by linarith ) ( a :: acc ) as ( b :: bs ) ; simp_all +decide [ List.pairwise_cons ];
      grind;
    · convert ih ( as.length + bs.length + 1 ) ( by linarith ) acc ( a :: as ) bs _ _ _ using 1;
      · grind;
      · aesop;
      · tauto;
      · simp +arith +decide;
    · grind

lemma mem_sdif (x : ℕ) {l1 l2 : List ℕ} (h1 : l1.Pairwise (· < ·)) (h2 : l2.Pairwise (· < ·)) :
    x ∈ sdif l1 l2 ↔ (x ∈ l1 ∧ x ∉ l2) := by
  rw [sdif, mem_sdifGo x [] l1 l2 h1 h2]; simp

lemma sdif_sorted {l1 l2 : List ℕ} (h1 : l1.Pairwise (· < ·)) :
    (sdif l1 l2).Pairwise (· < ·) := by
  -- Prove pairwise sortedness of `sdifGo` by induction on `l1`.
  have sdifGo_pairwise_induction : ∀ (acc l1 l2 : List ℕ),
    List.Pairwise (· > ·) acc →
    (∀ x ∈ acc, ∀ y ∈ l1, x < y) →
    List.Pairwise (· < ·) l1 →
    List.Pairwise (· < ·) (sdifGo acc l1 l2) := by
      intros acc l1 l2 hacc hacc_l1 hl1
      induction' l1 with a as ih generalizing acc l2;
      · unfold sdifGo;
        grind only [List.Pairwise.reverse];
      · induction' l2 with b bs ih';
        · unfold sdifGo; simp_all +decide [ List.pairwise_append ] ;
          exact List.pairwise_reverse.mpr hacc
        · unfold sdifGo;
          split_ifs <;> simp_all +decide [ List.pairwise_cons ];
  exact sdifGo_pairwise_induction _ _ _ ( by simp +decide ) ( by simp +decide ) h1

lemma mem_oneImage {f : ℕ → ℕ} {frontier : List ℕ} {x : ℕ} :
    x ∈ oneImage f frontier ↔ ∃ c ∈ frontier, f c = x := by
  simp only [oneImage, mem_dd, List.mem_mergeSort, List.mem_map]

lemma oneImage_sorted (f : ℕ → ℕ) (frontier : List ℕ) :
    (oneImage f frontier).Pairwise (· < ·) := by
  apply dd_sorted
  have h : ∀ (l : List ℕ), (List.mergeSort l (· ≤ ·)).Pairwise (· ≤ ·) := by
    intro l
    have := List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
      (by intro a b c; simp; omega) (by intro a b; simp; omega) l
    simpa using this
  exact h _

/-
Membership in a `foldl umrg` of per-transformer image pieces.
-/
lemma mem_imagesSorted_foldl (frontier : List ℕ) (x : ℕ) :
    ∀ (L : List (ℕ → ℕ)) (init : List ℕ),
      x ∈ L.foldl (fun acc f => umrg acc (oneImage f frontier)) init ↔
        x ∈ init ∨ ∃ f ∈ L, ∃ c ∈ frontier, f c = x := by
  intro L;
  induction' L with f L ih;
  · grind;
  · simp_all +decide [ mem_umrg, mem_oneImage ];
    grind +splitIndPred

/-
Sortedness of a `foldl umrg` of per-transformer image pieces.
-/
lemma sorted_imagesSorted_foldl (frontier : List ℕ) :
    ∀ (L : List (ℕ → ℕ)) (init : List ℕ), init.Pairwise (· < ·) →
      (L.foldl (fun acc f => umrg acc (oneImage f frontier)) init).Pairwise (· < ·) := by
  intros L init hinit
  induction' L with f L ih generalizing init;
  · exact hinit;
  · simpa using ih ( umrg init ( oneImage f frontier ) ) ( umrg_sorted hinit ( oneImage_sorted f frontier ) )

lemma mem_imagesSorted {fs : List (ℕ → ℕ)} {frontier : List ℕ} {x : ℕ} :
    x ∈ imagesSorted fs frontier ↔ ∃ f ∈ fs, ∃ c ∈ frontier, f c = x := by
  rw [imagesSorted, mem_imagesSorted_foldl]; simp

lemma imagesSorted_sorted (fs : List (ℕ → ℕ)) (frontier : List ℕ) :
    (imagesSorted fs frontier).Pairwise (· < ·) :=
  sorted_imagesSorted_foldl frontier fs [] (by simp)

/-! ### The frontier BFS -/

/-- One frontier BFS step: `new := frontier-images not yet visited`, then extend `visited`. -/
def bfsStep (fs : List (ℕ → ℕ)) (vf : List ℕ × List ℕ) : List ℕ × List ℕ :=
  let new := sdif (imagesSorted fs vf.2) vf.1
  (umrg vf.1 new, new)

/-- The BFS state after `K` steps, started from the singleton `start`. -/
def run (fs : List (ℕ → ℕ)) (start : ℕ) (K : ℕ) : List ℕ × List ℕ :=
  (bfsStep fs)^[K] ([start], [start])

/-- The visited set after `K` steps: the enumerated closure. -/
def orbit (fs : List (ℕ → ℕ)) (start : ℕ) (K : ℕ) : List ℕ := (run fs start K).1

/-! ### The reachability relation -/

/-- One transformer step. -/
def Step (fs : List (ℕ → ℕ)) (a b : ℕ) : Prop := ∃ f ∈ fs, f a = b

/-- `c` is reachable from `start` by applying transformers. -/
def Reach (fs : List (ℕ → ℕ)) (start c : ℕ) : Prop :=
  Relation.ReflTransGen (Step fs) start c

/-! ### Invariants of the BFS -/

/-
Both components of the BFS state are strictly sorted.
-/
lemma run_sorted (fs : List (ℕ → ℕ)) (start K : ℕ) :
    (run fs start K).1.Pairwise (· < ·) ∧ (run fs start K).2.Pairwise (· < ·) := by
  induction' K with K ih <;> simp_all +decide [ Function.iterate_succ_apply', run ];
  exact ⟨ umrg_sorted ih.1 ( sdif_sorted ( imagesSorted_sorted fs _ ) ), sdif_sorted ( imagesSorted_sorted fs _ ) ⟩

/-
The frontier is contained in the visited set.
-/
lemma run_frontier_subset (fs : List (ℕ → ℕ)) (start K : ℕ) :
    ∀ c ∈ (run fs start K).2, c ∈ (run fs start K).1 := by
  induction' K with K ih <;> simp_all +decide [ Function.iterate_succ_apply', run ];
  simp +decide [ bfsStep ];
  exact fun c hc => by rw [ mem_umrg ] ; tauto;

/-
Everything visited (and every frontier element) is reachable from `start`.
-/
lemma run_reach (fs : List (ℕ → ℕ)) (start K : ℕ) :
    (∀ c ∈ (run fs start K).1, Reach fs start c)
      ∧ (∀ c ∈ (run fs start K).2, Reach fs start c) := by
  induction' K with K ih;
  · constructor <;> intro <;> simp_all +decide [ run ]; all_goals exact fun h => Relation.ReflTransGen.refl;
  · -- Let `vf := run fs start K`, `new := sdif (imagesSorted fs vf.2) vf.1`.
    set vf := run fs start K
    set new := sdif (imagesSorted fs vf.2) vf.1;
    -- For `c ∈ new`, by `mem_sdif` (needs `imagesSorted` sorted and `vf.1` sorted), `c ∈ imagesSorted fs vf.2`.
    have h_new_mem : ∀ c ∈ new, ∃ f ∈ fs, ∃ c' ∈ vf.2, f c' = c := by
      grind only [mem_sdif, run_sorted, mem_imagesSorted, imagesSorted_sorted];
    -- By definition of `run`, we have `(run fs start (K + 1)).1 = umrg vf.1 new` and `(run fs start (K + 1)).2 = new`.
    have h_run_succ : run fs start (K + 1) = (umrg vf.1 new, new) := by
      exact Function.iterate_succ_apply' _ _ _;
    simp_all +decide [ mem_umrg ];
    exact ⟨ fun c hc => hc.elim ( fun hc => ih.1 c hc ) fun hc => by obtain ⟨ f, hf, c', hc', rfl ⟩ := h_new_mem c hc; exact Relation.ReflTransGen.tail ( ih.2 c' hc' ) ⟨ f, hf, rfl ⟩, fun c hc => by obtain ⟨ f, hf, c', hc', rfl ⟩ := h_new_mem c hc; exact Relation.ReflTransGen.tail ( ih.2 c' hc' ) ⟨ f, hf, rfl ⟩ ⟩

/-
BFS closure invariant: every visited node is either still in the frontier, or all of its
transformer-images are already visited.
-/
lemma run_closedInv (fs : List (ℕ → ℕ)) (start K : ℕ) :
    ∀ c ∈ (run fs start K).1, c ∈ (run fs start K).2 ∨ ∀ f ∈ fs, f c ∈ (run fs start K).1 := by
  induction' K with K ih;
  · unfold run; aesop;
  · simp_all +decide [ run, Function.iterate_succ_apply' ];
    have := run_sorted fs start K;
    simp_all +decide [ run, bfsStep ];
    grind only [mem_sdif, mem_umrg, imagesSorted_sorted, mem_imagesSorted]

/-! ### Exported interface -/

/-
`start` is in the closure.
-/
lemma start_mem_orbit (fs : List (ℕ → ℕ)) (start K : ℕ) : start ∈ orbit fs start K := by
  -- By induction on K, we can show that start is in the orbit at step K.
  have h_ind : ∀ K, start ∈ (run fs start K).1 := by
    intro K; induction' K with K ih <;> simp_all +decide [ Function.iterate_succ_apply', run ] ;
    exact mem_umrg start _ _ |>.2 ( Or.inl ih );
  exact h_ind K

/-- The closure is duplicate-free. -/
lemma orbit_nodup (fs : List (ℕ → ℕ)) (start K : ℕ) : (orbit fs start K).Nodup :=
  ((run_sorted fs start K).1).imp (fun h => ne_of_lt h)

/-- Every element of the closure is reachable from `start`. -/
lemma orbit_reach (fs : List (ℕ → ℕ)) (start K : ℕ) :
    ∀ c ∈ orbit fs start K, Reach fs start c := (run_reach fs start K).1

/-- If the BFS has terminated (empty frontier), the closure is closed under the transformers. -/
lemma orbit_closed (fs : List (ℕ → ℕ)) (start K : ℕ) (hterm : (run fs start K).2 = []) :
    ∀ c ∈ orbit fs start K, ∀ f ∈ fs, f c ∈ orbit fs start K := by
  intro c hc f hf
  rcases run_closedInv fs start K c hc with h | h
  · rw [hterm] at h; simp at h
  · exact h f hf

end FastBFS

end Mathieu
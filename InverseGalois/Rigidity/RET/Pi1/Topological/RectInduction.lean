/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Pi1.Topological.Exterior
import InverseGalois.Rigidity.RET.Pi1.Topological.RectSpider

/-!
# Every rectangle boundary loop is a generating product of puncture loops

Cutting a rectangle repeatedly reduces the number of punctures it contains: around a chosen
puncture one carves out a small square, by two vertical and two horizontal cuts, and each of the
four remaining pieces contains strictly fewer punctures. Since the square contains exactly one
puncture and the empty rectangle contributes the empty product, induction on the number of
punctures shows that the boundary loop of any rectangle is an ordered product of loops winding
once around each puncture inside it.

The same induction carries the generation clause of `RectSpider`, and this is what fixes the four
half-sides of the square: they are chosen so small that the frame of every piece of the recursion
still separates the punctures, so at the leaf the frame of the square is a convex region punctured
at a single point, whose loops are all powers of the boundary loop. Taking the frame of the whole
rectangle to be the plane, the loops produced by the induction generate the fundamental group of
the complement of the punctures.

The cut coordinates are chosen to avoid the coordinates of all the punctures, which keeps every
puncture strictly inside the piece that contains it; this is what makes the induction go through
without any general-position argument about lines through two punctures.

## Main results

* `Rigidity.RET.rectSpider_of_ncard_le` — the induction on the number of punctures.
* `Rigidity.RET.rectSpider_of_finite` — its unconditional form.
* `Rigidity.RET.exists_rect_interior` — a finite set of punctures sits in the interior of some
  rectangle, whose sides run outside a disc containing the punctures.
* `Rigidity.RET.exists_rectSpider_compl` — for a finite set of punctures there is a rectangle whose
  boundary loop, read in the complement of the punctures, is an ordered product of loops winding
  once around each of them which together generate every loop of the complement, and which runs
  entirely in the exterior of a disc containing the punctures.
-/

open scoped unitInterval
open CategoryTheory

noncomputable section

namespace Rigidity.RET

/-! ### Sides of a rectangle far from the origin -/

/-- A horizontal segment at a height of large absolute value lies outside a disc. -/
theorem seg_horiz_subset_extRegion {R y : ℝ} {a b : ℂ} (ha : a.im = y) (hb : b.im = y)
    (hy : R < |y|) : seg a b ⊆ extRegion R := by
  intro z hz
  rw [mem_extRegion]
  refine hy.trans_le ?_
  rw [← im_of_mem_seg ha hb hz]
  exact Complex.abs_im_le_norm z

/-- A vertical segment at an abscissa of large absolute value lies outside a disc. -/
theorem seg_vert_subset_extRegion {R x : ℝ} {a b : ℂ} (ha : a.re = x) (hb : b.re = x)
    (hx : R < |x|) : seg a b ⊆ extRegion R := by
  intro z hz
  rw [mem_extRegion]
  refine hx.trans_le ?_
  rw [← re_of_mem_seg ha hb hz]
  exact Complex.abs_re_le_norm z

/-- A finite set of points lies in the interior of some axis-parallel rectangle whose four sides
run outside a disc that already contains the whole set. -/
theorem exists_rect_interior {S : Set ℂ} (hSfin : S.Finite) :
    ∃ x₀ x₁ y₀ y₁ R : ℝ, x₀ ≤ x₁ ∧ y₀ ≤ y₁ ∧ 0 < R ∧
      R < -x₀ ∧ R < x₁ ∧ R < -y₀ ∧ R < y₁ ∧ (∀ t ∈ S, ‖t‖ < R) ∧
      ∀ t ∈ S, x₀ < t.re ∧ t.re < x₁ ∧ y₀ < t.im ∧ t.im < y₁ := by
  obtain ⟨M, hM⟩ := (hSfin.image (fun t : ℂ => ‖t‖)).bddAbove
  set N : ℝ := max M 0 + 1 with hN
  have hMN : M ≤ N - 1 := by
    have : M ≤ max M 0 := le_max_left _ _
    linarith
  have hN1 : (1 : ℝ) ≤ N := by
    have : (0 : ℝ) ≤ max M 0 := le_max_right _ _
    linarith
  refine ⟨-N, N, -N, N, N - 1 / 2, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, fun t ht => ?_, fun t ht => ?_⟩
  · have h1 : ‖t‖ ≤ M := hM ⟨t, ht, rfl⟩
    linarith
  · have h1 : ‖t‖ ≤ M := hM ⟨t, ht, rfl⟩
    have h2 : ‖t‖ < N := by linarith
    have h3 : |t.re| < N := lt_of_le_of_lt (Complex.abs_re_le_norm t) h2
    have h4 : |t.im| < N := lt_of_le_of_lt (Complex.abs_im_le_norm t) h2
    rw [abs_lt] at h3 h4
    exact ⟨h3.1, h3.2, h4.1, h4.2⟩

/-- **The boundary loop of a rectangle is an ordered product of loops around the punctures it
contains, generating the loops of its frame**, by induction on their number. -/
theorem rectSpider_of_ncard_le {X S : Set ℂ} (hSfin : S.Finite) :
    ∀ (n : ℕ) (x₀ x₁ y₀ y₁ : ℝ) (V : Set ℂ), (S ∩ rect x₀ x₁ y₀ y₁).ncard ≤ n → x₀ ≤ x₁ →
      y₀ ≤ y₁ → RectFrame S V x₀ x₁ y₀ y₁ →
      (∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → x₀ < t.re ∧ t.re < x₁ ∧ y₀ < t.im ∧ t.im < y₁) →
      RectSpider X S V x₀ x₁ y₀ y₁ := by
  intro n
  induction n with
  | zero =>
    intro x₀ x₁ y₀ y₁ V hcard hx hy hfr _
    exact rectSpider_of_empty hx hy hfr
      ((Set.ncard_eq_zero (hSfin.inter_of_left _)).mp (Nat.le_zero.mp hcard))
  | succ n ih =>
    intro x₀ x₁ y₀ y₁ V hcard hx hy hfr hgen
    rcases Set.eq_empty_or_nonempty (S ∩ rect x₀ x₁ y₀ y₁) with hE | ⟨s, hsS, hsR⟩
    · exact rectSpider_of_empty hx hy hfr hE
    obtain ⟨g1, g2, g3, g4⟩ := hgen s hsS hsR
    have hAfin : (S ∩ rect x₀ x₁ y₀ y₁).Finite := hSfin.inter_of_left _
    have hsV : s ∈ V := hfr.rect_subset hsR
    obtain ⟨ρ, hρ, hballV⟩ := Metric.isOpen_iff.mp hfr.isOpen s hsV
    -- a positive lower bound for the nonzero coordinate gaps between `s` and the other punctures
    have hDfin : ((((fun t : ℂ => |t.re - s.re|) '' (S ∩ rect x₀ x₁ y₀ y₁)) ∪
        ((fun t : ℂ => |t.im - s.im|) '' (S ∩ rect x₀ x₁ y₀ y₁))) ∩ Set.Ioi (0 : ℝ)).Finite :=
      ((hAfin.image _).union (hAfin.image _)).inter_of_left _
    obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ d ∈ ((((fun t : ℂ => |t.re - s.re|) ''
        (S ∩ rect x₀ x₁ y₀ y₁)) ∪ ((fun t : ℂ => |t.im - s.im|) ''
        (S ∩ rect x₀ x₁ y₀ y₁))) ∩ Set.Ioi (0 : ℝ)), δ ≤ d := by
      rcases Set.eq_empty_or_nonempty ((((fun t : ℂ => |t.re - s.re|) ''
          (S ∩ rect x₀ x₁ y₀ y₁)) ∪ ((fun t : ℂ => |t.im - s.im|) ''
          (S ∩ rect x₀ x₁ y₀ y₁))) ∩ Set.Ioi (0 : ℝ)) with hE | hne
      · exact ⟨1, one_pos, fun d hd => by rw [hE] at hd; exact hd.elim⟩
      · obtain ⟨δ, hδmem, hδmin⟩ := Set.exists_min_image _ id hDfin hne
        exact ⟨δ, hδmem.2, fun d hd => hδmin d hd⟩
    -- the half-side of the square carved out around `s`
    obtain ⟨a, hapos, haδ, haρ, hax0, hax1, hay0, hay1⟩ :
        ∃ a : ℝ, 0 < a ∧ 2 * a < δ ∧ 2 * a < ρ ∧ x₀ < s.re - a ∧ s.re + a < x₁ ∧
          y₀ < s.im - a ∧ s.im + a < y₁ := by
      set M : ℝ := min (min (δ / 3) (ρ / 3))
        (min (min (s.re - x₀) (x₁ - s.re)) (min (s.im - y₀) (y₁ - s.im))) with hM
      have h1 : M ≤ δ / 3 := by rw [hM]; exact (min_le_left _ _).trans (min_le_left _ _)
      have h2 : M ≤ ρ / 3 := by rw [hM]; exact (min_le_left _ _).trans (min_le_right _ _)
      have h3 : M ≤ s.re - x₀ := by
        rw [hM]; exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
      have h4 : M ≤ x₁ - s.re := by
        rw [hM]; exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
      have h5 : M ≤ s.im - y₀ := by
        rw [hM]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
      have h6 : M ≤ y₁ - s.im := by
        rw [hM]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
      have h0 : 0 < M := by
        rw [hM]
        exact lt_min (lt_min (by linarith) (by linarith))
          (lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith) (by linarith)))
      exact ⟨M / 2, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
        by linarith⟩
    -- every other puncture is far from `s` in each coordinate in which it differs from `s`
    have hre_tri : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ →
        t.re = s.re ∨ t.re < s.re - 2 * a ∨ s.re + 2 * a < t.re := by
      intro t htS htR
      rcases eq_or_ne t.re s.re with h | h
      · exact Or.inl h
      · have hd : δ ≤ |t.re - s.re| :=
          hδ _ ⟨Or.inl ⟨t, ⟨htS, htR⟩, rfl⟩, Set.mem_Ioi.mpr (abs_pos.mpr (sub_ne_zero.mpr h))⟩
        rcases abs_cases (t.re - s.re) with ⟨he, -⟩ | ⟨he, -⟩
        · exact Or.inr (Or.inr (by linarith))
        · exact Or.inr (Or.inl (by linarith))
    have him_tri : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ →
        t.im = s.im ∨ t.im < s.im - 2 * a ∨ s.im + 2 * a < t.im := by
      intro t htS htR
      rcases eq_or_ne t.im s.im with h | h
      · exact Or.inl h
      · have hd : δ ≤ |t.im - s.im| :=
          hδ _ ⟨Or.inr ⟨t, ⟨htS, htR⟩, rfl⟩, Set.mem_Ioi.mpr (abs_pos.mpr (sub_ne_zero.mpr h))⟩
        rcases abs_cases (t.im - s.im) with ⟨he, -⟩ | ⟨he, -⟩
        · exact Or.inr (Or.inr (by linarith))
        · exact Or.inr (Or.inl (by linarith))
    -- restriction of a property of the punctures to a sub-rectangle
    have hres : ∀ {u₀ u₁ v₀ v₁ : ℝ} {P : ℂ → Prop}, rect u₀ u₁ v₀ v₁ ⊆ rect x₀ x₁ y₀ y₁ →
        (∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → P t) → ∀ t ∈ S, t ∈ rect u₀ u₁ v₀ v₁ → P t :=
      fun hm hav t htS ht => hav t htS (hm ht)
    -- the eight coordinates that no puncture attains
    have avx0 : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.re ≠ x₀ := fun t h1 h2 => (hgen t h1 h2).1.ne'
    have avx1 : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.re ≠ x₁ := fun t h1 h2 => (hgen t h1 h2).2.1.ne
    have avy0 : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.im ≠ y₀ :=
      fun t h1 h2 => (hgen t h1 h2).2.2.1.ne'
    have avy1 : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.im ≠ y₁ :=
      fun t h1 h2 => (hgen t h1 h2).2.2.2.ne
    have avc1 : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.re ≠ s.re - a := by
      intro t htS htR he
      rcases hre_tri t htS htR with h | h | h <;> linarith
    have avc2 : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.re ≠ s.re + a := by
      intro t htS htR he
      rcases hre_tri t htS htR with h | h | h <;> linarith
    have avd1 : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.im ≠ s.im - a := by
      intro t htS htR he
      rcases him_tri t htS htR with h | h | h <;> linarith
    have avd2 : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.im ≠ s.im + a := by
      intro t htS htR he
      rcases him_tri t htS htR with h | h | h <;> linarith
    -- every puncture stays clear of the four cut lines by the margin `a`
    have hL1 : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.re < s.re - a ∨ s.re - a + a ≤ t.re := by
      intro t htS htR
      rcases hre_tri t htS htR with h | h | h
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    have hR1 : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.re ≤ s.re - a - a ∨ s.re - a < t.re := by
      intro t htS htR
      rcases hre_tri t htS htR with h | h | h
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    have hL2 : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.re < s.re + a ∨ s.re + a + a ≤ t.re := by
      intro t htS htR
      rcases hre_tri t htS htR with h | h | h
      · exact Or.inl (by linarith)
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    have hR2 : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.re ≤ s.re + a - a ∨ s.re + a < t.re := by
      intro t htS htR
      rcases hre_tri t htS htR with h | h | h
      · exact Or.inl (by linarith)
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    have hB1 : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.im < s.im - a ∨ s.im - a + a ≤ t.im := by
      intro t htS htR
      rcases him_tri t htS htR with h | h | h
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    have hT1 : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.im ≤ s.im - a - a ∨ s.im - a < t.im := by
      intro t htS htR
      rcases him_tri t htS htR with h | h | h
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    have hB2 : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.im < s.im + a ∨ s.im + a + a ≤ t.im := by
      intro t htS htR
      rcases him_tri t htS htR with h | h | h
      · exact Or.inl (by linarith)
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    have hT2 : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.im ≤ s.im + a - a ∨ s.im + a < t.im := by
      intro t htS htR
      rcases him_tri t htS htR with h | h | h
      · exact Or.inl (by linarith)
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    -- generic position and counts for the sub-rectangles
    have hgen' : ∀ {u₀ u₁ v₀ v₁ : ℝ}, rect u₀ u₁ v₀ v₁ ⊆ rect x₀ x₁ y₀ y₁ →
        (∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.re ≠ u₀) →
        (∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.re ≠ u₁) →
        (∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.im ≠ v₀) →
        (∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.im ≠ v₁) →
        ∀ t ∈ S, t ∈ rect u₀ u₁ v₀ v₁ → u₀ < t.re ∧ t.re < u₁ ∧ v₀ < t.im ∧ t.im < v₁ := by
      intro u₀ u₁ v₀ v₁ hm b0 b1 b2 b3 t htS ht
      have htR := hm ht
      exact ⟨lt_of_le_of_ne ht.1 (Ne.symm (b0 t htS htR)),
        lt_of_le_of_ne ht.2.1 (b1 t htS htR),
        lt_of_le_of_ne ht.2.2.1 (Ne.symm (b2 t htS htR)),
        lt_of_le_of_ne ht.2.2.2 (b3 t htS htR)⟩
    have hcount : ∀ {u₀ u₁ v₀ v₁ : ℝ}, rect u₀ u₁ v₀ v₁ ⊆ rect x₀ x₁ y₀ y₁ →
        s ∉ rect u₀ u₁ v₀ v₁ → (S ∩ rect u₀ u₁ v₀ v₁).ncard ≤ n := by
      intro u₀ u₁ v₀ v₁ hm hns
      have hsd : S ∩ rect u₀ u₁ v₀ v₁ ⊆ (S ∩ rect x₀ x₁ y₀ y₁) \ {s} := by
        rintro t ⟨htS, htr⟩
        refine ⟨⟨htS, hm htr⟩, ?_⟩
        simp only [Set.mem_singleton_iff]
        rintro rfl
        exact hns htr
      have h1 := Set.ncard_le_ncard hsd hAfin.diff
      have h2 := Set.ncard_diff_singleton_lt_of_mem (Set.mem_inter hsS hsR) hAfin
      omega
    -- the nine rectangles
    have mL : rect x₀ (s.re - a) y₀ y₁ ⊆ rect x₀ x₁ y₀ y₁ :=
      rect_mono le_rfl (by linarith) le_rfl le_rfl
    have mM' : rect (s.re - a) x₁ y₀ y₁ ⊆ rect x₀ x₁ y₀ y₁ :=
      rect_mono (by linarith) le_rfl le_rfl le_rfl
    have mM : rect (s.re - a) (s.re + a) y₀ y₁ ⊆ rect x₀ x₁ y₀ y₁ :=
      rect_mono (by linarith) (by linarith) le_rfl le_rfl
    have mRt : rect (s.re + a) x₁ y₀ y₁ ⊆ rect x₀ x₁ y₀ y₁ :=
      rect_mono (by linarith) le_rfl le_rfl le_rfl
    have mB : rect (s.re - a) (s.re + a) y₀ (s.im - a) ⊆ rect x₀ x₁ y₀ y₁ :=
      rect_mono (by linarith) (by linarith) le_rfl (by linarith)
    have mM'' : rect (s.re - a) (s.re + a) (s.im - a) y₁ ⊆ rect x₀ x₁ y₀ y₁ :=
      rect_mono (by linarith) (by linarith) (by linarith) le_rfl
    have mT : rect (s.re - a) (s.re + a) (s.im + a) y₁ ⊆ rect x₀ x₁ y₀ y₁ :=
      rect_mono (by linarith) (by linarith) (by linarith) le_rfl
    -- the eight frames
    have hfrL : RectFrame S (V ∩ {z : ℂ | z.re < s.re - a + a}) x₀ (s.re - a) y₀ y₁ :=
      hfr.cutLeft (by linarith) hapos hL1
    have hfrM' : RectFrame S (V ∩ {z : ℂ | s.re - a - a < z.re}) (s.re - a) x₁ y₀ y₁ :=
      hfr.cutRight (by linarith) hapos hR1
    have hfrM : RectFrame S (V ∩ {z : ℂ | s.re - a - a < z.re} ∩ {z : ℂ | z.re < s.re + a + a})
        (s.re - a) (s.re + a) y₀ y₁ :=
      hfrM'.cutLeft (by linarith) hapos (hres mM' hL2)
    have hfrRt : RectFrame S (V ∩ {z : ℂ | s.re - a - a < z.re} ∩ {z : ℂ | s.re + a - a < z.re})
        (s.re + a) x₁ y₀ y₁ :=
      hfrM'.cutRight (by linarith) hapos (hres mM' hR2)
    have hfrB : RectFrame S (V ∩ {z : ℂ | s.re - a - a < z.re} ∩ {z : ℂ | z.re < s.re + a + a} ∩
        {z : ℂ | z.im < s.im - a + a}) (s.re - a) (s.re + a) y₀ (s.im - a) :=
      hfrM.cutBot (by linarith) hapos (hres mM hB1)
    have hfrM'' : RectFrame S (V ∩ {z : ℂ | s.re - a - a < z.re} ∩ {z : ℂ | z.re < s.re + a + a} ∩
        {z : ℂ | s.im - a - a < z.im}) (s.re - a) (s.re + a) (s.im - a) y₁ :=
      hfrM.cutTop (by linarith) hapos (hres mM hT1)
    have hfrQ : RectFrame S (V ∩ {z : ℂ | s.re - a - a < z.re} ∩ {z : ℂ | z.re < s.re + a + a} ∩
        {z : ℂ | s.im - a - a < z.im} ∩ {z : ℂ | z.im < s.im + a + a})
        (s.re - a) (s.re + a) (s.im - a) (s.im + a) :=
      hfrM''.cutBot (by linarith) hapos (hres mM'' hB2)
    have hfrT : RectFrame S (V ∩ {z : ℂ | s.re - a - a < z.re} ∩ {z : ℂ | z.re < s.re + a + a} ∩
        {z : ℂ | s.im - a - a < z.im} ∩ {z : ℂ | s.im + a - a < z.im})
        (s.re - a) (s.re + a) (s.im + a) y₁ :=
      hfrM''.cutTop (by linarith) hapos (hres mM'' hT2)
    -- the square frame contains a disc around `s` and no other puncture
    have hballQ : Metric.ball s (2 * a) ⊆ V ∩ {z : ℂ | s.re - a - a < z.re} ∩
        {z : ℂ | z.re < s.re + a + a} ∩ {z : ℂ | s.im - a - a < z.im} ∩
        {z : ℂ | z.im < s.im + a + a} := by
      intro z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have h1 : |z.re - s.re| < 2 * a := by
        refine lt_of_le_of_lt ?_ hz
        simpa using Complex.abs_re_le_norm (z - s)
      have h2 : |z.im - s.im| < 2 * a := by
        refine lt_of_le_of_lt ?_ hz
        simpa using Complex.abs_im_le_norm (z - s)
      rw [abs_lt] at h1 h2
      refine ⟨⟨⟨⟨hballV ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm]; linarith
      · simp only [Set.mem_setOf_eq]; linarith
      · simp only [Set.mem_setOf_eq]; linarith
      · simp only [Set.mem_setOf_eq]; linarith
      · simp only [Set.mem_setOf_eq]; linarith
    have honeQ : S ∩ (V ∩ {z : ℂ | s.re - a - a < z.re} ∩ {z : ℂ | z.re < s.re + a + a} ∩
        {z : ℂ | s.im - a - a < z.im} ∩ {z : ℂ | z.im < s.im + a + a}) = {s} := by
      have hsQ : s ∈ V ∩ {z : ℂ | s.re - a - a < z.re} ∩ {z : ℂ | z.re < s.re + a + a} ∩
          {z : ℂ | s.im - a - a < z.im} ∩ {z : ℂ | z.im < s.im + a + a} := by
        refine ⟨⟨⟨⟨hsV, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> simp only [Set.mem_setOf_eq] <;> linarith
      refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨hsS, hsQ⟩, ?_⟩
      rintro t ⟨htS, ⟨⟨⟨htV, htA⟩, htB⟩, htC⟩, htD⟩
      have htR : t ∈ rect x₀ x₁ y₀ y₁ := hfr.inter_subset ⟨htS, htV⟩
      have hre : t.re = s.re := by
        rcases hre_tri t htS htR with h | h | h
        · exact h
        · exact absurd (show s.re - a - a < t.re from htA) (not_lt.mpr (by linarith))
        · exact absurd (show t.re < s.re + a + a from htB) (not_lt.mpr (by linarith))
      have him : t.im = s.im := by
        rcases him_tri t htS htR with h | h | h
        · exact h
        · exact absurd (show s.im - a - a < t.im from htC) (not_lt.mpr (by linarith))
        · exact absurd (show t.im < s.im + a + a from htD) (not_lt.mpr (by linarith))
      exact Complex.ext hre him
    -- the leaves
    have hQ := rectSpider_of_single (X := X) hapos hfrQ hballQ honeQ
    have hSL := ih x₀ (s.re - a) y₀ y₁ _
      (hcount mL (fun h => absurd h.2.1 (not_le.mpr (by linarith)))) (by linarith) hy hfrL
      (hgen' mL avx0 avc1 avy0 avy1)
    have hSRt := ih (s.re + a) x₁ y₀ y₁ _
      (hcount mRt (fun h => absurd h.1 (not_le.mpr (by linarith)))) (by linarith) hy hfrRt
      (hgen' mRt avc2 avx1 avy0 avy1)
    have hSB := ih (s.re - a) (s.re + a) y₀ (s.im - a) _
      (hcount mB (fun h => absurd h.2.2.2 (not_le.mpr (by linarith)))) (by linarith)
      (by linarith) hfrB (hgen' mB avc1 avc2 avy0 avd1)
    have hST := ih (s.re - a) (s.re + a) (s.im + a) y₁ _
      (hcount mT (fun h => absurd h.2.2.1 (not_le.mpr (by linarith)))) (by linarith)
      (by linarith) hfrT (hgen' mT avc1 avc2 avd2 avy1)
    -- assemble the four cuts
    have hSM'' := rectSpider_of_cut_horiz hSfin (by linarith : s.re - a ≤ s.re + a)
      (by linarith : s.im - a ≤ s.im + a) (by linarith : s.im + a ≤ y₁) hapos hfrM''
      (hres mM'' avd2) hQ hST
    have hSM := rectSpider_of_cut_horiz hSfin (by linarith : s.re - a ≤ s.re + a)
      (by linarith : y₀ ≤ s.im - a) (by linarith : s.im - a ≤ y₁) hapos hfrM
      (hres mM avd1) hSB hSM''
    have hSM' := rectSpider_of_cut_vert hSfin (by linarith : s.re - a ≤ s.re + a)
      (by linarith : s.re + a ≤ x₁) hy hapos hfrM' (hres mM' avc2) hSM hSRt
    exact rectSpider_of_cut_vert hSfin (by linarith : x₀ ≤ s.re - a)
      (by linarith : s.re - a ≤ x₁) hy hapos hfr avc1 hSL hSM'

/-- **The boundary loop of a rectangle is an ordered product of loops around the punctures it
contains, generating the loops of its frame**, for any finite set of punctures lying in its
interior. -/
theorem rectSpider_of_finite {X S V : Set ℂ} (hSfin : S.Finite) {x₀ x₁ y₀ y₁ : ℝ}
    (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁) (hfr : RectFrame S V x₀ x₁ y₀ y₁)
    (hgen : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → x₀ < t.re ∧ t.re < x₁ ∧ y₀ < t.im ∧ t.im < y₁) :
    RectSpider X S V x₀ x₁ y₀ y₁ :=
  rectSpider_of_ncard_le hSfin _ x₀ x₁ y₀ y₁ V le_rfl hx hy hfr hgen

/-- **For a finite set of punctures there is a rectangle whose boundary loop is an ordered product
of loops winding once around each puncture, and those loops generate the whole fundamental group
of the complement of the punctures.** -/
theorem exists_rectSpider_compl {S : Set ℂ} (hSfin : S.Finite) :
    ∃ (x₀ x₁ y₀ y₁ R : ℝ) (hab : seg (cpt x₀ y₀) (cpt x₁ y₀) ⊆ Sᶜ)
      (hbc : seg (cpt x₁ y₀) (cpt x₁ y₁) ⊆ Sᶜ) (hcd : seg (cpt x₁ y₁) (cpt x₀ y₁) ⊆ Sᶜ)
      (hda : seg (cpt x₀ y₁) (cpt x₀ y₀) ⊆ Sᶜ),
      0 < R ∧ extRegion R ⊆ Sᶜ ∧
        seg (cpt x₀ y₀) (cpt x₁ y₀) ⊆ extRegion R ∧
        seg (cpt x₁ y₀) (cpt x₁ y₁) ⊆ extRegion R ∧
        seg (cpt x₁ y₁) (cpt x₀ y₁) ⊆ extRegion R ∧
        seg (cpt x₀ y₁) (cpt x₀ y₀) ⊆ extRegion R ∧
        IsPunctureProd Sᶜ S (hab (left_mem_seg _ _))
          (FundamentalGroup.fromPath (boxLoop hab hbc hcd hda)) ⊤ := by
  obtain ⟨x₀, x₁, y₀, y₁, R, hx, hy, hR0, hRx0, hRx1, hRy0, hRy1, hRnorm, hint⟩ :=
    exists_rect_interior hSfin
  have hext : extRegion R ⊆ Sᶜ := fun z hz hzS =>
    absurd (mem_extRegion.mp hz) (not_lt.2 (hRnorm z hzS).le)
  have hax0 : R < |x₀| := hRx0.trans_le (neg_le_abs x₀)
  have hax1 : R < |x₁| := hRx1.trans_le (le_abs_self x₁)
  have hay0 : R < |y₀| := hRy0.trans_le (neg_le_abs y₀)
  have hay1 : R < |y₁| := hRy1.trans_le (le_abs_self y₁)
  have eab : seg (cpt x₀ y₀) (cpt x₁ y₀) ⊆ extRegion R :=
    seg_horiz_subset_extRegion (cpt_im x₀ y₀) (cpt_im x₁ y₀) hay0
  have ebc : seg (cpt x₁ y₀) (cpt x₁ y₁) ⊆ extRegion R :=
    seg_vert_subset_extRegion (cpt_re x₁ y₀) (cpt_re x₁ y₁) hax1
  have ecd : seg (cpt x₁ y₁) (cpt x₀ y₁) ⊆ extRegion R :=
    seg_horiz_subset_extRegion (cpt_im x₁ y₁) (cpt_im x₀ y₁) hay1
  have eda : seg (cpt x₀ y₁) (cpt x₀ y₀) ⊆ extRegion R :=
    seg_vert_subset_extRegion (cpt_re x₀ y₁) (cpt_re x₀ y₀) hax0
  have hSsub : S ⊆ rect x₀ x₁ y₀ y₁ := fun t ht =>
    ⟨(hint t ht).1.le, (hint t ht).2.1.le, (hint t ht).2.2.1.le, (hint t ht).2.2.2.le⟩
  have hgen : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ →
      x₀ < t.re ∧ t.re < x₁ ∧ y₀ < t.im ∧ t.im < y₁ := fun t ht _ => hint t ht
  have hfr : RectFrame S (Set.univ : Set ℂ) x₀ x₁ y₀ y₁ :=
    { isConvex := convex_univ
      isOpen := isOpen_univ
      rect_subset := Set.subset_univ _
      inter_subset := fun t ht => hSsub ht.1 }
  have hVX : (Set.univ : Set ℂ) \ S ⊆ Sᶜ := fun z hz => hz.2
  have hXU : (Sᶜ : Set ℂ) ⊆ Set.univ \ S := fun z hz => ⟨trivial, hz⟩
  have hdc : rect x₀ x₁ y₀ y₁ \ S ⊆ Set.univ \ S := Set.diff_subset_diff_left (Set.subset_univ _)
  have avy0 : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.im ≠ y₀ := fun t h1 h2 => (hgen t h1 h2).2.2.1.ne'
  have avy1 : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.im ≠ y₁ := fun t h1 h2 => (hgen t h1 h2).2.2.2.ne
  have avx0 : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.re ≠ x₀ := fun t h1 h2 => (hgen t h1 h2).1.ne'
  have avx1 : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.re ≠ x₁ := fun t h1 h2 => (hgen t h1 h2).2.1.ne
  have sab : seg (cpt x₀ y₀) (cpt x₁ y₀) ⊆ Set.univ \ S :=
    (seg_horiz_subset_diff ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ ⟨le_rfl, hy⟩ avy0).trans hdc
  have sbc : seg (cpt x₁ y₀) (cpt x₁ y₁) ⊆ Set.univ \ S :=
    (seg_vert_subset_diff ⟨le_rfl, hy⟩ ⟨hy, le_rfl⟩ ⟨hx, le_rfl⟩ avx1).trans hdc
  have scd : seg (cpt x₁ y₁) (cpt x₀ y₁) ⊆ Set.univ \ S :=
    (seg_horiz_subset_diff ⟨hx, le_rfl⟩ ⟨le_rfl, hx⟩ ⟨hy, le_rfl⟩ avy1).trans hdc
  have sda : seg (cpt x₀ y₁) (cpt x₀ y₀) ⊆ Set.univ \ S :=
    (seg_vert_subset_diff ⟨hy, le_rfl⟩ ⟨le_rfl, hy⟩ ⟨le_rfl, hx⟩ avx0).trans hdc
  refine ⟨x₀, x₁, y₀, y₁, R, sab.trans hVX, sbc.trans hVX, scd.trans hVX, sda.trans hVX,
    hR0, hext, eab, ebc, ecd, eda, ?_⟩
  have key := rectSpider_of_finite (X := Sᶜ) hSfin hx hy hfr hgen hVX sab sbc scd sda
  rw [Set.inter_eq_left.mpr hSsub] at key
  exact key.mono (pi1Image_eq_top_of_eq hVX hXU (sab (left_mem_seg _ _))).ge

end Rigidity.RET

end

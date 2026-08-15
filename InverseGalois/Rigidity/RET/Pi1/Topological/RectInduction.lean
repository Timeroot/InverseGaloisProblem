/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Pi1.Topological.RectSpider

/-!
# Every rectangle boundary loop is a product of puncture loops

Cutting a rectangle repeatedly reduces the number of punctures it contains: around a chosen
puncture one carves out a small square, by two vertical and two horizontal cuts, and each of the
four remaining pieces contains strictly fewer punctures. Since the square contains exactly one
puncture and the empty rectangle contributes the empty product, induction on the number of
punctures shows that the boundary loop of any rectangle is an ordered product of loops winding
once around each puncture inside it.

The cut coordinates are chosen to avoid the coordinates of all the punctures, which keeps every
puncture strictly inside the piece that contains it; this is what makes the induction go through
without any general-position argument about lines through two punctures.

## Main results

* `Rigidity.RET.rectSpider_of_ncard_le` — the induction on the number of punctures.
* `Rigidity.RET.rectSpider_of_finite` — its unconditional form.
* `Rigidity.RET.exists_rect_interior` — a finite set of punctures sits in the interior of some
  rectangle.
* `Rigidity.RET.exists_rectSpider_compl` — for a finite set of punctures there is a rectangle whose
  boundary loop, read in the complement of the punctures, is an ordered product of loops winding
  once around each of them.
-/

open scoped unitInterval
open CategoryTheory

noncomputable section

namespace Rigidity.RET

/-- A finite set of points lies in the interior of some axis-parallel rectangle. -/
theorem exists_rect_interior {S : Set ℂ} (hSfin : S.Finite) :
    ∃ x₀ x₁ y₀ y₁ : ℝ, x₀ ≤ x₁ ∧ y₀ ≤ y₁ ∧
      ∀ t ∈ S, x₀ < t.re ∧ t.re < x₁ ∧ y₀ < t.im ∧ t.im < y₁ := by
  obtain ⟨M, hM⟩ := (hSfin.image (fun t : ℂ => ‖t‖)).bddAbove
  set N : ℝ := max M 0 + 1 with hN
  have hN0 : (0 : ℝ) < N := by
    have : (0 : ℝ) ≤ max M 0 := le_max_right _ _
    linarith
  refine ⟨-N, N, -N, N, by linarith, by linarith, fun t ht => ?_⟩
  have h1 : ‖t‖ ≤ M := hM ⟨t, ht, rfl⟩
  have h2 : ‖t‖ < N := by
    have : M ≤ max M 0 := le_max_left _ _
    linarith
  have h3 : |t.re| < N := lt_of_le_of_lt (Complex.abs_re_le_norm t) h2
  have h4 : |t.im| < N := lt_of_le_of_lt (Complex.abs_im_le_norm t) h2
  rw [abs_lt] at h3 h4
  exact ⟨h3.1, h3.2, h4.1, h4.2⟩
/-- **The boundary loop of a rectangle is an ordered product of loops around the punctures it
contains**, by induction on their number. -/
theorem rectSpider_of_ncard_le {X S : Set ℂ} (hSfin : S.Finite) :
    ∀ (n : ℕ) (x₀ x₁ y₀ y₁ : ℝ), (S ∩ rect x₀ x₁ y₀ y₁).ncard ≤ n → x₀ ≤ x₁ → y₀ ≤ y₁ →
      rect x₀ x₁ y₀ y₁ \ S ⊆ X →
      (∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → x₀ < t.re ∧ t.re < x₁ ∧ y₀ < t.im ∧ t.im < y₁) →
      RectSpider X S x₀ x₁ y₀ y₁ := by
  intro n
  induction n with
  | zero =>
    intro x₀ x₁ y₀ y₁ hcard hx hy hsub _
    exact rectSpider_of_empty hx hy hsub
      ((Set.ncard_eq_zero (hSfin.inter_of_left _)).mp (Nat.le_zero.mp hcard))
  | succ n ih =>
    intro x₀ x₁ y₀ y₁ hcard hx hy hsub hgen
    rcases Set.eq_empty_or_nonempty (S ∩ rect x₀ x₁ y₀ y₁) with hE | ⟨s, hsS, hsR⟩
    · exact rectSpider_of_empty hx hy hsub hE
    obtain ⟨g1, g2, g3, g4⟩ := hgen s hsS hsR
    -- a punctured disc around `s` inside the open rectangle and missing `S`
    obtain ⟨ρ, hρ, hdisc⟩ :=
      exists_radius (isOpen_openRect x₀ x₁ y₀ y₁) (show s ∈ openRect x₀ x₁ y₀ y₁ from
        ⟨g1, g2, g3, g4⟩) hSfin
    have hdiscX : puncturedDisc s ρ ⊆ X := fun z hz =>
      hsub ⟨openRect_subset_rect _ _ _ _ (hdisc hz).1, (hdisc hz).2⟩
    -- the finite set of forbidden half-sides
    have hAfin : (S ∩ rect x₀ x₁ y₀ y₁).Finite := hSfin.inter_of_left _
    have hFfin : (((fun t : ℂ => s.re - t.re) '' (S ∩ rect x₀ x₁ y₀ y₁) ∪
        (fun t : ℂ => t.re - s.re) '' (S ∩ rect x₀ x₁ y₀ y₁)) ∪
        (fun t : ℂ => s.im - t.im) '' (S ∩ rect x₀ x₁ y₀ y₁) ∪
        (fun t : ℂ => t.im - s.im) '' (S ∩ rect x₀ x₁ y₀ y₁)).Finite :=
      (((hAfin.image _).union (hAfin.image _)).union (hAfin.image _)).union (hAfin.image _)
    have hεpos : (0 : ℝ) <
        min (min (ρ / 2) (s.re - x₀)) (min (x₁ - s.re) (min (s.im - y₀) (y₁ - s.im))) := by
      simp only [lt_min_iff]
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith, by linarith⟩
    obtain ⟨a, ⟨hapos, haε⟩, haF⟩ := (Set.Ioo_infinite hεpos).exists_notMem_finite hFfin
    have haρ : 2 * a < ρ := by
      have h := lt_of_lt_of_le haε ((min_le_left _ _).trans (min_le_left _ _))
      linarith
    have hax0 : x₀ < s.re - a := by
      have h := lt_of_lt_of_le haε ((min_le_left _ _).trans (min_le_right _ _))
      linarith
    have hax1 : s.re + a < x₁ := by
      have h := lt_of_lt_of_le haε ((min_le_right _ _).trans (min_le_left _ _))
      linarith
    have hay0 : y₀ < s.im - a := by
      have h := lt_of_lt_of_le haε
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
      linarith
    have hay1 : s.im + a < y₁ := by
      have h := lt_of_lt_of_le haε
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
      linarith
    -- the eight coordinates that no puncture attains
    have avx0 : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.re ≠ x₀ := fun t h1 h2 => (hgen t h1 h2).1.ne'
    have avx1 : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.re ≠ x₁ := fun t h1 h2 => (hgen t h1 h2).2.1.ne
    have avy0 : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.im ≠ y₀ :=
      fun t h1 h2 => (hgen t h1 h2).2.2.1.ne'
    have avy1 : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.im ≠ y₁ :=
      fun t h1 h2 => (hgen t h1 h2).2.2.2.ne
    have avc1 : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.re ≠ s.re - a := by
      intro t htS htR hre
      exact haF (Or.inl (Or.inl (Or.inl ⟨t, ⟨htS, htR⟩, by simp only [hre]; ring⟩)))
    have avc2 : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.re ≠ s.re + a := by
      intro t htS htR hre
      exact haF (Or.inl (Or.inl (Or.inr ⟨t, ⟨htS, htR⟩, by simp only [hre]; ring⟩)))
    have avd1 : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.im ≠ s.im - a := by
      intro t htS htR him
      exact haF (Or.inl (Or.inr ⟨t, ⟨htS, htR⟩, by simp only [him]; ring⟩))
    have avd2 : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.im ≠ s.im + a := by
      intro t htS htR him
      exact haF (Or.inr ⟨t, ⟨htS, htR⟩, by simp only [him]; ring⟩)
    -- generic position, subsets, and counts for the sub-rectangles
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
    have hsub' : ∀ {u₀ u₁ v₀ v₁ : ℝ}, rect u₀ u₁ v₀ v₁ ⊆ rect x₀ x₁ y₀ y₁ →
        rect u₀ u₁ v₀ v₁ \ S ⊆ X := fun hm z hz => hsub ⟨hm hz.1, hz.2⟩
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
    have havoid' : ∀ {u₀ u₁ v₀ v₁ : ℝ} {c : ℝ}, rect u₀ u₁ v₀ v₁ ⊆ rect x₀ x₁ y₀ y₁ →
        (∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.re ≠ c) →
        ∀ t ∈ S, t ∈ rect u₀ u₁ v₀ v₁ → t.re ≠ c := fun hm hav t htS ht => hav t htS (hm ht)
    have havoidI' : ∀ {u₀ u₁ v₀ v₁ : ℝ} {c : ℝ}, rect u₀ u₁ v₀ v₁ ⊆ rect x₀ x₁ y₀ y₁ →
        (∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.im ≠ c) →
        ∀ t ∈ S, t ∈ rect u₀ u₁ v₀ v₁ → t.im ≠ c := fun hm hav t htS ht => hav t htS (hm ht)
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
    -- the square around `s` contains no other puncture
    have hQS : S ∩ rect (s.re - a) (s.re + a) (s.im - a) (s.im + a) = {s} := by
      refine Set.eq_singleton_iff_unique_mem.mpr
        ⟨⟨hsS, by constructor <;> [linarith; exact ⟨by linarith, by linarith, by linarith⟩]⟩, ?_⟩
      rintro t ⟨htS, ht1, ht2, ht3, ht4⟩
      by_contra hne
      have hnorm : ‖t - s‖ < ρ := by
        refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
        rw [Complex.sub_re, Complex.sub_im]
        have h1 : |t.re - s.re| ≤ a := abs_le.mpr ⟨by linarith, by linarith⟩
        have h2 : |t.im - s.im| ≤ a := abs_le.mpr ⟨by linarith, by linarith⟩
        linarith
      exact (hdisc ⟨by rw [Metric.mem_ball, dist_eq_norm]; exact hnorm, hne⟩).2 htS
    -- the four leaves handled by the inductive hypothesis, and the square
    have hQ : RectSpider X S (s.re - a) (s.re + a) (s.im - a) (s.im + a) :=
      rectSpider_of_single hapos haρ hdiscX hQS
    have hL : RectSpider X S x₀ (s.re - a) y₀ y₁ :=
      ih _ _ _ _ (hcount mL (fun h => absurd h.2.1 (by simp; linarith))) (by linarith) hy
        (hsub' mL) (hgen' mL avx0 avc1 avy0 avy1)
    have hRt : RectSpider X S (s.re + a) x₁ y₀ y₁ :=
      ih _ _ _ _ (hcount mRt (fun h => absurd h.1 (by simp; linarith))) (by linarith) hy
        (hsub' mRt) (hgen' mRt avc2 avx1 avy0 avy1)
    have hB : RectSpider X S (s.re - a) (s.re + a) y₀ (s.im - a) :=
      ih _ _ _ _ (hcount mB (fun h => absurd h.2.2.2 (by simp; linarith))) (by linarith)
        (by linarith) (hsub' mB) (hgen' mB avc1 avc2 avy0 avd1)
    have hT : RectSpider X S (s.re - a) (s.re + a) (s.im + a) y₁ :=
      ih _ _ _ _ (hcount mT (fun h => absurd h.2.2.1 (by simp; linarith))) (by linarith)
        (by linarith) (hsub' mT) (hgen' mT avc1 avc2 avd2 avy1)
    -- assemble the four cuts
    have hM'' : RectSpider X S (s.re - a) (s.re + a) (s.im - a) y₁ :=
      rectSpider_of_cut_horiz (by linarith) (by linarith) (by linarith) (hsub' mM'')
        (havoidI' mM'' avd2) hQ hT
    have hM : RectSpider X S (s.re - a) (s.re + a) y₀ y₁ :=
      rectSpider_of_cut_horiz (by linarith) (by linarith) (by linarith) (hsub' mM)
        (havoidI' mM avd1) hB hM''
    have hM' : RectSpider X S (s.re - a) x₁ y₀ y₁ :=
      rectSpider_of_cut_vert (by linarith) (by linarith) hy (hsub' mM')
        (havoid' mM' avc2) hM hRt
    exact rectSpider_of_cut_vert (by linarith) (by linarith) hy hsub
      (fun t htS ht => avc1 t htS ht) hL hM'

/-- **The boundary loop of a rectangle is an ordered product of loops around the punctures it
contains**, for any finite set of punctures lying in its interior. -/
theorem rectSpider_of_finite {X S : Set ℂ} (hSfin : S.Finite) {x₀ x₁ y₀ y₁ : ℝ}
    (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁) (hsub : rect x₀ x₁ y₀ y₁ \ S ⊆ X)
    (hgen : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → x₀ < t.re ∧ t.re < x₁ ∧ y₀ < t.im ∧ t.im < y₁) :
    RectSpider X S x₀ x₁ y₀ y₁ :=
  rectSpider_of_ncard_le hSfin _ x₀ x₁ y₀ y₁ le_rfl hx hy hsub hgen

/-- **For a finite set of punctures there is a rectangle whose boundary loop is an ordered product
of loops winding once around each puncture**, read in the complement of the punctures. -/
theorem exists_rectSpider_compl {S : Set ℂ} (hSfin : S.Finite) :
    ∃ (x₀ x₁ y₀ y₁ : ℝ) (hab : seg (cpt x₀ y₀) (cpt x₁ y₀) ⊆ Sᶜ)
      (hbc : seg (cpt x₁ y₀) (cpt x₁ y₁) ⊆ Sᶜ) (hcd : seg (cpt x₁ y₁) (cpt x₀ y₁) ⊆ Sᶜ)
      (hda : seg (cpt x₀ y₁) (cpt x₀ y₀) ⊆ Sᶜ),
      IsPunctureProd Sᶜ S (hab (left_mem_seg _ _))
        (FundamentalGroup.fromPath (boxLoop hab hbc hcd hda)) := by
  obtain ⟨x₀, x₁, y₀, y₁, hx, hy, hint⟩ := exists_rect_interior hSfin
  have hSsub : S ⊆ rect x₀ x₁ y₀ y₁ := fun t ht =>
    ⟨(hint t ht).1.le, (hint t ht).2.1.le, (hint t ht).2.2.1.le, (hint t ht).2.2.2.le⟩
  have hgen : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ →
      x₀ < t.re ∧ t.re < x₁ ∧ y₀ < t.im ∧ t.im < y₁ := fun t ht _ => hint t ht
  have hdc : rect x₀ x₁ y₀ y₁ \ S ⊆ Sᶜ := fun z hz => hz.2
  have avy0 : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.im ≠ y₀ := fun t h1 h2 => (hgen t h1 h2).2.2.1.ne'
  have avy1 : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.im ≠ y₁ := fun t h1 h2 => (hgen t h1 h2).2.2.2.ne
  have avx0 : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.re ≠ x₀ := fun t h1 h2 => (hgen t h1 h2).1.ne'
  have avx1 : ∀ t ∈ S, t ∈ rect x₀ x₁ y₀ y₁ → t.re ≠ x₁ := fun t h1 h2 => (hgen t h1 h2).2.1.ne
  have sab : seg (cpt x₀ y₀) (cpt x₁ y₀) ⊆ Sᶜ :=
    (seg_horiz_subset_diff ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ ⟨le_rfl, hy⟩ avy0).trans hdc
  have sbc : seg (cpt x₁ y₀) (cpt x₁ y₁) ⊆ Sᶜ :=
    (seg_vert_subset_diff ⟨le_rfl, hy⟩ ⟨hy, le_rfl⟩ ⟨hx, le_rfl⟩ avx1).trans hdc
  have scd : seg (cpt x₁ y₁) (cpt x₀ y₁) ⊆ Sᶜ :=
    (seg_horiz_subset_diff ⟨hx, le_rfl⟩ ⟨le_rfl, hx⟩ ⟨hy, le_rfl⟩ avy1).trans hdc
  have sda : seg (cpt x₀ y₁) (cpt x₀ y₀) ⊆ Sᶜ :=
    (seg_vert_subset_diff ⟨hy, le_rfl⟩ ⟨le_rfl, hy⟩ ⟨le_rfl, hx⟩ avx0).trans hdc
  refine ⟨x₀, x₁, y₀, y₁, sab, sbc, scd, sda, ?_⟩
  have key := rectSpider_of_finite (X := Sᶜ) hSfin hx hy hdc hgen sab sbc scd sda
  rwa [Set.inter_eq_left.mpr hSsub] at key

end Rigidity.RET

end

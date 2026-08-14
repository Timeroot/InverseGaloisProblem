/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.GeomRET
import InverseGalois.Rigidity.RET.SubUnramified

/-!
# Branch points carrying a trivial branch cycle

A point of the line is unramified in a cover exactly when the *trivial* deck transformation is a
distinguished inertia generator there: the inertia groups above a point are all conjugate, so one of
them being trivial makes every one of them trivial, and conversely a point of the line always has a
place above it.

Consequently a branch point carrying the trivial branch cycle is not a branch point at all, and the
list of branch points of a realization may be padded with such points or stripped of them without
changing anything.  Together with the fact that the branch points and the branch cycles may be
reindexed simultaneously, this says that a realization depends on the branch data only as an
unordered family of *nontrivial* branch cycles attached to points.

## Main results

* `Rigidity.RET.LineCover.isInertiaGenAt_one_iff` — the trivial deck transformation is a
  distinguished inertia generator at a point exactly when the cover is unramified there.
* `Rigidity.RET.IsMonodromyOver.reindex` — branch points and branch cycles may be permuted together.
* `Rigidity.RET.IsMonodromyOver.snoc`, `Rigidity.RET.IsMonodromyOver.of_snoc` — a new branch point
  carrying the trivial branch cycle may be added, and removed again.
-/

open Polynomial
open scoped Pointwise

noncomputable section

namespace Rigidity.RET

open GeomAKLB

attribute [local instance] Ideal.Quotient.field GeomAKLB.instMSA GeomAKLB.instIsFrac
  GeomAKLB.instIGG GeomAKLB.instFinite GeomAKLB.instIntegral GeomAKLB.instFaithful
  GeomAKLB.instDedekindB

namespace LineCover

/-- **An unramified point carries the trivial distinguished inertia generator.**  Every point of the
line has a place of the cover above it, and there the inertia group is trivial. -/
theorem isInertiaGenAt_one (L : LineCover) {t : k}
    (h : ∀ σ : L.deck, L.IsInertiaAt t σ → σ = 1) : L.IsInertiaGenAt t 1 := by
  obtain ⟨Q, hmax, hover⟩ := L.exists_place t
  refine ⟨Q, hmax, hover, ?_⟩
  rw [Subgroup.zpowers_one_eq_bot, eq_bot_iff]
  intro σ hσ
  exact Subgroup.mem_bot.mpr (h σ ⟨Q, hmax, hover, hσ⟩)

/-- **A point carrying the trivial distinguished inertia generator is unramified.**  The inertia
groups above a point are conjugate, so one of them being trivial makes all of them trivial. -/
theorem eq_one_of_isInertiaGenAt_one (L : LineCover) {t : k} (h : L.IsInertiaGenAt t 1)
    {σ : L.deck} (hσ : L.IsInertiaAt t σ) : σ = 1 := by
  obtain ⟨Q, hmax, hover, hI⟩ := h
  obtain ⟨Q', hmax', hover', hin⟩ := hσ
  haveI := hmax
  haveI := hmax'
  haveI : Q.IsPrime := hmax.isPrime
  haveI : Q'.IsPrime := hmax'.isPrime
  haveI := hover
  haveI := hover'
  obtain ⟨g, hg⟩ := exists_smul_eq_of_liesOver (Ω := L.M) t Q Q'
  rw [hg, geomInertia_smul, hI, Subgroup.zpowers_one_eq_bot, Subgroup.map_bot,
    Subgroup.mem_bot] at hin
  exact hin

/-- **The trivial deck transformation is a distinguished inertia generator at a point exactly when
the cover is unramified there.** -/
theorem isInertiaGenAt_one_iff (L : LineCover) {t : k} :
    L.IsInertiaGenAt t 1 ↔ ∀ σ : L.deck, L.IsInertiaAt t σ → σ = 1 :=
  ⟨fun h _ hσ => L.eq_one_of_isInertiaGenAt_one h hσ, L.isInertiaGenAt_one⟩

end LineCover

/-! ## Reindexing the branch data -/

/-- **The branch points and the branch cycles may be permuted together.** -/
theorem IsMonodromyOver.reindex {G : Type} [Group G] [Finite G] {r : ℕ} {h : Fin r → G}
    {t : Fin r → k} (H : IsMonodromyOver h t) (σ : Equiv.Perm (Fin r)) :
    IsMonodromyOver (h ∘ σ) (t ∘ σ) := by
  obtain ⟨L, e, hout, hinf, hin⟩ := H
  have hrange : Set.range (t ∘ σ) = Set.range t := by
    rw [Set.range_comp, σ.surjective.range_eq, Set.image_univ]
  exact ⟨L, e, hrange ▸ hout, hinf, fun i => hin (σ i)⟩

/-! ## Adding and removing a trivial branch cycle -/

/-- **A new branch point carrying the trivial branch cycle may be added.**  The cover is unchanged;
the new point was not a branch point of it, so the trivial deck transformation generates the inertia
there. -/
theorem IsMonodromyOver.snoc {G : Type} [Group G] [Finite G] {r : ℕ} {h : Fin r → G}
    {t : Fin r → k} (H : IsMonodromyOver h t) {s : k} (hs : s ∉ Set.range t) :
    IsMonodromyOver (Fin.snoc h 1) (Fin.snoc t s) := by
  obtain ⟨L, e, hout, hinf, hin⟩ := H
  have hsub : Set.range t ⊆ Set.range (Fin.snoc t s : Fin (r + 1) → k) := by
    rintro _ ⟨i, rfl⟩
    refine ⟨i.castSucc, ?_⟩
    rw [Fin.snoc_castSucc]
  refine ⟨L, e, hout.mono hsub, hinf, fun i => ?_⟩
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
    exact hin j
  · rw [Fin.snoc_last, Fin.snoc_last, map_one]
    exact L.isInertiaGenAt_one fun τ hτ => hout s hs τ hτ

/-- **A branch point carrying the trivial branch cycle may be removed.**  The trivial branch cycle
says exactly that the cover is unramified there, so the remaining points already carry the whole
branch locus. -/
theorem IsMonodromyOver.of_snoc {G : Type} [Group G] [Finite G] {r : ℕ} {h : Fin r → G}
    {t : Fin r → k} {s : k} (H : IsMonodromyOver (Fin.snoc h 1) (Fin.snoc t s)) :
    IsMonodromyOver h t := by
  obtain ⟨L, e, hout, hinf, hin⟩ := H
  have hlast : L.IsInertiaGenAt s 1 := by
    have h1 := hin (Fin.last r)
    rwa [Fin.snoc_last, Fin.snoc_last, map_one] at h1
  refine ⟨L, e, ?_, hinf, fun i => ?_⟩
  · intro u hu τ hτ
    rcases eq_or_ne u s with rfl | hus
    · exact L.eq_one_of_isInertiaGenAt_one hlast hτ
    · refine hout u ?_ τ hτ
      rintro ⟨j, hj⟩
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · rw [Fin.snoc_castSucc] at hj
        exact hu ⟨j', hj⟩
      · rw [Fin.snoc_last] at hj
        exact hus hj.symm
  · have hi := hin i.castSucc
    rwa [Fin.snoc_castSucc, Fin.snoc_castSucc] at hi

end Rigidity.RET

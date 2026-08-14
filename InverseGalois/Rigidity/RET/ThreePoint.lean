/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.DihedralTriple
import InverseGalois.Rigidity.RET.MonodromyQuotient
import InverseGalois.Rigidity.RET.TrivialCycle
import InverseGalois.Rigidity.RET.ExistenceAbelian

/-!
# Three-point branch data, with the points forgotten

Three distinct points of the projective line carry no invariant, so a cover of the line branched
over three points can be read in a coordinate carrying those points to any other three
(`isMonodromyOver_transport`).  A tuple of three branch cycles is therefore realizable over one
triple of distinct points exactly when it is realizable over every triple, and the branch points can
be dropped from the statement altogether.

This file records that predicate on a group and a triple, `IsThreePointMonodromy`, together with
what is known about it: it is closed under quotients, isomorphisms, conjugation and reindexing, it
holds for every product-one generating triple in an abelian group and in a dihedral group, and the
existence half of the Riemann existence correspondence over three points is exactly the statement
that it holds for every product-one generating triple.

## Main results

* `Rigidity.RET.IsThreePointMonodromy` — the tuple is the branch-cycle system of a cover of the
  line branched over three points.
* `Rigidity.RET.isThreePointMonodromy_iff` — one triple of distinct points suffices to test it.
* `Rigidity.RET.IsThreePointMonodromy.map`, `.congr`, `.conj`, `.reindex` — the closure properties.
* `Rigidity.RET.isThreePointMonodromy_of_commGroup`,
  `Rigidity.RET.isThreePointMonodromy_dihedral` — the groups for which it is known.
* `Rigidity.RET.geomRETExistence_iff_forall_isThreePointMonodromy` — the existence half of the
  correspondence over three points, with the points forgotten.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

open GeomAKLB

/-! ## A concrete triple of distinct points -/

/-- The points `0`, `1` and `2` of the line are distinct. -/
theorem injective_zeroOneTwo : Function.Injective (![0, 1, 2] : Fin 3 → k) := by
  refine injective_fin3 ?_ ?_ ?_
  · show (0 : k) ≠ 1
    norm_num
  · show (0 : k) ≠ 2
    norm_num
  · show (1 : k) ≠ 2
    norm_num

/-! ## Three-point branch data -/

/-- **The tuple `h` is the branch-cycle system of a cover of the line branched over three points.**
Which three points is immaterial, so they are quantified over rather than prescribed. -/
def IsThreePointMonodromy {G : Type} [Group G] [Finite G] (h : Fin 3 → G) : Prop :=
  ∀ t : Fin 3 → k, Function.Injective t → IsMonodromyOver h t

/-- **A realization over one triple of distinct points is a realization over every triple.** -/
theorem isThreePointMonodromy_of_isMonodromyOver {G : Type} [Group G] [Finite G] {h : Fin 3 → G}
    {t : Fin 3 → k} (ht : Function.Injective t) (H : IsMonodromyOver h t) :
    IsThreePointMonodromy h :=
  fun _ hs => isMonodromyOver_transport ht hs H

/-- **One triple of distinct points suffices to test three-point realizability.** -/
theorem isThreePointMonodromy_iff {G : Type} [Group G] [Finite G] (h : Fin 3 → G) :
    IsThreePointMonodromy h ↔ ∃ t : Fin 3 → k, Function.Injective t ∧ IsMonodromyOver h t :=
  ⟨fun H => ⟨_, injective_zeroOneTwo, H _ injective_zeroOneTwo⟩,
    fun ⟨_, ht, H⟩ => isThreePointMonodromy_of_isMonodromyOver ht H⟩

/-! ## Closure properties -/

/-- **Three-point branch data pushes forward along a surjection of groups.** -/
theorem IsThreePointMonodromy.map {G H : Type} [Group G] [Finite G] [Group H] [Finite H]
    {h : Fin 3 → G} (H₀ : IsThreePointMonodromy h) (π : G →* H) (hπ : Function.Surjective π) :
    IsThreePointMonodromy fun i => π (h i) :=
  fun t ht => (H₀ t ht).map π hπ

/-- **Three-point branch data transports along an isomorphism of groups.** -/
theorem IsThreePointMonodromy.congr {G H : Type} [Group G] [Finite G] [Group H] [Finite H]
    {h : Fin 3 → G} (H₀ : IsThreePointMonodromy h) (φ : G ≃* H) :
    IsThreePointMonodromy fun i => φ (h i) :=
  fun t ht => (H₀ t ht).congr φ

/-- **Three-point branch data may be conjugated.** -/
theorem IsThreePointMonodromy.conj {G : Type} [Group G] [Finite G] {h : Fin 3 → G}
    (H₀ : IsThreePointMonodromy h) (g : G) :
    IsThreePointMonodromy fun i => g * h i * g⁻¹ :=
  fun t ht => (H₀ t ht).conj g

/-- **Three-point branch data may be permuted.**  The branch points can be permuted along with the
cycles, and then moved back to where they were. -/
theorem IsThreePointMonodromy.reindex {G : Type} [Group G] [Finite G] {h : Fin 3 → G}
    (H₀ : IsThreePointMonodromy h) (σ : Equiv.Perm (Fin 3)) :
    IsThreePointMonodromy (h ∘ σ) := by
  intro s hs
  have hcomp : (s ∘ (σ.symm : Equiv.Perm (Fin 3))) ∘ (σ : Equiv.Perm (Fin 3)) = s := by
    funext i
    show s (σ.symm (σ i)) = s i
    rw [σ.symm_apply_apply]
  have hinj : Function.Injective (s ∘ (σ.symm : Equiv.Perm (Fin 3))) :=
    hs.comp σ.symm.injective
  have := (H₀ _ hinj).reindex σ
  rwa [hcomp] at this

/-! ## What is known -/

/-- **Every product-one generating triple in a finite abelian group is three-point branch data.** -/
theorem isThreePointMonodromy_of_commGroup {H : Type} [CommGroup H] [Finite H] (h : Fin 3 → H)
    (hprod : (List.ofFn h).prod = 1) (htop : Subgroup.closure (Set.range h) = ⊤) :
    IsThreePointMonodromy h :=
  fun t ht => exists_cover_of_commGroup t ht h hprod htop

/-- **Every product-one generating triple in a dihedral group is three-point branch data.** -/
theorem isThreePointMonodromy_dihedral (n : ℕ) [NeZero n] (hn : 3 ≤ n) {h : Fin 3 → DihedralGroup n}
    (hprod : (List.ofFn h).prod = 1) (htop : Subgroup.closure (Set.range h) = ⊤) :
    IsThreePointMonodromy h :=
  fun _ hs => isMonodromyOver_dihedral n hn hprod htop hs

/-! ## The existence half of the correspondence, with the points forgotten -/

/-- **Over three branch points the existence half of the Riemann existence correspondence is a
statement about groups alone.**  It says of every finite group and every product-one generating
triple in it that the triple is three-point branch data; where the three points sit plays no part. -/
theorem geomRETExistence_iff_forall_isThreePointMonodromy {t : Fin 3 → k}
    (ht : Function.Injective t) :
    GeomRETExistence t ↔ ∀ (G : Type) [Group G] [Finite G] (h : Fin 3 → G),
      (List.ofFn h).prod = 1 → Subgroup.closure (Set.range h) = ⊤ → IsThreePointMonodromy h := by
  constructor
  · intro H G _ _ h hprod htop
    exact isThreePointMonodromy_of_isMonodromyOver ht (H h hprod htop)
  · intro H G _ _ h hprod htop
    exact H G h hprod htop t ht

end Rigidity.RET

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.Braid
import InverseGalois.Rigidity.RET.MonodromyGroup

/-!
# Branch data along the Hurwitz action

A cover sees its branch cycle at a point only up to conjugacy: the inertia groups at the places
over a fixed point form a single conjugacy class of subgroups, so any conjugate of a distinguished
inertia element is again one.  Consequently a branch datum depends on its tuple of cycles only
through the tuple of conjugacy classes, and only up to a simultaneous permutation of the cycles
and the points.

The Hurwitz move `braidTuple n` transposes the `n`-th and `(n+1)`-st conjugacy classes, so it is
absorbed by permuting the two branch points.  If the branch points are not prescribed — the
situation at three points, where any triple of distinct points can be moved to any other — the
permutation costs nothing and the entire braid-and-conjugation class of a realized tuple is
realized.

## Main results

* `Rigidity.RET.IsMonodromyOver.of_isConj` — the cycles may be conjugated one at a time.
* `Rigidity.RET.IsMonodromyOver.of_conjClasses` — a branch datum depends only on the conjugacy
  classes of its cycles, up to permuting cycles and points together.
* `Rigidity.RET.IsGenericMonodromy` — branch data over an unprescribed tuple of distinct points.
* `Rigidity.RET.IsGenericMonodromy.braidConj` — invariance under the Hurwitz action.
* `Rigidity.RET.isMonodromyGroupOver_of_braidConj_reps` — one representative of each
  braid-and-conjugation class suffices to realize a group.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

open GeomAKLB

/-! ## A branch datum depends only on the conjugacy classes of its cycles -/

/-- **Each branch cycle may be replaced by a conjugate, independently of the others.**  The
distinguished inertia elements at a point are closed under conjugation, because the places over
the point are permuted transitively by the deck group. -/
theorem IsMonodromyOver.of_isConj {G : Type} [Group G] [Finite G] {r : ℕ} {h h' : Fin r → G}
    {t : Fin r → k} (H₀ : IsMonodromyOver h t) (hc : ∀ i, IsConj (h i) (h' i)) :
    IsMonodromyOver h' t := by
  obtain ⟨L, e, hout, hinf, hin⟩ := H₀
  refine ⟨L, e, hout, hinf, fun i => ?_⟩
  obtain ⟨c, hc'⟩ := isConj_iff.mp (hc i)
  have hmap : e.symm (h' i) = e.symm c * e.symm (h i) * (e.symm c)⁻¹ := by
    rw [← hc', map_mul, map_mul, map_inv]
  rw [hmap]
  exact (hin i).conj (e.symm c)

/-- **A branch datum sees its cycles only through their conjugacy classes, and only up to a
simultaneous permutation of the cycles and the branch points.** -/
theorem IsMonodromyOver.of_conjClasses {G : Type} [Group G] [Finite G] {r : ℕ} {h h' : Fin r → G}
    {t : Fin r → k} (H₀ : IsMonodromyOver h t) (σ : Equiv.Perm (Fin r))
    (hcl : ∀ i, ConjClasses.mk (h' i) = ConjClasses.mk (h (σ i))) :
    IsMonodromyOver h' (t ∘ σ) :=
  (H₀.reindex σ).of_isConj fun i => ConjClasses.mk_eq_mk_iff_isConj.mp (hcl i).symm

/-- **A Hurwitz move on the cycles is absorbed by transposing the two branch points it moves.** -/
theorem IsMonodromyOver.braidTuple {G : Type} [Group G] [Finite G] {r n : ℕ} (hn : n + 1 < r)
    {h : Fin r → G} {t : Fin r → k} (H₀ : IsMonodromyOver h t) :
    IsMonodromyOver (Rigidity.braidTuple n h)
      (t ∘ Equiv.swap (⟨n, by omega⟩ : Fin r) ⟨n + 1, hn⟩) :=
  H₀.of_conjClasses _ (mk_braidTuple_apply hn h)

/-- **The inverse Hurwitz move is absorbed the same way.** -/
theorem IsMonodromyOver.braidTupleInv {G : Type} [Group G] [Finite G] {r n : ℕ} (hn : n + 1 < r)
    {h : Fin r → G} {t : Fin r → k} (H₀ : IsMonodromyOver h t) :
    IsMonodromyOver (Rigidity.braidTupleInv n h)
      (t ∘ Equiv.swap (⟨n, by omega⟩ : Fin r) ⟨n + 1, hn⟩) :=
  H₀.of_conjClasses _ (mk_braidTupleInv_apply hn h)

/-! ## Branch data over an unprescribed tuple of points -/

/-- **The tuple `h` is the branch-cycle system of a cover of the line branched over an arbitrary
prescribed tuple of distinct points.**  At three points this is `IsThreePointMonodromy`. -/
def IsGenericMonodromy {G : Type} [Group G] [Finite G] {r : ℕ} (h : Fin r → G) : Prop :=
  ∀ t : Fin r → k, Function.Injective t → IsMonodromyOver h t

/-- At three points, being realized over an arbitrary triple is three-point branch data. -/
theorem isThreePointMonodromy_iff_isGenericMonodromy {G : Type} [Group G] [Finite G]
    (h : Fin 3 → G) : IsThreePointMonodromy h ↔ IsGenericMonodromy h := Iff.rfl

/-- **Permuting the cycles and conjugating them one at a time preserves realizability over an
unprescribed tuple**, because the branch points may be permuted back. -/
theorem IsGenericMonodromy.of_conjClasses {G : Type} [Group G] [Finite G] {r : ℕ}
    {h h' : Fin r → G} (H₀ : IsGenericMonodromy h) (σ : Equiv.Perm (Fin r))
    (hcl : ∀ i, ConjClasses.mk (h' i) = ConjClasses.mk (h (σ i))) : IsGenericMonodromy h' := by
  intro t ht
  have hinj : Function.Injective (t ∘ (σ.symm : Equiv.Perm (Fin r))) := ht.comp σ.symm.injective
  have hmon := (H₀ _ hinj).of_conjClasses σ hcl
  have hcomp : (t ∘ (σ.symm : Equiv.Perm (Fin r))) ∘ (σ : Equiv.Perm (Fin r)) = t :=
    funext fun i => congrArg t (σ.symm_apply_apply i)
  rwa [hcomp] at hmon

/-- **The cycles may be permuted.** -/
theorem IsGenericMonodromy.reindex {G : Type} [Group G] [Finite G] {r : ℕ} {h : Fin r → G}
    (H₀ : IsGenericMonodromy h) (σ : Equiv.Perm (Fin r)) : IsGenericMonodromy (h ∘ σ) :=
  H₀.of_conjClasses σ fun _ => rfl

/-- **The cycles may be conjugated one at a time.** -/
theorem IsGenericMonodromy.of_isConj {G : Type} [Group G] [Finite G] {r : ℕ} {h h' : Fin r → G}
    (H₀ : IsGenericMonodromy h) (hc : ∀ i, IsConj (h i) (h' i)) : IsGenericMonodromy h' :=
  H₀.of_conjClasses (Equiv.refl _) fun i => (ConjClasses.mk_eq_mk_iff_isConj.2 (hc i)).symm

/-- **The cycles may be conjugated simultaneously.** -/
theorem IsGenericMonodromy.conj {G : Type} [Group G] [Finite G] {r : ℕ} {h : Fin r → G}
    (H₀ : IsGenericMonodromy h) (c : G) : IsGenericMonodromy fun i => c * h i * c⁻¹ :=
  fun t ht => (H₀ t ht).conj c

/-! ## Invariance under the Hurwitz action -/

/-- **A Hurwitz move preserves realizability over an unprescribed tuple of points.** -/
theorem IsGenericMonodromy.braidTuple {G : Type} [Group G] [Finite G] {r : ℕ} {h : Fin r → G}
    (H₀ : IsGenericMonodromy h) (n : ℕ) : IsGenericMonodromy (Rigidity.braidTuple n h) := by
  by_cases hn : n + 1 < r
  · exact H₀.of_conjClasses _ (mk_braidTuple_apply hn h)
  · rw [Rigidity.braidTuple_of_le (by omega) h]
    exact H₀

/-- **An inverse Hurwitz move preserves realizability over an unprescribed tuple of points.** -/
theorem IsGenericMonodromy.braidTupleInv {G : Type} [Group G] [Finite G] {r : ℕ} {h : Fin r → G}
    (H₀ : IsGenericMonodromy h) (n : ℕ) : IsGenericMonodromy (Rigidity.braidTupleInv n h) := by
  by_cases hn : n + 1 < r
  · exact H₀.of_conjClasses _ (mk_braidTupleInv_apply hn h)
  · rw [Rigidity.braidTupleInv_of_le (by omega) h]
    exact H₀

/-- **One elementary Hurwitz or conjugation move preserves realizability.** -/
theorem IsGenericMonodromy.braidConjStep {G : Type} [Group G] [Finite G] {r : ℕ}
    {h h' : Fin r → G} (H₀ : IsGenericMonodromy h) (hs : BraidConjStep h h') :
    IsGenericMonodromy h' := by
  cases hs with
  | braid n _ => exact H₀.braidTuple n
  | braidInv n _ => exact H₀.braidTupleInv n
  | conj c _ => exact H₀.conj c

/-- **The whole braid-and-conjugation class of a realized tuple is realized.**  This is the
algebraic shadow of moving the branch points around one another: the Hurwitz move only transposes
two branch points, and where the branch points are does not matter. -/
theorem IsGenericMonodromy.braidConj {G : Type} [Group G] [Finite G] {r : ℕ} {h h' : Fin r → G}
    (H₀ : IsGenericMonodromy h) (hb : BraidConj h h') : IsGenericMonodromy h' := by
  induction hb with
  | refl => exact H₀
  | tail _ hstep ih => exact ih.braidConjStep hstep

/-- **The braid-and-conjugation class of a three-point branch datum consists of three-point
branch data.** -/
theorem IsThreePointMonodromy.braidConj {G : Type} [Group G] [Finite G] {h h' : Fin 3 → G}
    (H₀ : IsThreePointMonodromy h) (hb : BraidConj h h') : IsThreePointMonodromy h' :=
  IsGenericMonodromy.braidConj H₀ hb

/-! ## Closure properties at the generic level -/

/-- **Branch data over an unprescribed tuple push forward along a surjection of groups.** -/
theorem IsGenericMonodromy.map {G H : Type} [Group G] [Finite G] [Group H] [Finite H] {r : ℕ}
    {h : Fin r → G} (H₀ : IsGenericMonodromy h) (π : G →* H) (hπ : Function.Surjective π) :
    IsGenericMonodromy fun i => π (h i) :=
  fun t ht => (H₀ t ht).map π hπ

/-- **Branch data over an unprescribed tuple transport along an isomorphism of groups.** -/
theorem IsGenericMonodromy.congr {G H : Type} [Group G] [Finite G] [Group H] [Finite H] {r : ℕ}
    {h : Fin r → G} (H₀ : IsGenericMonodromy h) (φ : G ≃* H) :
    IsGenericMonodromy fun i => φ (h i) :=
  fun t ht => (H₀ t ht).congr φ

/-- **Branch data of coprime order multiply, over an unprescribed tuple.** -/
theorem IsGenericMonodromy.prod_coprime {G₁ G₂ : Type} [Group G₁] [Finite G₁] [Group G₂]
    [Finite G₂] {r : ℕ} {h₁ : Fin r → G₁} {h₂ : Fin r → G₂}
    (hcop : Nat.Coprime (Nat.card G₁) (Nat.card G₂)) (H₁ : IsGenericMonodromy h₁)
    (H₂ : IsGenericMonodromy h₂) : IsGenericMonodromy fun i => (h₁ i, h₂ i) :=
  fun t ht => IsMonodromyOver.prod_coprime hcop (H₁ t ht) (H₂ t ht)

/-! ## Rigid class tuples -/

/-- **In a rigid class tuple, realizing one branch datum realizes them all.**  Rigidity says
exactly that the generating product-one tuples in the prescribed classes form a single orbit under
simultaneous conjugation, and simultaneous conjugation is one of the moves. -/
theorem isGenericMonodromy_of_rigid {G : Type} [Group G] [Finite G] {r : ℕ}
    {C : Fin r → ConjClasses G} (hZ : Subgroup.center G = ⊥)
    (hrigid : Nat.card (rigidTuples C) = Nat.card G) {g₀ : Fin r → G}
    (hg₀ : g₀ ∈ rigidTuples C) (H : IsGenericMonodromy g₀) {g : Fin r → G}
    (hg : g ∈ rigidTuples C) : IsGenericMonodromy g := by
  obtain ⟨x, hx⟩ := (rigid_card_iff_single_orbit hZ ⟨g₀, hg₀⟩).mp hrigid g₀ hg₀ g hg
  exact hx ▸ H.braidConj (BraidConj.conjAct x g₀)

/-- **A rigidity certificate reduces the existence half over its classes to a single tuple.** -/
theorem isGenericMonodromy_of_certificate {G : Type} [Group G] [Finite G]
    (cert : RigidityCertificate G) {g₀ : Fin cert.r → G} (hg₀ : g₀ ∈ rigidTuples cert.C)
    (H : IsGenericMonodromy g₀) {g : Fin cert.r → G} (hg : g ∈ rigidTuples cert.C) :
    IsGenericMonodromy g :=
  isGenericMonodromy_of_rigid (center_triv_iff_center_eq_bot.mp cert.center_triv) cert.rigid
    hg₀ H hg

/-! ## What this buys -/

/-- **Every product-one generating tuple in a finite abelian group is realized over an arbitrary
tuple of distinct points.** -/
theorem isGenericMonodromy_of_commGroup {A : Type} [CommGroup A] [Finite A] {r : ℕ} (h : Fin r → A)
    (hprod : (List.ofFn h).prod = 1) (htop : Subgroup.closure (Set.range h) = ⊤) :
    IsGenericMonodromy h :=
  fun t ht => exists_cover_of_commGroup t ht h hprod htop

/-- **A finite group is realized over a tuple of distinct points as soon as every product-one
generating tuple in it is braid-and-conjugation equivalent to a realized one.**  So the existence
half of the correspondence need only be checked on one representative of each class. -/
theorem isMonodromyGroupOver_of_braidConj_reps {G : Type} [Group G] [Finite G] {r : ℕ}
    {t : Fin r → k} (ht : Function.Injective t)
    (hrep : ∀ g : Fin r → G, (List.ofFn g).prod = 1 → Subgroup.closure (Set.range g) = ⊤ →
      ∃ g₀, BraidConj g₀ g ∧ IsGenericMonodromy g₀) :
    IsMonodromyGroupOver G t := by
  intro g hprod htop
  obtain ⟨g₀, hb, hg₀⟩ := hrep g hprod htop
  exact hg₀.braidConj hb t ht

end Rigidity.RET

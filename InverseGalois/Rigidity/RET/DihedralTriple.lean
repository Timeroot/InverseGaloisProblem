/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.DihedralExistence
import InverseGalois.Rigidity.RET.ProjectiveTransport

/-!
# Dihedral covers of the line over an arbitrary triple of branch points

The explicit dihedral covers are built over one convenient triple of points, `0`, `1/2` and `-1/2`,
because that is where the Kummer pullback used to construct them is cleanest.  Three distinct points
of the projective line carry no invariant, though, so a cover branched over that triple can be read
in a coordinate carrying the triple to any other, and the reading is again a cover, with the same
deck group and the same distinguished inertia generators at the moved points.

The existence half of the Riemann existence correspondence for dihedral groups therefore holds over
*every* ordered triple of distinct points of the line, with the ordering of the branch cycles
prescribed as well.

## Main results

* `Rigidity.RET.isMonodromyOver_dihedral` — every generating product-one triple in a dihedral group
  is the tuple of distinguished inertia generators of a cover branched over any prescribed triple of
  distinct points.
* `Rigidity.RET.exists_cover_dihedral_triple` — the same, written out as the cover it produces.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

open GeomAKLB

/-! ## Injectivity of a tuple from the size of its range -/

/-- A tuple whose range is as large as its index type is injective. -/
theorem injective_of_ncard_range {α : Type*} {r : ℕ} {t : Fin r → α}
    (h : (Set.range t).ncard = r) : Function.Injective t := by
  classical
  have hcoe : ((Finset.univ.image t : Finset α) : Set α) = Set.range t := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hcard : (Finset.univ.image t).card = (Finset.univ : Finset (Fin r)).card := by
    rw [← Set.ncard_coe_finset, hcoe, h, Finset.card_univ, Fintype.card_fin]
  have hinj := Finset.card_image_iff.mp hcard
  exact fun i j hij => hinj (Finset.mem_univ i) (Finset.mem_univ j) hij

/-! ## The three branch points of the explicit dihedral cover are distinct -/

/-- The branch locus of the explicit dihedral covers has three points. -/
theorem ncard_dihedralTriple : ({0, 2⁻¹, -2⁻¹} : Set k).ncard = 3 := by
  have h2 : (2 : k) ≠ 0 := by norm_num
  have hhalf : (2⁻¹ : k) ≠ 0 := inv_ne_zero h2
  have hne : (2⁻¹ : k) ≠ -2⁻¹ := by
    intro hcontra
    refine hhalf (add_self_eq_zero.mp ?_)
    nth_rewrite 2 [hcontra]
    exact add_neg_cancel _
  have h1 : (2⁻¹ : k) ∉ ({-2⁻¹} : Set k) := by
    simpa using hne
  have h0 : (0 : k) ∉ ({2⁻¹, -2⁻¹} : Set k) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun hcontra => hhalf hcontra.symm, fun hcontra => hhalf (neg_eq_zero.mp hcontra.symm)⟩
  rw [Set.ncard_insert_of_notMem h0, Set.ncard_insert_of_notMem h1, Set.ncard_singleton]

/-! ## Dihedral covers over an arbitrary triple -/

/-- **Every generating product-one triple in a dihedral group is the tuple of distinguished inertia
generators of a cover of the line branched over any prescribed triple of distinct points.**

The explicit construction produces a cover branched over `0`, `1/2` and `-1/2`, in an ordering
dictated by the triple; a coordinate change of the projective line then carries it to the
prescribed triple in the prescribed order. -/
theorem isMonodromyOver_dihedral (n : ℕ) [NeZero n] (hn : 3 ≤ n) {h : Fin 3 → DihedralGroup n}
    (hprod : (List.ofFn h).prod = 1) (htop : Subgroup.closure (Set.range h) = ⊤)
    {s : Fin 3 → k} (hs : Function.Injective s) : IsMonodromyOver h s := by
  obtain ⟨t, L, e, hr, hout, hinf, hin⟩ := exists_cover_dihedral n hn hprod htop
  have ht : Function.Injective t :=
    injective_of_ncard_range (by rw [hr]; exact ncard_dihedralTriple)
  exact isMonodromyOver_transport ht hs ⟨L, e, hout, hinf, hin⟩

/-- **The existence half of the Riemann existence correspondence, for dihedral groups, over an
arbitrary triple of branch points.** -/
theorem exists_cover_dihedral_triple (n : ℕ) [NeZero n] (hn : 3 ≤ n) {t : Fin 3 → k}
    (ht : Function.Injective t) {h : Fin 3 → DihedralGroup n}
    (hprod : (List.ofFn h).prod = 1) (htop : Subgroup.closure (Set.range h) = ⊤) :
    ∃ (L : LineCover) (e : L.deck ≃* DihedralGroup n),
      L.IsUnramifiedOutside (Set.range t) ∧ L.IsUnramifiedAtInfinity ∧
      ∀ i, L.IsInertiaGenAt (t i) (e.symm (h i)) :=
  isMonodromyOver_dihedral n hn hprod htop ht

end Rigidity.RET

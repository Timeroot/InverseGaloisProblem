/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.CoprimeProduct
import InverseGalois.Rigidity.RET.DihedralTriple
import InverseGalois.Rigidity.RET.MoveInfinity
import InverseGalois.Rigidity.RET.MobiusRelated

/-!
# The groups realized over a fixed branch locus

The existence half of the branch-cycle correspondence over a tuple `t` of points asks of *every*
finite group that every product-one generating tuple in it be the branch-cycle system of a cover
branched over `t`.  Splitting that quantifier off gives a property of a single group,
`IsMonodromyGroupOver G t`, and the existence half is the assertion that every finite group has it.

The point of isolating the class is that it has closure properties.  It contains every finite
abelian group, and at three points every dihedral group; and it is closed under direct products of
coprime order, because a product-one generating tuple in `G₁ × G₂` projects to product-one
generating tuples in the factors and coprime branch data over a common locus multiply.  Combining
these produces branch data over three points in groups that are neither abelian nor dihedral.

## Main results

* `Rigidity.RET.IsMonodromyGroupOver` — the property of a single finite group.
* `Rigidity.RET.geomRETExistence_iff_forall_isMonodromyGroupOver` — the existence half is exactly
  this property, for every finite group.
* `Rigidity.RET.IsMonodromyGroupOver.prod_coprime` — closure under coprime direct products.
* `Rigidity.RET.isMonodromyGroupOver_commGroup`, `Rigidity.RET.isMonodromyGroupOver_dihedral` — the
  two families known unconditionally.
* `Rigidity.RET.isThreePointMonodromy_dihedral_prod` — a dihedral group times an abelian group of
  coprime order is realized over any three points.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

open GeomAKLB

/-! ## Tuples under a homomorphism -/

/-- The ordered product of a tuple is carried along by a homomorphism. -/
theorem prod_ofFn_map {G H : Type*} [Group G] [Group H] (f : G →* H) {r : ℕ} (h : Fin r → G) :
    (List.ofFn fun i => f (h i)).prod = f (List.ofFn h).prod := by
  rw [map_list_prod, List.map_ofFn]
  rfl

/-! ## The class of groups realized over a fixed branch locus -/

/-- **The finite group `G` is realized over `t`**: every tuple in `G` which generates it and has
ordered product `1` is the branch-cycle system of a cover of the line with deck group `G`,
unramified outside the `tᵢ` and infinity. -/
def IsMonodromyGroupOver (G : Type) [Group G] [Finite G] {r : ℕ} (t : Fin r → k) : Prop :=
  ∀ h : Fin r → G, (List.ofFn h).prod = 1 → Subgroup.closure (Set.range h) = ⊤ →
    IsMonodromyOver h t

/-- **The existence half of the correspondence over `t` says exactly that every finite group is
realized over `t`.** -/
theorem geomRETExistence_iff_forall_isMonodromyGroupOver {r : ℕ} (t : Fin r → k) :
    GeomRETExistence t ↔ ∀ (G : Type) [Group G] [Finite G], IsMonodromyGroupOver G t :=
  ⟨fun H _ _ _ h hprod htop => H h hprod htop, fun H _ _ _ h hprod htop => H _ h hprod htop⟩

/-- **Being realized over `t` transports along an isomorphism of groups.** -/
theorem IsMonodromyGroupOver.congr {G H : Type} [Group G] [Finite G] [Group H] [Finite H]
    {r : ℕ} {t : Fin r → k} (hG : IsMonodromyGroupOver G t) (φ : G ≃* H) :
    IsMonodromyGroupOver H t := by
  intro h hprod htop
  have hprod' : (List.ofFn fun i => φ.symm (h i)).prod = 1 := by
    have hm := prod_ofFn_map (φ.symm : H →* G) h
    rw [hprod, map_one] at hm
    exact hm
  have htop' : Subgroup.closure (Set.range fun i => φ.symm (h i)) = ⊤ :=
    closure_range_map_eq_top (φ.symm : H →* G) φ.symm.surjective htop
  have hmon := (hG _ hprod' htop').congr φ
  have hfun : (fun i => φ (φ.symm (h i))) = h := funext fun i => φ.apply_symm_apply (h i)
  rwa [hfun] at hmon

/-- **Being realized is invariant under a coordinate change of the line.** -/
theorem IsMonodromyGroupOver.mobius {G : Type} [Group G] [Finite G] {r : ℕ} {t s : Fin r → k}
    (hrel : MobiusRelated t s) (hG : IsMonodromyGroupOver G t) : IsMonodromyGroupOver G s :=
  fun h hprod htop => (hG h hprod htop).mobius hrel

/-! ## Closure under coprime direct products -/

/-- **A direct product of two groups of coprime order realized over `t` is realized over `t`.**

A product-one generating tuple in `G₁ × G₂` projects to a product-one generating tuple in each
factor, and coprime branch data over one and the same branch locus multiply. -/
theorem IsMonodromyGroupOver.prod_coprime {G₁ G₂ : Type} [Group G₁] [Finite G₁] [Group G₂]
    [Finite G₂] {r : ℕ} {t : Fin r → k} (hcop : Nat.Coprime (Nat.card G₁) (Nat.card G₂))
    (H₁ : IsMonodromyGroupOver G₁ t) (H₂ : IsMonodromyGroupOver G₂ t) :
    IsMonodromyGroupOver (G₁ × G₂) t := by
  intro h hprod htop
  have hfst : Function.Surjective (MonoidHom.fst G₁ G₂) := fun a => ⟨(a, 1), rfl⟩
  have hsnd : Function.Surjective (MonoidHom.snd G₁ G₂) := fun b => ⟨(1, b), rfl⟩
  have h1 : IsMonodromyOver (fun i => (h i).1) t := by
    refine H₁ _ ?_ (closure_range_map_eq_top (MonoidHom.fst G₁ G₂) hfst htop)
    have hm := prod_ofFn_map (MonoidHom.fst G₁ G₂) h
    rw [hprod, map_one] at hm
    exact hm
  have h2 : IsMonodromyOver (fun i => (h i).2) t := by
    refine H₂ _ ?_ (closure_range_map_eq_top (MonoidHom.snd G₁ G₂) hsnd htop)
    have hm := prod_ofFn_map (MonoidHom.snd G₁ G₂) h
    rw [hprod, map_one] at hm
    exact hm
  have hmon := IsMonodromyOver.prod_coprime hcop h1 h2
  have hfun : (fun i => ((h i).1, (h i).2)) = h := funext fun i => rfl
  rwa [hfun] at hmon

/-! ## What is realized unconditionally -/

/-- **Every finite abelian group is realized over every tuple of distinct points.** -/
theorem isMonodromyGroupOver_commGroup (A : Type) [CommGroup A] [Finite A] {r : ℕ}
    {t : Fin r → k} (ht : Function.Injective t) : IsMonodromyGroupOver A t :=
  fun h hprod htop => exists_cover_of_commGroup t ht h hprod htop

/-- **Every dihedral group is realized over every triple of distinct points.** -/
theorem isMonodromyGroupOver_dihedral (n : ℕ) [NeZero n] (hn : 3 ≤ n) {t : Fin 3 → k}
    (ht : Function.Injective t) : IsMonodromyGroupOver (DihedralGroup n) t :=
  fun _ hprod htop => isMonodromyOver_dihedral n hn hprod htop ht

/-- **A dihedral group times an abelian group of coprime order is realized over every triple of
distinct points.**  These are the first three-point branch data in groups that are neither abelian
nor dihedral. -/
theorem isMonodromyGroupOver_dihedral_prod (n : ℕ) [NeZero n] (hn : 3 ≤ n) (A : Type)
    [CommGroup A] [Finite A] (hcop : Nat.Coprime (2 * n) (Nat.card A)) {t : Fin 3 → k}
    (ht : Function.Injective t) : IsMonodromyGroupOver (DihedralGroup n × A) t := by
  refine IsMonodromyGroupOver.prod_coprime ?_ (isMonodromyGroupOver_dihedral n hn ht)
    (isMonodromyGroupOver_commGroup A ht)
  rwa [DihedralGroup.nat_card]

/-- **A product-one generating triple in a dihedral group times an abelian group of coprime order
is three-point branch data.** -/
theorem isThreePointMonodromy_dihedral_prod (n : ℕ) [NeZero n] (hn : 3 ≤ n) {A : Type}
    [CommGroup A] [Finite A] (hcop : Nat.Coprime (2 * n) (Nat.card A))
    {h : Fin 3 → DihedralGroup n × A} (hprod : (List.ofFn h).prod = 1)
    (htop : Subgroup.closure (Set.range h) = ⊤) : IsThreePointMonodromy h :=
  fun _ ht => isMonodromyGroupOver_dihedral_prod n hn A hcop ht h hprod htop

end Rigidity.RET

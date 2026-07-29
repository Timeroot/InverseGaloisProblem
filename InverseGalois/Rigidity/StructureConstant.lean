/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Rigidity.Certificate

/-!
# The structure constant: rigidity as a single conjugacy orbit

The `rigid` field of a `RigidityCertificate` is stored as the **cardinality condition**
`Nat.card (rigidTuples C) = Nat.card G` (structure constant `= 1`), because that form is directly
`decide`-friendly for a concrete finite group.  This file proves that — for a **centerless** group
— this cheap count is *exactly* the classical rigidity condition: the generating product-one
tuples in the prescribed classes form a **single orbit** under simultaneous conjugation.

The mechanism is orbit–stabilizer:

* `smul_mem_rigidTuples` — `rigidTuples C` is invariant under simultaneous conjugation
  (`ConjAct G` acting diagonally), because conjugation is an automorphism preserving conjugacy
  classes, products, and generation.
* `stabilizer_conjAct_eq_bot` — a **generating** tuple has trivial stabilizer, since an element
  commuting with a generating set lies in the center (`= ⊥`).
* `card_orbit_conjAct` — hence every generating tuple's orbit has exactly `Nat.card G` elements.
* `rigid_card_iff_single_orbit` — the count equals `Nat.card G` iff all the tuples lie in one
  orbit (are pairwise simultaneously conjugate).

## Main results

* `Rigidity.rigid_card_iff_single_orbit` — the soundness theorem tying the certificate's
  cardinality condition to classical rigidity.
-/

open scoped BigOperators

open MulAction Subgroup

namespace Rigidity

variable {G : Type*} [Group G]

/-- **Simultaneous conjugation preserves the rigid tuples.**  For `x : ConjAct G`, if `g` lies in
`rigidTuples C` then so does the coordinatewise conjugate `x • g`: conjugation fixes each conjugacy
class, sends a product-one tuple to a product-one tuple, and preserves generation. -/
theorem smul_mem_rigidTuples {r : ℕ} {C : Fin r → ConjClasses G} {g : Fin r → G}
    (hg : g ∈ rigidTuples C) (x : ConjAct G) : x • g ∈ rigidTuples C := by
  obtain ⟨hclass, hprod, hgen⟩ := hg
  set c := ConjAct.ofConjAct x with hc
  set f : G →* G := (MulAut.conj c).toMonoidHom with hf
  have hφ : ∀ i, (x • g) i = f (g i) := fun i => by
    rw [Pi.smul_apply, ConjAct.smul_eq_mulAut_conj]; rfl
  have hfun : (x • g) = f ∘ g := funext hφ
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [hφ i, ← hclass i, ConjClasses.mk_eq_mk_iff_isConj]
    simp only [hf, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact isConj_iff.mpr ⟨c⁻¹, by group⟩
  · have hlist : List.ofFn (x • g) = (List.ofFn g).map f := by rw [List.map_ofFn, ← hfun]
    rw [hlist, ← map_list_prod f, hprod, map_one]
  · have hrange : Set.range (x • g) = f '' Set.range g := by rw [← Set.range_comp, ← hfun]
    rw [hrange, ← MonoidHom.map_closure f, hgen]
    exact Subgroup.map_top_of_surjective f (MulAut.conj c).surjective

/-- **A generating tuple has trivial stabilizer under simultaneous conjugation**, provided the
group is centerless.  An element `x` fixing `g` coordinatewise commutes with every `g i`, hence
with the whole generated group `⟨g⟩ = G`, so `ofConjAct x` lies in the center `= ⊥`. -/
theorem stabilizer_conjAct_eq_bot {r : ℕ} {g : Fin r → G}
    (hgen : Subgroup.closure (Set.range g) = ⊤) (hZ : Subgroup.center G = ⊥) :
    MulAction.stabilizer (ConjAct G) g = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [MulAction.mem_stabilizer_iff] at hx
  have hcomm : ConjAct.ofConjAct x ∈ Subgroup.centralizer (Set.range g) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro h ⟨i, rfl⟩
    have hi : x • g i = g i := congrFun hx i
    rw [ConjAct.smul_def, mul_inv_eq_iff_eq_mul] at hi
    exact hi.symm
  have hcenter : ConjAct.ofConjAct x ∈ Subgroup.center G := by
    rw [← Subgroup.centralizer_univ, ← Subgroup.coe_top, ← hgen, Subgroup.centralizer_closure]
    exact hcomm
  rw [hZ, Subgroup.mem_bot] at hcenter
  have hx1 : x = 1 := by
    have := congrArg ConjAct.toConjAct hcenter
    rwa [ConjAct.toConjAct_ofConjAct, map_one] at this
  rw [Subgroup.mem_bot]; exact hx1

/-- **Every generating tuple's simultaneous-conjugacy orbit has exactly `|G|` elements**, by
orbit–stabilizer with the trivial stabilizer of `stabilizer_conjAct_eq_bot`. -/
theorem card_orbit_conjAct {r : ℕ} [Finite G] {g : Fin r → G}
    (hgen : Subgroup.closure (Set.range g) = ⊤) (hZ : Subgroup.center G = ⊥) :
    Nat.card (MulAction.orbit (ConjAct G) g) = Nat.card G := by
  rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (ConjAct G) g),
    stabilizer_conjAct_eq_bot hgen hZ,
    Nat.card_congr (QuotientGroup.quotientBot).toEquiv]
  exact Nat.card_congr ConjAct.ofConjAct.toEquiv

/-- **Soundness of the cardinality form of rigidity.**  For a centerless group with at least one
generating product-one tuple in the prescribed classes, the certificate's structure-constant
condition `Nat.card (rigidTuples C) = Nat.card G` holds **iff** those tuples form a single orbit
under simultaneous conjugation — i.e. any two are related by a global conjugation.  This is exactly
the classical statement that the structure constant equals `1`. -/
theorem rigid_card_iff_single_orbit {r : ℕ} {C : Fin r → ConjClasses G} [Finite G]
    (hZ : Subgroup.center G = ⊥) (hne : (rigidTuples C).Nonempty) :
    Nat.card (rigidTuples C) = Nat.card G ↔
      ∀ g₁ ∈ rigidTuples C, ∀ g₂ ∈ rigidTuples C, ∃ x : ConjAct G, x • g₁ = g₂ := by
  obtain ⟨g₀, hg₀⟩ := hne
  set S := rigidTuples C with hS
  set O := MulAction.orbit (ConjAct G) g₀ with hO
  have hSfin : S.Finite := Set.toFinite _
  have hsub : O ⊆ S := by rintro _ ⟨x, rfl⟩; exact smul_mem_rigidTuples hg₀ x
  have hcardO : O.ncard = Nat.card G := by
    rw [← Nat.card_coe_set_eq]; exact card_orbit_conjAct hg₀.2.2 hZ
  constructor
  · -- count `= |G|` ⇒ `O = S`, so every pair is conjugate through the common base point
    intro hcard
    have hcardS : S.ncard = Nat.card G := by rw [← Nat.card_coe_set_eq]; exact hcard
    have hSO : O = S :=
      Set.eq_of_subset_of_ncard_le hsub (hcardS.trans hcardO.symm).le hSfin
    intro g₁ hg₁ g₂ hg₂
    rw [← hSO] at hg₁ hg₂
    obtain ⟨x₁, hx₁⟩ := hg₁
    obtain ⟨x₂, hx₂⟩ := hg₂
    have hx₁' : x₁ • g₀ = g₁ := hx₁
    have hx₂' : x₂ • g₀ = g₂ := hx₂
    exact ⟨x₂ * x₁⁻¹, by rw [← hx₁', ← hx₂', smul_smul, mul_assoc, inv_mul_cancel, mul_one]⟩
  · -- single orbit ⇒ `S ⊆ O`, hence `S = O` and the counts agree
    intro hforall
    have hSsub : S ⊆ O := fun g₁ hg₁ => hforall g₀ hg₀ g₁ hg₁
    have hSO : S = O := hsub.antisymm' hSsub
    rw [hSO, Nat.card_coe_set_eq, hcardO]

end Rigidity

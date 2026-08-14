/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.DeckMonodromy
import InverseGalois.Rigidity.RET.Analytic.PathConnected

/-!
# A group acting on the roots of a family by continuous formulas is the monodromy group

The automorphisms of a Galois cover of the line act on the roots of a defining equation by
substituting a formula: the conjugate of the generator is a polynomial in the generator, and the
same polynomial, with its coefficients specialized, permutes the roots of every specialization of
the equation away from finitely many parameters.

This file packages exactly that data — one continuous formula per group element, permuting the
roots of every good specialization, with the group law and with distinct elements moving a root to
distinct places — and shows that it makes the group act on the root cover by deck transformations.
When the group has as many elements as the equation has degree, the action on a fibre is simply
transitive, and for an irreducible equation the monodromy group is then a copy of the group.

## Main definitions

* `Rigidity.RET.Analytic.RationalDeck` — a group of continuous formulas permuting the roots of a
  family.

## Main results

* `Rigidity.RET.Analytic.RationalDeck.mulAction` — the induced action on the root cover.
* `Rigidity.RET.Analytic.RationalDeck.monodromyEquiv` — for an irreducible family whose degree is
  the order of the group, the monodromy group of the root cover is isomorphic to the group.
-/

open Polynomial Rigidity.RET

noncomputable section

namespace Rigidity.RET.Analytic

variable {P : Polynomial (Polynomial ℂ)} {S : Finset ℂ} {G : Type} [Group G]

/-- **A group of continuous formulas permuting the roots of a family.**

`act g z w` is where the automorphism `g` sends the root `w` of the specialization at `z`.  The
formula is continuous in the pair `(z, w)` away from the exceptional parameters, carries roots to
roots, respects the group law on roots, and separates group elements at every root. -/
structure RationalDeck (P : Polynomial (Polynomial ℂ)) (S : Finset ℂ) (G : Type) [Group G] where
  /-- the formula: where `g` sends the root `w` of the specialization at `z`. -/
  act : G → ℂ → ℂ → ℂ
  /-- the formula is continuous away from the exceptional parameters. -/
  continuousOn : ∀ g : G,
    ContinuousOn (fun q : ℂ × ℂ => act g q.1 q.2) {q : ℂ × ℂ | q.1 ∉ (S : Set ℂ)}
  /-- the formula carries roots to roots. -/
  isRoot : ∀ (g : G) {z w : ℂ}, z ∉ (S : Set ℂ) → (spec P z).IsRoot w →
    (spec P z).IsRoot (act g z w)
  /-- the identity acts trivially on roots. -/
  act_one : ∀ {z w : ℂ}, z ∉ (S : Set ℂ) → (spec P z).IsRoot w → act 1 z w = w
  /-- the formulas compose according to the group law. -/
  act_mul : ∀ (g h : G) {z w : ℂ}, z ∉ (S : Set ℂ) → (spec P z).IsRoot w →
    act (g * h) z w = act g z (act h z w)
  /-- distinct group elements move a root to distinct places. -/
  injOn : ∀ {z w : ℂ}, z ∉ (S : Set ℂ) → (spec P z).IsRoot w →
    Function.Injective fun g : G => act g z w

namespace RationalDeck

variable (D : RationalDeck P S G)

theorem fst_notMem (e : ↥(rootProj P ⁻¹' ((S : Set ℂ)ᶜ))) :
    ((e : rootVariety P) : ℂ × ℂ).1 ∉ (S : Set ℂ) := e.2

theorem isRoot_snd (e : ↥(rootProj P ⁻¹' ((S : Set ℂ)ᶜ))) :
    (spec P ((e : rootVariety P) : ℂ × ℂ).1).IsRoot ((e : rootVariety P) : ℂ × ℂ).2 :=
  (e : rootVariety P).2

/-- The point of the root cover reached from `e` by the formula of `g`. -/
def smul (g : G) (e : ↥(rootProj P ⁻¹' ((S : Set ℂ)ᶜ))) : ↥(rootProj P ⁻¹' ((S : Set ℂ)ᶜ)) :=
  ⟨⟨(((e : rootVariety P) : ℂ × ℂ).1,
      D.act g ((e : rootVariety P) : ℂ × ℂ).1 ((e : rootVariety P) : ℂ × ℂ).2),
    D.isRoot g (fst_notMem e) (isRoot_snd e)⟩, e.2⟩

theorem coe_smul (g : G) (e : ↥(rootProj P ⁻¹' ((S : Set ℂ)ᶜ))) :
    ((D.smul g e : ↥(rootProj P ⁻¹' ((S : Set ℂ)ᶜ))) : ℂ × ℂ)
      = (((e : rootVariety P) : ℂ × ℂ).1,
          D.act g ((e : rootVariety P) : ℂ × ℂ).1 ((e : rootVariety P) : ℂ × ℂ).2) :=
  rfl

/-- **The formulas make the group act on the root cover.** -/
def mulAction : MulAction G ↥(rootProj P ⁻¹' ((S : Set ℂ)ᶜ)) where
  smul := D.smul
  one_smul e := by
    show D.smul 1 e = e
    refine Subtype.ext (Subtype.ext ?_)
    rw [coe_smul, D.act_one (fst_notMem e) (isRoot_snd e)]
  mul_smul g h e := by
    show D.smul (g * h) e = D.smul g (D.smul h e)
    refine Subtype.ext (Subtype.ext ?_)
    rw [coe_smul, coe_smul, coe_smul, D.act_mul g h (fst_notMem e) (isRoot_snd e)]

/-- The action is by maps over the parameter plane. -/
theorem puncturedProj_smul (g : G) (e : ↥(rootProj P ⁻¹' ((S : Set ℂ)ᶜ))) :
    puncturedProj P S (D.smul g e) = puncturedProj P S e :=
  Subtype.ext rfl

/-- The action is by continuous maps. -/
theorem continuous_smul (g : G) : Continuous fun e : ↥(rootProj P ⁻¹' ((S : Set ℂ)ᶜ)) =>
    D.smul g e := by
  have hval : Continuous fun e : ↥(rootProj P ⁻¹' ((S : Set ℂ)ᶜ)) =>
      ((e : rootVariety P) : ℂ × ℂ) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hmem : ∀ e : ↥(rootProj P ⁻¹' ((S : Set ℂ)ᶜ)),
      ((e : rootVariety P) : ℂ × ℂ) ∈ {q : ℂ × ℂ | q.1 ∉ (S : Set ℂ)} := fun e => e.2
  have hact : Continuous fun e : ↥(rootProj P ⁻¹' ((S : Set ℂ)ᶜ)) =>
      D.act g ((e : rootVariety P) : ℂ × ℂ).1 ((e : rootVariety P) : ℂ × ℂ).2 :=
    (D.continuousOn g).comp_continuous hval hmem
  exact ((hval.fst.prodMk hact).subtype_mk _).subtype_mk _

/-! ### Simple transitivity on a fibre -/

/-- The orbit map of a point of a fibre, as a map into that fibre. -/
def orbitFibre {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ))
    (e₀ : puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}) (g : G) :
    puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))} :=
  ⟨D.smul g (e₀ : ↥(rootProj P ⁻¹' ((S : Set ℂ)ᶜ))),
    by rw [Set.mem_preimage, D.puncturedProj_smul]; exact e₀.2⟩

theorem injective_orbitFibre {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ))
    (e₀ : puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}) :
    Function.Injective (D.orbitFibre hz₀ e₀) := by
  intro g h hgh
  refine D.injOn (fst_notMem (e₀ : ↥(rootProj P ⁻¹' ((S : Set ℂ)ᶜ))))
    (isRoot_snd (e₀ : ↥(rootProj P ⁻¹' ((S : Set ℂ)ᶜ)))) ?_
  have hval := congrArg
    (fun e : ↥(puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}) =>
      (((e : ↥(rootProj P ⁻¹' ((S : Set ℂ)ᶜ))) : rootVariety P) : ℂ × ℂ).2) hgh
  exact hval

/-- **The action on a fibre is transitive** once the group is as large as the degree. -/
theorem surjective_orbitFibre [Finite G] (hP : P.Monic)
    (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ))
    (hcard : Nat.card G = P.natDegree)
    (e₀ : puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}) :
    Function.Surjective (D.orbitFibre hz₀ e₀) := by
  haveI : Finite (puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}) :=
    (finite_puncturedFiber hP hz₀).to_subtype
  haveI := Fintype.ofFinite G
  haveI := Fintype.ofFinite (puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))})
  have hcards : Fintype.card G
      = Fintype.card (puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard,
      card_puncturedFiber hP hS hz₀]
  exact ((Fintype.bijective_iff_injective_and_card _).2
    ⟨D.injective_orbitFibre hz₀ e₀, hcards⟩).2

/-! ### The monodromy group -/

/-- **The monodromy group of an irreducible family carrying a group of formulas of the right size
is a copy of that group.** -/
def monodromyEquiv [Finite G] (hP : P.Monic) (hdeg : 0 < P.natDegree) (hirr : Irreducible P)
    (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ))
    (hcard : Nat.card G = P.natDegree)
    (e₀ : puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}) :
    (monodromyHom hP hS hz₀).range ≃* G := by
  letI : MulAction G ↥(rootProj P ⁻¹' ((S : Set ℂ)ᶜ)) := D.mulAction
  haveI := pathConnectedSpace_punctured hP hdeg hirr hS
  have hsmul : ∀ (g : G) (e : ↥(rootProj P ⁻¹' ((S : Set ℂ)ᶜ))), g • e = D.smul g e :=
    fun _ _ => rfl
  refine monodromyRangeEquiv (isCoveringMap_puncturedProj hP hS)
    (fun g => by simpa only [hsmul] using D.continuous_smul g)
    (fun g e => by rw [hsmul]; exact D.puncturedProj_smul g e) e₀ ?_ ?_
  · intro g hg
    have hone : D.orbitFibre hz₀ e₀ g = D.orbitFibre hz₀ e₀ 1 := by
      refine Subtype.ext ?_
      show D.smul g (e₀ : ↥(rootProj P ⁻¹' ((S : Set ℂ)ᶜ)))
        = D.smul 1 (e₀ : ↥(rootProj P ⁻¹' ((S : Set ℂ)ᶜ)))
      rw [← hsmul, ← hsmul, hg, one_smul]
    exact D.injective_orbitFibre hz₀ e₀ hone
  · intro e
    obtain ⟨g, hg⟩ := D.surjective_orbitFibre hP hS hz₀ hcard e₀ e
    exact ⟨g, by rw [hsmul]; exact congrArg Subtype.val hg⟩

end RationalDeck

end Rigidity.RET.Analytic

end

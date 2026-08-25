/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Family

/-!
# A section-valued two-cocycle that is locally a coboundary is a coboundary

A group acting on a family of modules indexed by a set with a group action acts on the group of
sections of the family.  A two-cocycle for that action assigns to each pair of group elements a
section, and its value at a single index is only acted on by the stabiliser of that index.  The
question this file answers is whether the cocycle can be reconstituted from those local pieces:
if, at every index, the restriction of the cocycle to the stabiliser is a coboundary for the
stabiliser, is the cocycle itself a coboundary?

It is, and the proof is an explicit construction.  Two specialisations of the cocycle identity do
all the work.  The first expresses the value of the cocycle at an arbitrary index in terms of its
values at a chosen index of the same orbit, transported there by any group element carrying one to
the other.  The second, obtained from the first by taking both indices to be the chosen one, says
that the function `(s, y) ↦ f s y` on the stabiliser is a twisted cocycle in its first variable.
Subtracting the local coboundary datum turns that twisted cocycle into a genuine crossed
homomorphism in the first variable, which therefore extends from the stabiliser to the whole group
once a transversal for the right cosets of the stabiliser is chosen.  The extension is exactly the
correction term needed to turn the local trivialisation into a global one, and the resulting
one-cochain is well defined because the corrections transform correctly under the stabiliser.

Nothing is assumed to be finite: neither the group, nor the index set, nor the orbits.  The
construction also keeps track of an invariant family of subgroups, so that a cocycle whose values
lie in the subgroups away from a fixed invariant set of indices is a coboundary of a cochain with
the same property.  That refinement is what makes the statement usable for a restricted product
such as the ideles, where a section is admissible only when it is a unit at all but finitely many
indices.

## Main definitions

* `InverseGalois.CFT.FamilyAction.IsCocycle₂`: a two-cocycle for the action on the sections of a
  family of modules.

## Main results

* `InverseGalois.CFT.FamilyAction.transport_apply_cocycle`: the value of a two-cocycle at an index,
  transported to another index by a group element carrying the first to the second.
* `InverseGalois.CFT.FamilyAction.exists_equivariantCochain`: from a trivialisation of a
  two-cocycle over the stabiliser of an index, **a one-cochain on the whole group, with values in
  the module at that index, that trivialises the cocycle and is equivariant for the stabiliser.**
* `InverseGalois.CFT.FamilyAction.exists_coboundary_mem`: **a two-cocycle that is a coboundary over
  the stabiliser of every index is a coboundary**, by a one-cochain whose values lie in a given
  invariant family of subgroups wherever the cocycle's do.
* `InverseGalois.CFT.FamilyAction.exists_coboundary`: the same statement without the bookkeeping of
  subgroups.

## Tags

group cohomology, two-cocycle, coboundary, family of modules, sections, stabiliser, idele
-/

namespace InverseGalois.CFT

variable {G X : Type*} [Group G] [MulAction G X]
  {M : X → Type*} [∀ x, AddCommGroup (M x)]

namespace FamilyAction

variable {F : FamilyAction M G}

/-- **A two-cocycle for the action of a group on the sections of a family of modules.**  This is
the usual inhomogeneous condition in degree two, written for the action assembled from the
transport isomorphisms of the family. -/
def IsCocycle₂ (F : FamilyAction M G) (f : G → G → ∀ x, M x) : Prop :=
  ∀ g h j : G, F.familyAut g (f h j) + f g (h * j) = f (g * h) j + f g h

variable {f : G → G → ∀ x, M x}

/-- **The value of a two-cocycle at an index, transported to another index** by a group element
carrying the first index to the second.  The right-hand side involves only the values of the
cocycle at the target index, so this expresses the whole cocycle over an orbit in terms of its
values at a single point of the orbit. -/
theorem transport_apply_cocycle (hf : F.IsCocycle₂ f) (y g h : G) {x x₀ : X} (hy : y • x = x₀) :
    F.transport hy (f g h x) = f (y * g) h x₀ - f y (g * h) x₀ + f y g x₀ := by
  have h1 := congrFun (hf y g h) (y • x)
  simp only [Pi.add_apply, F.familyAut_apply_smul] at h1
  have h2 := congrArg (famCast M hy) h1
  rw [map_add, map_add, famCast_apply_section, famCast_apply_section, famCast_apply_section,
    ← transport_apply] at h2
  rw [eq_sub_of_add_eq h2]
  abel

/-- **A trivialisation of a two-cocycle over the stabiliser of an index spreads out to the whole
group.**  Given a one-cochain on the stabiliser of an index whose coboundary is the restriction of
the cocycle there, there is a one-cochain on the whole group, with values in the module at that
index, which computes every transported value of the cocycle and is equivariant for the stabiliser.
Its values stay inside any subgroup containing the values of the cocycle and of the given cochain.

The construction subtracts the given cochain from the cocycle to obtain a crossed homomorphism in
the first variable, and extends it over a transversal for the right cosets of the stabiliser. -/
theorem exists_equivariantCochain (hf : F.IsCocycle₂ f) (x₀ : X) (c : G → M x₀)
    (hc : ∀ (s t : G) (hs : s • x₀ = x₀), t • x₀ = x₀ →
      f s t x₀ = F.transport hs (c t) - c (s * t) + c s) :
    ∃ Ψ : G → G → M x₀,
      (∀ (s : G) (hs : s • x₀ = x₀) (y g : G), Ψ (s * y) g = F.transport hs (Ψ y g)) ∧
      (∀ (y g h : G) {x : X} (hy : y • x = x₀),
        F.transport hy (f g h x) = Ψ (y * g) h - Ψ y (g * h) + Ψ y g) ∧
      (∀ N : AddSubgroup (M x₀), (∀ a b : G, f a b x₀ ∈ N) → (∀ a : G, c a ∈ N) →
        ∀ y g : G, Ψ y g ∈ N) := by
  classical
  set S : Subgroup G := MulAction.stabilizer G x₀ with hS
  set D : G → G → M x₀ := fun s y => f s y x₀ - c s with hD
  have E1 : ∀ (s t : G) (hs : s • x₀ = x₀), t • x₀ = x₀ → ∀ y : G,
      D (s * t) y = F.transport hs (D t y) + D s (t * y) := by
    intro s t hs ht y
    have h1 := transport_apply_cocycle hf s t y hs
    have h2 := hc s t hs ht
    simp only [hD, map_sub]
    rw [h1, h2]
    abel
  -- a transversal for the right cosets of the stabiliser
  let rel : Setoid G := QuotientGroup.rightRel S
  let R : G → G := fun y => (Quotient.mk rel y).out
  have hRmk : ∀ y : G, Quotient.mk rel (R y) = Quotient.mk rel y := fun y => Quotient.out_eq _
  have hRmem : ∀ y : G, y * (R y)⁻¹ ∈ S := by
    intro y
    exact (QuotientGroup.rightRel_apply (s := S)).1 (Quotient.exact (hRmk y))
  have hRsmul : ∀ (s : G), s ∈ S → ∀ y : G, R (s * y) = R y := by
    intro s hs y
    have hq : Quotient.mk rel (s * y) = Quotient.mk rel y := by
      apply Quotient.sound
      show rel.r (s * y) y
      rw [QuotientGroup.rightRel_apply]
      simpa using hs
    simp only [R, hq]
  set e : G → M x₀ := fun y => D (y * (R y)⁻¹) (R y) with he
  have hsg : ∀ y : G, y * (R y)⁻¹ * R y = y := by
    intro y; group
  have hE : ∀ (s : G) (hs : s • x₀ = x₀) (y : G),
      e (s * y) = F.transport hs (e y) + D s y := by
    intro s hs y
    have hRy := hRsmul s hs y
    have ht : (y * (R y)⁻¹) • x₀ = x₀ := hRmem y
    simp only [he, hRy]
    rw [mul_assoc s y (R y)⁻¹, E1 s (y * (R y)⁻¹) hs ht (R y), hsg y]
  set Ψ : G → G → M x₀ := fun y g => f y g x₀ - e (y * g) + e y with hΨdef
  have hΨ : ∀ y g : G, Ψ y g = f y g x₀ - e (y * g) + e y := fun _ _ => rfl
  refine ⟨Ψ, ?_, ?_, ?_⟩
  · intro s hs y g
    have h1 := transport_apply_cocycle hf s y g hs
    have h2 := hE s hs (y * g)
    have h3 := hE s hs y
    rw [← mul_assoc s y g] at h2
    simp only [hΨ, map_sub, map_add]
    rw [h1, h2, h3]
    simp only [hD]
    abel
  · intro y g h x hy
    simp only [hΨ]
    rw [transport_apply_cocycle hf y g h hy, ← mul_assoc y g h]
    abel
  · intro N hfN hcN y g
    have hDN : ∀ a b : G, D a b ∈ N := fun a b => N.sub_mem (hfN a b) (hcN a)
    rw [hΨ]
    exact N.add_mem (N.sub_mem (hfN y g) (hDN _ _)) (hDN _ _)

/-- **A two-cocycle that is a coboundary over the stabiliser of every index is a coboundary**, and
the trivialising one-cochain can be taken to have its values in an invariant family of subgroups
over any invariant set of indices where the cocycle and the local trivialisations already do. -/
theorem exists_coboundary_mem (hf : F.IsCocycle₂ f) (N : ∀ x, AddSubgroup (M x))
    (hN : ∀ (g : G) (x : X) (a : M x), a ∈ N x → F.map g x a ∈ N (g • x))
    (Good : Set X) (hGood : ∀ (g : G) (x : X), x ∈ Good → g • x ∈ Good)
    (hfN : ∀ (g h : G) (x : X), x ∈ Good → f g h x ∈ N x)
    (hloc : ∀ x₀ : X, ∃ c : G → M x₀,
      (∀ (s t : G) (hs : s • x₀ = x₀), t • x₀ = x₀ →
        f s t x₀ = F.transport hs (c t) - c (s * t) + c s) ∧
      (x₀ ∈ Good → ∀ g : G, c g ∈ N x₀)) :
    ∃ b : G → ∀ x, M x, (∀ g h : G, F.familyAut g (b h) - b (g * h) + b g = f g h) ∧
      ∀ (g : G) (x : X), x ∈ Good → b g x ∈ N x := by
  classical
  have htr : ∀ {g : G} {x y : X} (h : g • x = y) (a : M x), a ∈ N x → F.transport h a ∈ N y := by
    intro g x y h a ha
    subst h
    rw [transport_apply]
    simpa using hN g x a ha
  choose c hc hcN using hloc
  choose Ψ hΨ1 hΨ2 hΨ3 using fun x₀ => exists_equivariantCochain hf x₀ (c x₀) (hc x₀)
  obtain ⟨base, hbmk, hbsmul⟩ : ∃ base : X → X,
      (∀ x, ∃ g : G, g • base x = x) ∧ (∀ (g : G) (x : X), base (g • x) = base x) := by
    refine ⟨fun x => (Quotient.mk (MulAction.orbitRel G X) x).out, ?_, ?_⟩
    · intro x
      obtain ⟨g, hg⟩ := (MulAction.orbitRel_apply (G := G) (α := X)).1
        (Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel G X) x)))
      refine ⟨g⁻¹, ?_⟩
      show g⁻¹ • (Quotient.mk (MulAction.orbitRel G X) x).out = x
      rw [← hg, inv_smul_smul]
    · intro g x
      show (Quotient.mk (MulAction.orbitRel G X) (g • x)).out
        = (Quotient.mk (MulAction.orbitRel G X) x).out
      rw [Quotient.sound ((MulAction.orbitRel_apply (G := G) (α := X)).2
        (MulAction.mem_orbit x g))]
  choose z hz using hbmk
  set b : G → ∀ x, M x := fun g x => F.transport (hz x) (Ψ (base x) (z x)⁻¹ g) with hbdef
  have hbval : ∀ (g : G) (x : X), b g x = F.transport (hz x) (Ψ (base x) (z x)⁻¹ g) :=
    fun _ _ => rfl
  -- the value of the cochain does not depend on the chosen group element
  have hb : ∀ (g : G) (x p : X) (_ : p = base x) (w : G) (hw : w • p = x),
      b g x = F.transport hw (Ψ p w⁻¹ g) := by
    intro g x p hp w hw
    subst hp
    have hwinv : w⁻¹ • x = base x := by rw [inv_smul_eq_iff, hw]
    have hs : (w⁻¹ * z x) • base x = base x := by rw [mul_smul, hz x, hwinv]
    have hkey := hΨ1 (base x) (w⁻¹ * z x) hs (z x)⁻¹ g
    rw [show w⁻¹ * z x * (z x)⁻¹ = w⁻¹ from by group] at hkey
    have h₃ : (w * (w⁻¹ * z x)) • base x = x := by
      rw [show w * (w⁻¹ * z x) = z x from by group]; exact hz x
    rw [hbval, hkey, F.transport_trans hs hw h₃]
    exact (F.transport_congr (show w * (w⁻¹ * z x) = z x from by group) h₃ (hz x) _).symm
  refine ⟨b, ?_, ?_⟩
  · intro g h
    funext x
    have hw : (g⁻¹ * z x) • base x = g⁻¹ • x := by rw [mul_smul, hz x]
    have h₃ : (g * (g⁻¹ * z x)) • base x = x := by
      rw [show g * (g⁻¹ * z x) = z x from by group]; exact hz x
    have h1 : F.familyAut g (b h) x = F.transport (hz x) (Ψ (base x) ((z x)⁻¹ * g) h) := by
      rw [F.familyAut_apply_eq_transport (smul_inv_smul g x) (b h),
        hb h (g⁻¹ • x) (base x) (hbsmul g⁻¹ x).symm (g⁻¹ * z x) hw,
        F.transport_trans hw (smul_inv_smul g x) h₃,
        show (g⁻¹ * z x)⁻¹ = (z x)⁻¹ * g from by group]
      exact F.transport_congr (show g * (g⁻¹ * z x) = z x from by group) h₃ (hz x) _
    have hy : (z x)⁻¹ • x = base x := by rw [inv_smul_eq_iff, hz x]
    have h4 := hΨ2 (base x) (z x)⁻¹ g h hy
    have h₅ : (z x * (z x)⁻¹) • x = x := by simp
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [h1, hbval (g * h) x, hbval g x, ← map_sub, ← map_add, ← h4,
      F.transport_trans hy (hz x) h₅,
      F.transport_congr (mul_inv_cancel (z x)) h₅ (one_smul G x), F.transport_one_self]
  · intro g x hx
    have hy : (z x)⁻¹ • x = base x := by rw [inv_smul_eq_iff, hz x]
    have hbG : base x ∈ Good := by rw [← hy]; exact hGood _ _ hx
    rw [hbval]
    exact htr (hz x) _ (hΨ3 (base x) (N (base x)) (fun a b => hfN a b _ hbG)
      (fun a => hcN (base x) hbG a) _ _)

/-- **A two-cocycle for the action on the sections of a family of modules that is a coboundary over
the stabiliser of every index is a coboundary.** -/
theorem exists_coboundary (hf : F.IsCocycle₂ f)
    (hloc : ∀ x₀ : X, ∃ c : G → M x₀, ∀ (s t : G) (hs : s • x₀ = x₀), t • x₀ = x₀ →
      f s t x₀ = F.transport hs (c t) - c (s * t) + c s) :
    ∃ b : G → ∀ x, M x, ∀ g h : G, F.familyAut g (b h) - b (g * h) + b g = f g h := by
  obtain ⟨b, hb, -⟩ := exists_coboundary_mem hf (fun _ => ⊤) (by simp) ∅ (by simp) (by simp)
    (fun x₀ => (hloc x₀).imp fun c hc => ⟨hc, by simp⟩)
  exact ⟨b, hb⟩

end FamilyAction

end InverseGalois.CFT

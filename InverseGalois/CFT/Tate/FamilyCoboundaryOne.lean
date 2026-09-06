/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Family

/-!
# A section-valued one-cocycle that is locally a coboundary is a coboundary

A group acting on a family of modules indexed by a set with a group action acts on the group of
sections of the family.  A one-cocycle for that action assigns to each group element a section, and
its value at a single index is only acted on by the stabiliser of that index.  This file answers
the same question for one-cocycles that `InverseGalois.CFT.Tate.FamilyCoboundary` answers for
two-cocycles: if, at every index, the restriction of the cocycle to the stabiliser of that index is
a coboundary for the stabiliser, then the cocycle itself is a coboundary.

The construction is completely explicit and shorter than in degree two.  One specialisation of the
cocycle identity expresses the value of the cocycle at an arbitrary index as a difference of two of
its values at a chosen index of the same orbit, transported there by a group element carrying one
index to the other.  Choosing an orbit representative for every index and any group element
carrying it to that index, the local trivialising element at the representative, transported
forward and corrected by the value of the cocycle at the chosen group element, is a section of the
family.  It is well defined — independent of the chosen group element — precisely because of the
local identity applied to the stabiliser element comparing two such choices, and the same local
identity shows that its coboundary is the cocycle.

Nothing is assumed to be finite: neither the group, nor the index set, nor the orbits.

## Main definitions

* `InverseGalois.CFT.FamilyAction.IsCocycle₁`: a one-cocycle for the action on the sections of a
  family of modules.

## Main results

* `InverseGalois.CFT.FamilyAction.transport_apply_cocycle₁`: the value of a one-cocycle at an
  index, transported to another index by a group element carrying the first to the second.
* `InverseGalois.CFT.FamilyAction.exists_coboundary₁`: **a one-cocycle that is a coboundary over
  the stabiliser of every index is a coboundary.**

## Tags

group cohomology, one-cocycle, coboundary, family of modules, sections, stabiliser, idele
-/

namespace InverseGalois.CFT

variable {G X : Type*} [Group G] [MulAction G X]
  {M : X → Type*} [∀ x, AddCommGroup (M x)]

namespace FamilyAction

variable {F : FamilyAction M G}

/-- **A one-cocycle for the action of the group on the sections of a family of modules.** -/
def IsCocycle₁ (F : FamilyAction M G) (f : G → ∀ x, M x) : Prop :=
  ∀ g h : G, f (g * h) = F.familyAut g (f h) + f g

variable {f : G → ∀ x, M x}

/-- **The value of a one-cocycle at an index, transported to another index of the same orbit.**
Transporting by a group element carrying the first index to the second turns the value into a
difference of two values of the cocycle at the second index. -/
theorem transport_apply_cocycle₁ (hf : F.IsCocycle₁ f) (y g : G) {x x₀ : X} (hy : y • x = x₀) :
    F.transport hy (f g x) = f (y * g) x₀ - f y x₀ := by
  have h1 := congrFun (hf y g) (y • x)
  simp only [Pi.add_apply, F.familyAut_apply_smul] at h1
  have h2 := congrArg (famCast M hy) h1
  rw [map_add, famCast_apply_section, famCast_apply_section, ← transport_apply] at h2
  rw [h2]
  abel

/-- **A one-cocycle that is a coboundary over the stabiliser of every index is a coboundary.**
The trivialising section takes, at each index, the local trivialising element at the orbit
representative, transported forward by a group element carrying the representative to the index and
corrected by the value of the cocycle at that group element. -/
theorem exists_coboundary₁ (hf : F.IsCocycle₁ f)
    (hloc : ∀ x₀ : X, ∃ c : M x₀, ∀ (s : G) (hs : s • x₀ = x₀), f s x₀ = F.transport hs c - c) :
    ∃ b : ∀ x, M x, ∀ g : G, F.familyAut g b - b = f g := by
  classical
  choose c hc using hloc
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
  set b : ∀ x, M x := fun x => F.transport (hz x) (c (base x)) - f (z x) x with hbdef
  have hbval : ∀ x : X, b x = F.transport (hz x) (c (base x)) - f (z x) x := fun _ => rfl
  -- the section does not depend on the group element carrying the representative to the index
  have hb : ∀ (x p : X) (_ : p = base x) (w : G) (hw : w • p = x),
      b x = F.transport hw (c p) - f w x := by
    intro x p hp w hw
    subst hp
    have hs : ((z x)⁻¹ * w) • base x = base x := by
      rw [mul_smul, hw, inv_smul_eq_iff, hz x]
    have h₃ : (z x * ((z x)⁻¹ * w)) • base x = x := by
      rw [show z x * ((z x)⁻¹ * w) = w from by group]; exact hw
    have hkey : F.transport hw (c (base x)) - F.transport (hz x) (c (base x))
        = f w x - f (z x) x := by
      have htr := transport_apply_cocycle₁ hf (z x) ((z x)⁻¹ * w) (hz x)
      rw [hc (base x) ((z x)⁻¹ * w) hs, map_sub, F.transport_trans hs (hz x) h₃,
        F.transport_congr (show z x * ((z x)⁻¹ * w) = w from by group) h₃ hw,
        show z x * ((z x)⁻¹ * w) = w from by group] at htr
      exact htr
    have h4 : F.transport hw (c (base x)) - f w x
        = F.transport (hz x) (c (base x)) - f (z x) x := by
      rw [← sub_eq_zero] at hkey ⊢
      rw [← hkey]
      abel
    rw [hbval, h4]
  refine ⟨b, fun g => funext fun x => ?_⟩
  have hy : (g⁻¹ * z x) • base x = g⁻¹ • x := by rw [mul_smul, hz x]
  have h₃ : (g * (g⁻¹ * z x)) • base x = x := by
    rw [show g * (g⁻¹ * z x) = z x from by group]; exact hz x
  have hgx : g • (g⁻¹ • x) = x := smul_inv_smul g x
  have hbg := hb (g⁻¹ • x) (base x) (hbsmul g⁻¹ x).symm (g⁻¹ * z x) hy
  have h1 : F.familyAut g b x = F.transport hgx (b (g⁻¹ • x)) :=
    F.familyAut_apply_eq_transport hgx b
  have h2 := transport_apply_cocycle₁ hf g (g⁻¹ * z x) hgx
  simp only [Pi.sub_apply]
  rw [h1, hbg, map_sub, h2, F.transport_trans hy hgx h₃,
    F.transport_congr (show g * (g⁻¹ * z x) = z x from by group) h₃ (hz x),
    show g * (g⁻¹ * z x) = z x from by group, hbval]
  abel

end FamilyAction

end InverseGalois.CFT

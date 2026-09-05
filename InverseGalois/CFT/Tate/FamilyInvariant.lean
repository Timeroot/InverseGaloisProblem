/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Family

/-!
# An invariant section assembled from germs fixed by the stabilisers

A section of a family of abelian groups indexed by a set with a group action is fixed by the whole
group exactly when its value at every index is carried to its value at the translated index.  To
produce such a section it is enough to have, at one index of every orbit, a value that the
stabiliser of that index leaves alone: transporting it to the other indices of the orbit by any
group element reaching them is unambiguous precisely because two such elements differ by a member of
the stabiliser, and the section so defined is fixed by construction.

The values obtained this way are transports of the chosen ones, so any property of the values that
the transports preserve is inherited by the whole section.  That is what makes the construction
usable: a uniformizer at a place of a number field is only ever fixed by the decomposition group
there, and the statement needed is a family of uniformizers, one at every place, fixed by the whole
Galois group as a family.

## Main results

* `InverseGalois.CFT.FamilyAction.transport_index_eq`: transports of a section along equal indices
  agree.
* `InverseGalois.CFT.FamilyAction.transport_pred`: a property of the values preserved by the
  transports is preserved along a transport between two indices.
* `InverseGalois.CFT.FamilyAction.exists_familyAut_eq_self_of_stabilizerFixed`: **a family whose
  value at each index can be chosen with a property preserved by the transports and fixed by the
  stabiliser of that index has an invariant section all of whose values have the property.**
* `InverseGalois.CFT.FamilyAction.smul_mem_stabFixedSet_iff`: **the indices carrying such a value
  form an invariant set** as soon as the property is preserved by the transports.
* `InverseGalois.CFT.FamilyAction.exists_familyAut_eq_self_stabFixedSet`: **an invariant section
  whose value has the property at every index carrying one**, with no invariance assumption to
  supply.

## Tags

group action, family of modules, sections, orbit, stabiliser, invariant section
-/

namespace InverseGalois.CFT

open MulAction

variable {X : Type*} {M : X → Type*} [∀ x, AddCommGroup (M x)] {G : Type*} [Group G]
  [MulAction G X]

namespace FamilyAction

variable (F : FamilyAction M G)

/-! ### Transports along a trivial or an unnamed change of index -/

/-- The transport by a group element which happens to be recorded as carrying an index to its own
image is the transport isomorphism of the family. -/
theorem transport_rfl (g : G) (x : X) (a : M x) :
    F.transport (rfl : g • x = g • x) a = F.map g x a := rfl

/-- **Transports of a section along equal indices agree.**  The two indices being equal, so are the
two values of the section at them, and the two transports differ only by the proof they carry. -/
theorem transport_index_eq {r r' : X} (e : r' = r) (s : ∀ z, M z) {g : G} {y : X}
    (h : g • r' = y) (h' : g • r = y) : F.transport h (s r') = F.transport h' (s r) := by
  subst e; rfl

/-- **A property of the values preserved by the transports is preserved along a transport between
two indices.** -/
theorem transport_pred {P : ∀ x, M x → Prop}
    (hP : ∀ (g : G) (x : X) (a : M x), P x a → P (g • x) (F.map g x a))
    {g : G} {x y : X} (h : g • x = y) {a : M x} (ha : P x a) : P y (F.transport h a) := by
  subst h
  exact hP g x a ha

/-! ### The invariant section -/

/-- Every index is reached from the chosen index of its orbit. -/
theorem exists_smul_out_eq (x : X) :
    ∃ g : G, g • (Quotient.mk'' x : orbitRel.Quotient G X).out = x := by
  obtain ⟨g, hg⟩ : (Quotient.mk'' x : orbitRel.Quotient G X).out ∈ MulAction.orbit G x :=
    orbitRel.Quotient.mem_orbit.mpr (Quotient.out_eq' (Quotient.mk'' x))
  exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩

/-- The chosen index of an orbit does not change when the index is moved by the group. -/
theorem out_smul_eq (g : G) (x : X) :
    (Quotient.mk'' (g • x) : orbitRel.Quotient G X).out
      = (Quotient.mk'' x : orbitRel.Quotient G X).out := by
  have h : (Quotient.mk'' (g • x) : orbitRel.Quotient G X) = Quotient.mk'' x :=
    @Quotient.sound X (orbitRel G X) _ _ (mem_orbit x g)
  rw [h]

/-- **A family whose value at each index can be chosen with a property preserved by the transports
and fixed by the stabiliser of that index has an invariant section all of whose values have the
property.**  The value at an index is the transport of the chosen value at the chosen index of its
orbit, which does not depend on the group element used because two of them differ by a member of the
stabiliser there. -/
theorem exists_familyAut_eq_self_of_stabilizerFixed (P : ∀ x, M x → Prop)
    (hP : ∀ (g : G) (x : X) (a : M x), P x a → P (g • x) (F.map g x a))
    (h : ∀ x : X, ∃ a : M x, P x a ∧ ∀ (g : G) (hg : g • x = x), F.transport hg a = a) :
    ∃ s : ∀ x, M x, (∀ g : G, F.familyAut g s = s) ∧ ∀ x, P x (s x) := by
  choose a hPa hfix using h
  choose gsel hgsel using exists_smul_out_eq (X := X) (G := G)
  have hany : ∀ (x : X) (g : G) (hg : g • (Quotient.mk'' x : orbitRel.Quotient G X).out = x),
      F.transport hg (a (Quotient.mk'' x : orbitRel.Quotient G X).out)
        = F.transport (hgsel x) (a (Quotient.mk'' x : orbitRel.Quotient G X).out) := by
    intro x g hg
    have hs : ((gsel x)⁻¹ * g) • (Quotient.mk'' x : orbitRel.Quotient G X).out
        = (Quotient.mk'' x : orbitRel.Quotient G X).out := by
      rw [mul_smul, hg]
      exact inv_smul_eq_iff.mpr (hgsel x).symm
    have h3 : (gsel x * ((gsel x)⁻¹ * g)) • (Quotient.mk'' x : orbitRel.Quotient G X).out = x := by
      rw [mul_smul, hs]
      exact hgsel x
    calc F.transport hg (a (Quotient.mk'' x : orbitRel.Quotient G X).out)
        = F.transport h3 (a (Quotient.mk'' x : orbitRel.Quotient G X).out) :=
          (F.transport_congr (by group) h3 hg _).symm
      _ = F.transport (hgsel x) (F.transport hs
            (a (Quotient.mk'' x : orbitRel.Quotient G X).out)) :=
          (F.transport_trans hs (hgsel x) h3 _).symm
      _ = F.transport (hgsel x) (a (Quotient.mk'' x : orbitRel.Quotient G X).out) := by
          rw [hfix _ _ hs]
  refine ⟨fun x => F.transport (hgsel x) (a (Quotient.mk'' x : orbitRel.Quotient G X).out),
    fun g => F.familyAut_eq_of_map g _ _ fun x => ?_,
    fun x => F.transport_pred hP (hgsel x) (hPa _)⟩
  have hcomp : (g * gsel x) • (Quotient.mk'' x : orbitRel.Quotient G X).out = g • x := by
    rw [mul_smul, hgsel x]
  have e : (Quotient.mk'' (g • x) : orbitRel.Quotient G X).out
      = (Quotient.mk'' x : orbitRel.Quotient G X).out := out_smul_eq g x
  have hcomp' : (g * gsel x) • (Quotient.mk'' (g • x) : orbitRel.Quotient G X).out = g • x := by
    rw [e]; exact hcomp
  rw [← F.transport_rfl g x, F.transport_trans (hgsel x) (rfl : g • x = g • x) hcomp,
    ← hany (g • x) (g * gsel x) hcomp', F.transport_index_eq e a hcomp' hcomp]

/-! ### The indices carrying a value fixed by their stabiliser -/

/-- A value fixed by the stabiliser of an index has a transport fixed by the stabiliser of the image
index, because an element fixing the image index is conjugate to one fixing the index. -/
theorem transport_map_eq_self_of_stabilizerFixed {x : X} {a : M x}
    (ha : ∀ (g : G) (hg : g • x = x), F.transport hg a = a) (g h : G)
    (hh : h • (g • x) = g • x) : F.transport hh (F.map g x a) = F.map g x a := by
  have h1 : (g⁻¹ * h * g) • x = x := by rw [mul_smul, mul_smul, hh, inv_smul_smul]
  have h3 : (h * g) • x = g • x := by rw [mul_smul, hh]
  have h3' : (g * (g⁻¹ * h * g)) • x = g • x := by rw [mul_smul, h1]
  calc F.transport hh (F.map g x a)
      = F.transport hh (F.transport (rfl : g • x = g • x) a) := by rw [F.transport_rfl]
    _ = F.transport h3 a := F.transport_trans (rfl : g • x = g • x) hh h3 a
    _ = F.transport h3' a := F.transport_congr (by group) h3 h3' a
    _ = F.transport (rfl : g • x = g • x) (F.transport h1 a) :=
        (F.transport_trans h1 (rfl : g • x = g • x) h3' a).symm
    _ = F.transport (rfl : g • x = g • x) a := by rw [ha _ h1]
    _ = F.map g x a := F.transport_rfl g x a

variable (Q : ∀ x, M x → Prop)

/-- **The indices at which some value with a given property is fixed by the stabiliser.** -/
def stabFixedSet : Set X :=
  {x | ∃ a : M x, Q x a ∧ ∀ (g : G) (hg : g • x = x), F.transport hg a = a}

theorem mem_stabFixedSet {x : X} :
    x ∈ F.stabFixedSet Q ↔
      ∃ a : M x, Q x a ∧ ∀ (g : G) (hg : g • x = x), F.transport hg a = a := Iff.rfl

variable {Q}

/-- The image of an index carrying a value fixed by its stabiliser carries one too. -/
theorem smul_mem_stabFixedSet (hQ : ∀ (g : G) (x : X) (a : M x), Q x a → Q (g • x) (F.map g x a))
    (g : G) {x : X} (hx : x ∈ F.stabFixedSet Q) : g • x ∈ F.stabFixedSet Q := by
  obtain ⟨a, hQa, hfix⟩ := hx
  exact ⟨F.map g x a, hQ g x a hQa,
    fun h hh => F.transport_map_eq_self_of_stabilizerFixed hfix g h hh⟩

/-- **The indices carrying a value with a given property fixed by the stabiliser form an invariant
set** as soon as the property is preserved by the transports. -/
theorem smul_mem_stabFixedSet_iff
    (hQ : ∀ (g : G) (x : X) (a : M x), Q x a → Q (g • x) (F.map g x a)) (g : G) (x : X) :
    g • x ∈ F.stabFixedSet Q ↔ x ∈ F.stabFixedSet Q := by
  refine ⟨fun hx => ?_, fun hx => F.smul_mem_stabFixedSet hQ g hx⟩
  have h := F.smul_mem_stabFixedSet hQ g⁻¹ hx
  rwa [inv_smul_smul] at h

/-- **An invariant section whose value has the given property at every index carrying a value with
that property fixed by the stabiliser.**  Nothing is assumed of the property beyond its being
preserved by the transports: the set of indices where a value is available is invariant of its own
accord, and away from it the section is zero. -/
theorem exists_familyAut_eq_self_stabFixedSet
    (hQ : ∀ (g : G) (x : X) (a : M x), Q x a → Q (g • x) (F.map g x a)) :
    ∃ s : ∀ x, M x, (∀ g : G, F.familyAut g s = s) ∧ ∀ x ∈ F.stabFixedSet Q, Q x (s x) := by
  obtain ⟨s, hs, hPs⟩ := F.exists_familyAut_eq_self_of_stabilizerFixed
    (fun x a => x ∈ F.stabFixedSet Q → Q x a)
    (fun g x a hPa hgx => hQ g x a (hPa ((F.smul_mem_stabFixedSet_iff hQ g x).1 hgx)))
    (fun x => by
      by_cases hx : x ∈ F.stabFixedSet Q
      · obtain ⟨a, hQa, hfix⟩ := hx
        exact ⟨a, fun _ => hQa, hfix⟩
      · exact ⟨0, fun hc => absurd hc hx, fun g hg => _root_.map_zero (F.transport hg)⟩)
  exact ⟨s, hs, fun x hx => hPs x hx⟩

end FamilyAction

end InverseGalois.CFT

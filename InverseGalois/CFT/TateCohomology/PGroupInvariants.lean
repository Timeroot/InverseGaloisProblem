/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Invariant vectors of a p-group in characteristic p

A finite `p`-group acting on a finite set fixes a number of points congruent modulo `p` to the
cardinality of the set.  A representation of a `p`-group on a vector space over the field with `p`
elements therefore has a nonzero invariant vector as soon as it is nonzero: the orbit of a nonzero
vector spans a finite subspace whose cardinality is divisible by `p`, and the origin is already a
fixed point of the action on that subspace, so there must be a second one.

Two consequences are recorded in the shape in which they get used.  A nonzero stable subspace
contains a nonzero invariant vector, and a stable subspace that is not everything is missed by
some vector which is invariant modulo it.  Both of them are also recorded over an arbitrary base,
for a representation all of whose vectors are killed by `p`: such a representation can be read over
the field with `p` elements, and the two conclusions do not mention the scalars.

## Main definitions

* `InverseGalois.CFT.Tate.zmodRep`: a representation whose vectors are killed by `p`, read over the
  field with `p` elements.

## Main results

* `InverseGalois.CFT.Tate.exists_invariant_ne_zero`: **a nonzero representation of a `p`-group over
  the field with `p` elements has a nonzero invariant vector.**
* `InverseGalois.CFT.Tate.exists_invariant_mem_ne_zero`: **a nonzero stable subspace contains a
  nonzero invariant vector.**
* `InverseGalois.CFT.Tate.exists_notMem_invariant_mod`: **a stable subspace that is not everything
  is missed by a vector invariant modulo it.**
* `InverseGalois.CFT.Tate.exists_invariant_mem_ne_zero_of_nsmul`,
  `InverseGalois.CFT.Tate.exists_notMem_invariant_mod_of_nsmul`: the same two statements over an
  arbitrary base, for a representation whose vectors are killed by `p`.

## Tags

p-group, invariant vector, fixed point, characteristic p
-/

namespace InverseGalois.CFT.Tate

open Representation MulAction

noncomputable section

/-! ### The action underlying a representation -/

section Action

variable {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]

/-- **The self-maps of the module underlying a representation.** -/
def repFunctionEnd (ρ : Representation k G V) : G →* Function.End V where
  toFun g := ⇑(ρ g)
  map_one' := by
    funext v
    show ρ 1 v = v
    simp
  map_mul' g h := by
    funext v
    show ρ (g * h) v = ρ g (ρ h v)
    rw [map_mul]
    rfl

/-- **The action of the group on the vectors of a representation.** -/
def repMulAction (ρ : Representation k G V) : MulAction G V :=
  MulAction.ofEndHom (repFunctionEnd ρ)

theorem mem_fixedPoints_repMulAction (ρ : Representation k G V) (v : V) :
    letI := repMulAction ρ
    v ∈ fixedPoints G V ↔ ∀ g : G, ρ g v = v :=
  Iff.rfl

end Action

/-! ### A nonzero invariant vector -/

section PGroup

variable {p : ℕ} [Fact p.Prime] {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod p) V]

/-- **Every vector in characteristic `p` is killed by `p`.** -/
theorem nsmul_prime_eq_zero (v : V) : p • v = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_self, zero_smul]

omit [Finite G] in
/-- **A finite nonzero representation of a `p`-group in characteristic `p` has a nonzero invariant
vector.** -/
theorem exists_invariant_ne_zero_of_finite (hG : IsPGroup p G) [Finite V]
    (ρ : Representation (ZMod p) G V) {a : V} (ha : a ≠ 0) :
    ∃ b : V, b ≠ 0 ∧ ∀ g : G, ρ g b = b := by
  letI := repMulAction ρ
  have hdvd : p ∣ Nat.card V := by
    have h1 : addOrderOf a ∣ p := addOrderOf_dvd_iff_nsmul_eq_zero.2 (nsmul_prime_eq_zero a)
    have h2 : addOrderOf a ≠ 1 := fun h => ha (AddMonoid.addOrderOf_eq_one_iff.1 h)
    have h3 : addOrderOf a = p := ((Fact.out : p.Prime).eq_one_or_self_of_dvd _ h1).resolve_left h2
    exact h3 ▸ addOrderOf_dvd_natCard a
  obtain ⟨b, hb, hne⟩ := hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hdvd
    (a := (0 : V)) (fun g => map_zero (ρ g))
  exact ⟨b, hne.symm, hb⟩

/-- **A nonzero representation of a `p`-group in characteristic `p` has a nonzero invariant
vector.** -/
theorem exists_invariant_ne_zero (hG : IsPGroup p G) (ρ : Representation (ZMod p) G V) {a : V}
    (ha : a ≠ 0) : ∃ b : V, b ≠ 0 ∧ ∀ g : G, ρ g b = b := by
  set U : Submodule (ZMod p) V := Submodule.span (ZMod p) (Set.range fun g : G => ρ g a) with hUdef
  have hU : ∀ g : G, U ≤ U.comap (ρ g) := by
    intro g
    rw [hUdef]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h, rfl⟩
    refine Submodule.mem_comap.2 ?_
    have : ρ g (ρ h a) = ρ (g * h) a := by rw [map_mul]; rfl
    rw [this]
    exact Submodule.subset_span ⟨g * h, rfl⟩
  have haU : a ∈ U := Submodule.subset_span ⟨1, by simp⟩
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  haveI : Module.Finite (ZMod p) U :=
    Module.Finite.iff_fg.2 (Submodule.fg_span (Set.finite_range _))
  haveI : Finite U := Module.finite_of_finite (ZMod p)
  obtain ⟨c, hc0, hcinv⟩ :=
    exists_invariant_ne_zero_of_finite hG (ρ.subrepresentation U hU) (a := ⟨a, haU⟩)
      (by simpa using ha)
  refine ⟨(c : V), fun h => hc0 (Subtype.ext h), fun g => ?_⟩
  simpa using congrArg Subtype.val (hcinv g)

/-- **A nonzero stable subspace contains a nonzero invariant vector.** -/
theorem exists_invariant_mem_ne_zero (hG : IsPGroup p G) (ρ : Representation (ZMod p) G V)
    {U : Submodule (ZMod p) V} (hU : ∀ g : G, U ≤ U.comap (ρ g)) {a : V} (haU : a ∈ U)
    (ha : a ≠ 0) : ∃ b : V, b ∈ U ∧ b ≠ 0 ∧ ∀ g : G, ρ g b = b := by
  obtain ⟨c, hc0, hcinv⟩ :=
    exists_invariant_ne_zero hG (ρ.subrepresentation U hU) (a := ⟨a, haU⟩) (by simpa using ha)
  refine ⟨(c : V), c.2, fun h => hc0 (Subtype.ext h), fun g => ?_⟩
  simpa using congrArg Subtype.val (hcinv g)

/-- **A stable subspace that is not everything is missed by a vector invariant modulo it.** -/
theorem exists_notMem_invariant_mod (hG : IsPGroup p G) (ρ : Representation (ZMod p) G V)
    {U : Submodule (ZMod p) V} (hU : ∀ g : G, U ≤ U.comap (ρ g)) {a : V} (ha : a ∉ U) :
    ∃ b : V, b ∉ U ∧ ∀ g : G, ρ g b - b ∈ U := by
  obtain ⟨c, hc0, hcinv⟩ :=
    exists_invariant_ne_zero hG (ρ.quotient U hU) (a := U.mkQ a)
      (fun h => ha ((Submodule.Quotient.mk_eq_zero U).1 h))
  obtain ⟨b, rfl⟩ := U.mkQ_surjective c
  refine ⟨b, fun h => hc0 ((Submodule.Quotient.mk_eq_zero U).2 h), fun g => ?_⟩
  have h1 : U.mkQ (ρ g b) = U.mkQ b := by simpa using hcinv g
  have h2 : U.mkQ (ρ g b - b) = 0 := by rw [map_sub, h1, sub_self]
  rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h2

end PGroup

/-! ### Other bases -/

section Base

variable {p : ℕ} {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]

/-- **A representation read over the field with `p` elements**, when the vectors are killed by
`p`. -/
def zmodRep (p : ℕ) [Module (ZMod p) V] (ρ : Representation k G V) :
    Representation (ZMod p) G V where
  toFun g := ((ρ g).toAddMonoidHom).toZModLinearMap p
  map_one' := by
    ext v
    show ρ 1 v = v
    simp
  map_mul' g h := by
    ext v
    show ρ (g * h) v = ρ g (ρ h v)
    rw [map_mul]
    rfl

@[simp]
theorem zmodRep_apply [Module (ZMod p) V] (ρ : Representation k G V) (g : G) (v : V) :
    zmodRep p ρ g v = ρ g v := rfl

variable [Fact p.Prime] [Finite G]

/-- **A nonzero stable subspace contains a nonzero invariant vector**, over any base over which the
vectors are killed by `p`. -/
theorem exists_invariant_mem_ne_zero_of_nsmul (hG : IsPGroup p G) (ρ : Representation k G V)
    (hp : ∀ v : V, p • v = 0) {U : Submodule k V} (hU : ∀ g : G, U ≤ U.comap (ρ g)) {a : V}
    (haU : a ∈ U) (ha : a ≠ 0) : ∃ b : V, b ∈ U ∧ b ≠ 0 ∧ ∀ g : G, ρ g b = b := by
  letI := AddCommGroup.zmodModule (n := p) hp
  exact exists_invariant_mem_ne_zero hG (zmodRep p ρ)
    (U := AddSubgroup.toZModSubmodule p U.toAddSubgroup) (fun g _ hx => hU g hx) haU ha

/-- **A stable subspace that is not everything is missed by a vector invariant modulo it**, over any
base over which the vectors are killed by `p`. -/
theorem exists_notMem_invariant_mod_of_nsmul (hG : IsPGroup p G) (ρ : Representation k G V)
    (hp : ∀ v : V, p • v = 0) {U : Submodule k V} (hU : ∀ g : G, U ≤ U.comap (ρ g)) {a : V}
    (ha : a ∉ U) : ∃ b : V, b ∉ U ∧ ∀ g : G, ρ g b - b ∈ U := by
  letI := AddCommGroup.zmodModule (n := p) hp
  exact exists_notMem_invariant_mod hG (zmodRep p ρ)
    (U := AddSubgroup.toZModSubmodule p U.toAddSubgroup) (fun g _ hx => hU g hx) ha

end Base

end

end InverseGalois.CFT.Tate

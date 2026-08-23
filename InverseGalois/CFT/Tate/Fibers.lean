/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.CyclicAction

/-!
# The lattice of a set fibred over its orbits

A permutation of a finite set whose orbits are the fibres of a map to an index set presents that
set as a disjoint union of cyclically shifted blocks, one for each index: the block at an index is
the orbit of a chosen point of the fibre there, and it is a cyclic model of that fibre.  The
Herbrand quotient of the free lattice on the whole set is then the product over the indices of the
contribution of one block.

For a finite cyclic group this is the general form of the computation: the group acts on a finite
set, the orbits are the fibres of the map to the set of orbits, and the contribution of an orbit is
the order of the stabiliser of a point of it.  The set of infinite places of a Galois extension is
fibred in exactly this way over the infinite places of the base field, and the set of primes above
a finite set of primes likewise.

## Main definitions

* `InverseGalois.CFT.fiberPoint`: the point of the block at an index at a given place.
* `InverseGalois.CFT.fiberEquiv`: the block presentation of a set fibred over its orbits.

## Main results

* `InverseGalois.CFT.apply_orbitPoint`: the permutation advances the place by one.
* `InverseGalois.CFT.herbrand_permLatticeAut_of_fibers`: the Herbrand quotient of the free lattice
  on a set fibred over its orbits is the product of the contributions of the blocks.
* `InverseGalois.CFT.period_eq_card_orbit`: the period of a generator at a point is the number of
  points of its orbit.
* `InverseGalois.CFT.herbrand_permLatticeAut_toPerm_of_fibers`: **the Herbrand quotient of the free
  lattice on a finite set acted on by a finite cyclic group is the product over the orbits of the
  order of the stabiliser of a point.**
* `InverseGalois.CFT.herbrand_permLatticeAut_toPerm_orbits`: the same computation indexed by the
  quotient of the set by the orbit relation.

## Tags

Tate cohomology, Herbrand quotient, orbit, stabiliser, permutation module
-/

namespace InverseGalois.CFT

open MulAction

variable {X I : Type*} [Fintype X] {p : Equiv.Perm X}

/-! ### The blocks of an invariant fibring -/

variable (p)

/-- **The permutation advances the place of a point of an orbit by one.** -/
theorem apply_orbitPoint (x₀ : X) (j : ZMod (period p x₀)) :
    p (orbitPoint p x₀ j) = orbitPoint p x₀ (j + 1) := by
  have h : ((j.val + 1 : ℕ) : ZMod (period p x₀)) = (((j + 1).val : ℕ) : ZMod (period p x₀)) := by
    rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_rightInverse j,
      ZMod.natCast_rightInverse (j + 1)]
  rw [orbitPoint_apply, orbitPoint_apply, ← Equiv.Perm.mul_apply, ← pow_succ']
  exact pow_apply_congr p x₀ h

omit [Fintype X] in
/-- A map constant along the permutation is constant along all of its powers. -/
theorem apply_pow_of_invariant {f : X → I} (hf : ∀ x, f (p x) = f x) (k : ℕ) (x : X) :
    f ((p ^ k) x) = f x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [pow_succ, Equiv.Perm.mul_apply, ih, hf]

/-- **The point of the block at an index at a given place.** -/
noncomputable def fiberPoint (x₀ : I → X) (s : Σ i : I, ZMod (period p (x₀ i))) : X :=
  orbitPoint p (x₀ s.1) s.2

omit [Fintype X] in
theorem fiberPoint_apply (x₀ : I → X) (i : I) (j : ZMod (period p (x₀ i))) :
    fiberPoint p x₀ ⟨i, j⟩ = (p ^ j.val) (x₀ i) := rfl

variable {p}

omit [Fintype X] in
/-- The map to the index set recovers the index of a block. -/
theorem apply_fiberPoint {f : X → I} {x₀ : I → X} (hf : ∀ x, f (p x) = f x)
    (hx₀ : ∀ i, f (x₀ i) = i) (i : I) (j : ZMod (period p (x₀ i))) :
    f (fiberPoint p x₀ ⟨i, j⟩) = i := by
  rw [fiberPoint_apply, apply_pow_of_invariant p hf, hx₀]

theorem fiberPoint_injective {f : X → I} {x₀ : I → X} (hf : ∀ x, f (p x) = f x)
    (hx₀ : ∀ i, f (x₀ i) = i) : Function.Injective (fiberPoint p x₀) := by
  rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h
  have hi : i₁ = i₂ := by
    rw [← apply_fiberPoint hf hx₀ i₁ j₁, ← apply_fiberPoint hf hx₀ i₂ j₂, h]
  subst hi
  exact congrArg (Sigma.mk i₁) (orbitPoint_injective p (x₀ i₁) h)

theorem fiberPoint_surjective {f : X → I} {x₀ : I → X}
    (htrans : ∀ y : X, ∃ k : ℕ, (p ^ k) (x₀ (f y)) = y) :
    Function.Surjective (fiberPoint p x₀) := by
  intro y
  obtain ⟨k, hk⟩ := htrans y
  refine ⟨⟨f y, (k : ZMod (period p (x₀ (f y))))⟩, ?_⟩
  exact (pow_apply_congr p (x₀ (f y))
    (ZMod.natCast_rightInverse (k : ZMod (period p (x₀ (f y)))))).trans hk

/-- **The block presentation of a set fibred over its orbits.** -/
noncomputable def fiberEquiv {f : X → I} {x₀ : I → X} (hf : ∀ x, f (p x) = f x)
    (hx₀ : ∀ i, f (x₀ i) = i) (htrans : ∀ y : X, ∃ k : ℕ, (p ^ k) (x₀ (f y)) = y) :
    (Σ i : I, ZMod (period p (x₀ i))) ≃ X :=
  Equiv.ofBijective _ ⟨fiberPoint_injective hf hx₀, fiberPoint_surjective htrans⟩

theorem fiberEquiv_apply {f : X → I} {x₀ : I → X} (hf : ∀ x, f (p x) = f x)
    (hx₀ : ∀ i, f (x₀ i) = i) (htrans : ∀ y : X, ∃ k : ℕ, (p ^ k) (x₀ (f y)) = y)
    (s : Σ i : I, ZMod (period p (x₀ i))) : fiberEquiv hf hx₀ htrans s = fiberPoint p x₀ s := rfl

/-! ### The Herbrand quotient -/

/-- **The Herbrand quotient of the free lattice on a set fibred over its orbits** is the product
over the indices of the contribution of one block. -/
theorem herbrand_permLatticeAut_of_fibers [Fintype I] {f : X → I} {x₀ : I → X} {m : I → ℕ} {n : ℕ}
    (hf : ∀ x, f (p x) = f x) (hx₀ : ∀ i, f (x₀ i) = i)
    (htrans : ∀ y : X, ∃ k : ℕ, (p ^ k) (x₀ (f y)) = y)
    (hnm : ∀ i, period p (x₀ i) * m i = n) (hm : ∀ i, m i ≠ 0) :
    herbrand (permLatticeAut p) n = ∏ i, (m i : ℚ) :=
  herbrand_permLatticeAut hnm hm (fiberEquiv hf hx₀ htrans) fun i j => apply_orbitPoint p (x₀ i) j

/-! ### The orbits of a finite cyclic group -/

variable {G : Type*} [Group G] [MulAction G X]

omit [Fintype X] in
/-- **The orbit–stabiliser theorem** for a point of an arbitrary action. -/
theorem card_orbit_mul_card_stabilizer (x : X) :
    Nat.card (orbit G x) * Nat.card (stabilizer G x) = Nat.card G := by
  have h : Nat.card (orbit G x) = (stabilizer G x).index :=
    Nat.card_congr (orbitEquivQuotientStabilizer G x)
  rw [h, Subgroup.index_mul_card]

variable {σ : G}

/-- The places of the orbit of a point under a generator of the group. -/
noncomputable def orbitPointEquiv [Finite G] (hσ : ∀ g : G, g ∈ Subgroup.zpowers σ) (x : X) :
    ZMod (period (toPerm σ : Equiv.Perm X) x) ≃ orbit G x := by
  refine Equiv.ofBijective
    (fun j => ⟨orbitPoint (toPerm σ : Equiv.Perm X) x j, ?_⟩) ⟨?_, ?_⟩
  · rw [orbitPoint_apply, pow_toPerm_apply]
    exact mem_orbit x _
  · exact fun a b hab => orbitPoint_injective _ x (Subtype.ext_iff.mp hab)
  · rintro ⟨y, g, rfl⟩
    obtain ⟨k, hk⟩ := mem_powers_iff_mem_zpowers.2 (hσ g)
    have hk' : σ ^ k = g := hk
    refine ⟨(k : ZMod (period (toPerm σ : Equiv.Perm X) x)), Subtype.ext ?_⟩
    show orbitPoint (toPerm σ : Equiv.Perm X) x
      (k : ZMod (period (toPerm σ : Equiv.Perm X) x)) = g • x
    rw [orbitPoint_apply, pow_apply_congr (toPerm σ : Equiv.Perm X) x
      (ZMod.natCast_rightInverse (k : ZMod (period (toPerm σ : Equiv.Perm X) x))),
      pow_toPerm_apply, hk']

/-- **The period of a generator at a point is the number of points of its orbit.** -/
theorem period_eq_card_orbit [Finite G] (hσ : ∀ g : G, g ∈ Subgroup.zpowers σ) (x : X) :
    period (toPerm σ : Equiv.Perm X) x = Nat.card (orbit G x) := by
  rw [← Nat.card_congr (orbitPointEquiv hσ x), Nat.card_zmod]

/-- **The Herbrand quotient of the free lattice on a finite set acted on by a finite cyclic group**
is the product over the orbits of the order of the stabiliser of a point.  The orbits are presented
as the fibres of an invariant map together with a point in each of them. -/
theorem herbrand_permLatticeAut_toPerm_of_fibers [Finite G] [Fintype I] {f : X → I} {x₀ : I → X}
    (hf : ∀ (g : G) (x : X), f (g • x) = f x) (hx₀ : ∀ i, f (x₀ i) = i)
    (htrans : ∀ y : X, ∃ g : G, g • x₀ (f y) = y) (hσ : ∀ g : G, g ∈ Subgroup.zpowers σ) {n : ℕ}
    (hn : Nat.card G = n) :
    herbrand (permLatticeAut (toPerm σ : Equiv.Perm X)) n
      = ∏ i, (Nat.card (stabilizer G (x₀ i)) : ℚ) := by
  refine herbrand_permLatticeAut_of_fibers (fun x => hf σ x) hx₀ (fun y => ?_) (fun i => ?_)
    fun i => Nat.card_pos.ne'
  · obtain ⟨g, hg⟩ := htrans y
    obtain ⟨k, hk⟩ := mem_powers_iff_mem_zpowers.2 (hσ g)
    have hk' : σ ^ k = g := hk
    exact ⟨k, by rw [pow_toPerm_apply, hk', hg]⟩
  · rw [period_eq_card_orbit hσ, card_orbit_mul_card_stabilizer, hn]

/-- **The Herbrand quotient of the free lattice on a finite set acted on by a finite cyclic group**
is the product over the set of orbits of the order of the stabiliser of a chosen point of each.
This is the previous computation with the canonical choice of index set, the quotient by the orbit
relation. -/
theorem herbrand_permLatticeAut_toPerm_orbits [Finite G] [Fintype (orbitRel.Quotient G X)]
    (hσ : ∀ g : G, g ∈ Subgroup.zpowers σ) {n : ℕ} (hn : Nat.card G = n) :
    herbrand (permLatticeAut (toPerm σ : Equiv.Perm X)) n
      = ∏ o : orbitRel.Quotient G X, (Nat.card (stabilizer G o.out) : ℚ) := by
  refine herbrand_permLatticeAut_toPerm_of_fibers (f := Quotient.mk'') (x₀ := Quotient.out)
    (fun g x => Quotient.sound' (mem_orbit x g)) (fun i => i.out_eq') (fun y => ?_) hσ hn
  have hy : y ∈ orbitRel.Quotient.orbit (Quotient.mk'' y : orbitRel.Quotient G X) :=
    orbitRel.Quotient.mem_orbit.mpr rfl
  rw [orbitRel.Quotient.orbit_eq_orbit_out _ Quotient.out_eq'] at hy
  exact hy

end InverseGalois.CFT

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.Congr
import InverseGalois.CFT.Tate.Permutation

/-!
# The lattice of a permuted basis

A permutation of a set acts on the free abelian group on that set by permuting the basis, and the
Herbrand quotient of that action is computed by the model of a permutation lattice: once the set is
presented as a disjoint union of cyclically shifted blocks, the two are isomorphic by an
equivariant map, and an equivariant isomorphism does not change the Herbrand quotient.

The presentation of the set is left as a hypothesis here, since in practice it is exactly what the
situation provides: for the places of a Galois extension lying over the places of the base field,
the blocks are the places over a fixed place of the base, and the length of a block is the index of
the decomposition group.

## Main definitions

* `InverseGalois.CFT.permLatticeAut`: the action of a permutation on the free lattice it generates.
* `InverseGalois.CFT.permLatticeEquiv`: the comparison with the model of a permutation lattice.

## Main results

* `InverseGalois.CFT.permLatticeAut_pow_eq_one`: the action inherits the order of the permutation.
* `InverseGalois.CFT.herbrand_permLatticeAut`: **the Herbrand quotient of a permuted basis is the
  product over the blocks of the order of the stabiliser.**

## Tags

Tate cohomology, Herbrand quotient, permutation module
-/

namespace InverseGalois.CFT

variable {X : Type*} {n : ℕ}

/-! ### The action on the free lattice -/

/-- **The action of a permutation on the free lattice it generates**, by permuting the basis. -/
def permLatticeAut (p : Equiv.Perm X) : (X → ℤ) ≃+ (X → ℤ) where
  toFun f := f ∘ p
  invFun f := f ∘ p.symm
  left_inv f := funext fun x => congrArg f (p.apply_symm_apply x)
  right_inv f := funext fun x => congrArg f (p.symm_apply_apply x)
  map_add' _ _ := rfl

@[simp]
theorem permLatticeAut_apply (p : Equiv.Perm X) (f : X → ℤ) (x : X) :
    permLatticeAut p f x = f (p x) := rfl

/-- Powers of the action are the actions of the powers. -/
theorem pow_permLatticeAut_apply (p : Equiv.Perm X) (k : ℕ) (f : X → ℤ) (x : X) :
    ((permLatticeAut p) ^ k) f x = f ((p ^ k) x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ_apply, permLatticeAut_apply, ih, pow_succ, Equiv.Perm.mul_apply]

/-- **The action inherits the order of the permutation.** -/
theorem permLatticeAut_pow_eq_one {p : Equiv.Perm X} (hp : p ^ n = 1) :
    (permLatticeAut p) ^ n = 1 := by
  refine AddEquiv.ext fun f => funext fun x => ?_
  show ((permLatticeAut p) ^ n) f x = f x
  rw [pow_permLatticeAut_apply, hp]
  rfl

/-! ### The comparison with the model -/

variable {ι : Type*} {d : ι → ℕ}

/-- **The comparison with the model of a permutation lattice** attached to a presentation of the
basis as a disjoint union of blocks. -/
def permLatticeEquiv (φ : (Σ i, ZMod (d i)) ≃ X) : (X → ℤ) ≃+ (∀ i, ZMod (d i) → ℤ) where
  toFun f i j := f (φ ⟨i, j⟩)
  invFun g x := g (φ.symm x).1 (φ.symm x).2
  left_inv f := funext fun x => congrArg f (φ.apply_symm_apply x)
  right_inv g := funext fun i => funext fun j =>
    congrArg (fun s : Σ i, ZMod (d i) => g s.1 s.2) (φ.symm_apply_apply ⟨i, j⟩)
  map_add' _ _ := rfl

@[simp]
theorem permLatticeEquiv_apply (φ : (Σ i, ZMod (d i)) ≃ X) (f : X → ℤ) (i : ι) (j : ZMod (d i)) :
    permLatticeEquiv φ f i j = f (φ ⟨i, j⟩) := rfl

/-- A presentation of the basis by cyclically shifted blocks makes the comparison equivariant. -/
theorem permLatticeEquiv_equivariant {p : Equiv.Perm X} (φ : (Σ i, ZMod (d i)) ≃ X)
    (hφ : ∀ (i : ι) (j : ZMod (d i)), p (φ ⟨i, j⟩) = φ ⟨i, j + 1⟩) (f : X → ℤ) :
    permLatticeEquiv φ (permLatticeAut p f) = permAut d (permLatticeEquiv φ f) := by
  refine funext fun i => funext fun j => ?_
  rw [permAut_apply, permLatticeEquiv_apply, permLatticeEquiv_apply, permLatticeAut_apply]
  exact congrArg f (hφ i j)

/-! ### The Herbrand quotient -/

/-- **The Herbrand quotient of a permuted basis is the product over the blocks of the order of the
stabiliser.**  A block of length `d` inside a cyclic group of order `n = d * m` has a stabiliser of
order `m`, and it contributes exactly that factor. -/
theorem herbrand_permLatticeAut [Fintype ι] [∀ i, NeZero (d i)] {m : ι → ℕ}
    (hn : ∀ i, d i * m i = n) (hm : ∀ i, m i ≠ 0) {p : Equiv.Perm X}
    (φ : (Σ i, ZMod (d i)) ≃ X)
    (hφ : ∀ (i : ι) (j : ZMod (d i)), p (φ ⟨i, j⟩) = φ ⟨i, j + 1⟩) :
    herbrand (permLatticeAut p) n = ∏ i, (m i : ℚ) := by
  rw [herbrand_congr (permLatticeEquiv φ) (permLatticeEquiv_equivariant φ hφ) n,
    herbrand_permAut hn hm]

end InverseGalois.CFT

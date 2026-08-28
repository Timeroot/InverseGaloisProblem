/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Scholz.StrongScholz

/-!
# Raising the class of a strong Scholz realization

A solution of the rung of the tower of free objects over a strong Scholz realization is again a
strong Scholz realization, with the very same blocks: the square roots of the field below are
square roots of the field above, and the distinguished generators of the free object of the higher
class project onto the distinguished generators of the one below, so they move those square roots
in exactly the same pattern.

This is the last step of a turn of the dyadic Scholz–Reichardt induction.  Everything before it —
solving the rung, shrinking, correcting the residues — produces a field satisfying Serre's
condition with the right Galois group over the realization one class down; this reads that field as
a realization in its own right.

## Main definitions

* `InverseGalois.CFT.StrongScholzRealization.stepUp`: **a Scholz solution of the rung over a strong
  Scholz realization is a strong Scholz realization of the next class.**

## Tags

Scholz–Reichardt, strong Scholz field, block, free `2`-group, `2`-class
-/

open NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

namespace StrongScholzRealization

/-- **A Scholz solution of the rung over a strong Scholz realization is a strong Scholz realization
of the next class**, with the same blocks.  A square root of the field below is one of the field
above, and it is moved by the same sign, because the distinguished generator of the higher class
restricts to the distinguished generator of the lower one. -/
noncomputable def stepUp {d c M N : ℕ} (S : StrongScholzRealization d c M)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (hSF : S.carrier ≤ F) (hsch : IsScholz 2 N ↥F) (eF : Gal(↥F/ℚ) ≃* FreePClass 2 d (c + 1))
    (hcomp : ∀ τ, FreePClass.proj 2 d c (eF τ) = S.galEquiv (galRestrictLE hSF τ)) :
    StrongScholzRealization d (c + 1) N where
  carrier := F
  isScholz := hsch
  block := S.block
  blockPrime := S.blockPrime
  blockDisjoint := S.blockDisjoint
  galEquiv := eF
  sqrt := fun i => IntermediateField.inclusion hSF (S.sqrt i)
  sqrt_sq := fun i => by rw [← map_pow, S.sqrt_sq i, AlgHom.commutes]
  sqrtSign_gen := fun k i => by
    have h : galRestrictLE hSF (eF.symm (FreePClass.gen 2 d (c + 1) k))
        = S.galEquiv.symm (FreePClass.gen 2 d c k) := by
      rw [MulEquiv.eq_symm_apply, ← hcomp, MulEquiv.apply_symm_apply, FreePClass.proj_gen]
    rw [sqrtSign_inclusion hSF, h]
    exact S.sqrtSign_gen k i

@[simp] theorem stepUp_carrier {d c M N : ℕ} (S : StrongScholzRealization d c M)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (hSF : S.carrier ≤ F) (hsch : IsScholz 2 N ↥F) (eF : Gal(↥F/ℚ) ≃* FreePClass 2 d (c + 1))
    (hcomp : ∀ τ, FreePClass.proj 2 d c (eF τ) = S.galEquiv (galRestrictLE hSF τ)) :
    (S.stepUp F hSF hsch eF hcomp).carrier = F := rfl

@[simp] theorem stepUp_block {d c M N : ℕ} (S : StrongScholzRealization d c M)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (hSF : S.carrier ≤ F) (hsch : IsScholz 2 N ↥F) (eF : Gal(↥F/ℚ) ≃* FreePClass 2 d (c + 1))
    (hcomp : ∀ τ, FreePClass.proj 2 d c (eF τ) = S.galEquiv (galRestrictLE hSF τ)) :
    (S.stepUp F hSF hsch eF hcomp).block = S.block := rfl

end StrongScholzRealization

end InverseGalois.CFT

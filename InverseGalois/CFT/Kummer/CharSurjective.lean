/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.EmbeddingObstruction
import InverseGalois.CFT.Profinite.Kummer
import InverseGalois.CFT.Profinite.SymbolCyclic
import InverseGalois.CFT.Profinite.Trivial

/-!
# Every character of the whole Galois group is a Kummer character

The roots of unity being in the base field, a smooth character of the absolute Galois group with
values in the residues modulo their order is a one cocycle for the trivial action, so Hilbert's
theorem ninety produces an element of the extension whose coboundary it is; the power of that
element by the order is fixed, hence a unit of the base, and the character is by uniqueness the
Kummer character of that unit.

This is the surjectivity of the Kummer homomorphism, read on characters rather than on cohomology
classes.  A prescription made character by character can therefore always be met by units of the
base field, which is what the reciprocity residue needs in order to be defined on all of the dual
of a layer and not merely on a subspace of it.

## Main results

* `InverseGalois.CFT.exists_units_forall_kummerChar_eq` — **every smooth character of the Galois
  group is the Kummer character of a unit of the base field.**

## Tags

Kummer theory, Hilbert's theorem 90, character, root of unity, surjectivity
-/

namespace InverseGalois.CFT

open groupCohomology

section CharSurjective

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω] {n : ℕ} [NeZero n]
  {ζ : k} {hζ : IsPrimitiveRoot ζ n}

attribute [local instance] zmodTrivialAction

variable (h : IsKummerData k Ω (Multiplicative (ZMod n)) (zmodRootHom hζ) n)

/-- **Every smooth character of the Galois group is the Kummer character of a unit of the base
field.**

Read in the units of the extension the character is a smooth one cocycle, the action on the roots
of unity of the base being trivial, so Hilbert's theorem ninety for the whole group presents it as
the coboundary of an element whose power by the order comes from the base field.  The Kummer
cochain of that unit is the only cochain with this coboundary, so it is the character itself. -/
theorem exists_units_forall_kummerChar_eq (χ : Gal(Ω/k) → ZMod n)
    (hχ : ∀ x y : Gal(Ω/k), χ (x * y) = χ x + χ y)
    (hsm : ∃ N : Subgroup Gal(Ω/k), IsOpen (N : Set Gal(Ω/k)) ∧ ∀ x ∈ N, χ x = 0) :
    ∃ a : kˣ, ∀ g : Gal(Ω/k), kummerChar h a g = χ g := by
  have hmul : ∀ x y : Gal(Ω/k), Multiplicative.ofAdd (χ (x * y))
      = Multiplicative.ofAdd (χ x) * Multiplicative.ofAdd (χ y) := fun x y => by
    rw [hχ, ofAdd_add]
  set χ' : Gal(Ω/k) →* Multiplicative (ZMod n) :=
    MonoidHom.mk' (fun x => Multiplicative.ofAdd (χ x)) hmul with hχ'def
  have hker : IsOpenNormal χ'.ker := by
    obtain ⟨N, hNopen, hN⟩ := hsm
    refine ⟨χ'.normal_ker, Subgroup.isOpen_mono (H₁ := N) (fun x hx => ?_) hNopen⟩
    rw [MonoidHom.mem_ker]
    show Multiplicative.ofAdd (χ x) = 1
    rw [hN x hx]
    rfl
  obtain ⟨a, β, hβ, hcβ⟩ := exists_pow_eq_of_isMulCocycle₁ h.smul_eq h.pow_eq_one
    (isMulCocycle₁_of_hom h.smul_eq χ') (isSmooth₁_of_isOpenNormal_ker hker)
  refine ⟨a, fun g => ?_⟩
  have hg := congrFun (h.cochain_unique a hβ hcβ) g
  rw [kummerChar_apply, ← hg]
  rfl

end CharSurjective

end InverseGalois.CFT

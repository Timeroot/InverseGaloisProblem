/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.LevelShrink

/-!
# The everywhere locally trivial classes covered by the homology of the level

What one rung of the ladder consumes is that an everywhere locally trivial class of the layer die
under a shrinking whose rank is fixed before the class is known.  Inflation from the operator group
is one way of arranging that, but it is not what the global duality of a number field says.  What
duality says is that the everywhere locally trivial classes of the second cohomology are the
characters of the everywhere locally trivial classes of the first cohomology of the Cartier dual;
those inject into the first cohomology of a finite level, and the characters of the first cohomology
of a finite group are its first homology, which is complete cohomology in degree minus two.  So the
classes the rung has to kill are covered by the first homology of the level with coefficients in the
layer twisted by a fixed module.

That covering is what is asked for here, and only that.  It is asked in the form the rung uses it:
a class of the first homology upstairs is produced for each locally trivial class, and a shrinking
which kills the homology class is required to kill the cohomology class with it.  The compatibility
is the naturality of the duality pairing in the coefficients, and it is the whole of what the
condition adds to the bare existence of a cover.

Granted the covering, the rung follows from the count alone: the first homology of a generic
semidirect product with coefficients in a twisted layer is annihilated by a surjective equivariant
homomorphism onto the intended rank, and the rank to start from depends only on the operator group,
the intended rank, the layer and the twist, so it is fixed before any class is named.

## Main definitions

* `InverseGalois.Shafarevich.HasShaTateCover` — **every everywhere locally trivial class of the
  layer comes from a first homology class of the level, compatibly with shrinking.**

## Main results

* `InverseGalois.Shafarevich.hasShrinkableSha_of_hasShaTateCover` — **a covered class is a
  shrinkable class**, and hence the whole rung follows from the covering.

## Tags

Shafarevich's theorem, embedding problem, Poitou-Tate, global duality, group homology, p-central
series
-/

namespace InverseGalois.Shafarevich

open CategoryTheory InverseGalois.CFT

/-! ### The covering the duality supplies -/

/-- **Every everywhere locally trivial class of the second cohomology with coefficients in a layer
comes from a first homology class of the level, compatibly with shrinking.**

The homology is that of the semidirect product of the generic operator group with the operator
group, with coefficients in the layer tensored with a fixed module; over a number field the fixed
module is the twist by the roots of unity, and the covering is global duality read against the
level: the locally trivial classes of the second cohomology are characters of the locally trivial
classes of the first cohomology of the Cartier dual, those inject into the first cohomology of the
level, and the characters of the first cohomology of a finite group are its first homology.

The compatibility asked for is the naturality of that reading in the coefficients: a shrinking which
kills the homology class kills the cohomology class it covers. -/
def HasShaTateCover (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U] [Finite U] [TopologicalSpace U]
    (N : ℕ) (S : Type) [Group S] [Finite S] (j : ℕ) {k Ω : Type*} [Field k] [Field Ω]
    [Algebra k Ω] (φ : Gal(Ω/k) →* U) (T : Set (Subgroup Gal(Ω/k))) (W : Rep (ZMod ℓ) U) : Prop :=
  letI := galLayerAction ℓ U N S j φ
  ∀ ε ∈ sha2 ↥(layerSub ℓ (Generic U N S) j) T,
    ∃ x : groupHomology.H1 (genericInflate U N S ℓ j W),
      ∀ (n : ℕ) (α : Generic U N S →* Generic U n S) (hα : IsOperatorHom α),
        groupHomology.map (operatorSemidirect hα) (operatorInflateRep hα ℓ j W) 1 x = 0 →
          letI := galLayerAction ℓ U n S j φ
          coeffH2 (layerSubMap ℓ α j)
            (layerSubMap_smul_comm φ (fun _ _ => rfl) (fun _ _ => rfl) hα) ε = 1

/-! ### A covered class is a shrinkable class -/

/-- **A covered class is a shrinkable class.**

The number of letters to start from is settled by the count on first homology, which asks only for
the operator group, the intended number of letters, the layer and the twist; so it is fixed before
any solution, and hence any class, is chosen.  At that number of letters the covering turns the
locally trivial class into a single homology class, the count kills that class by a surjective
equivariant homomorphism onto the intended number of letters, and the compatibility carries the
killing back to the class one started with. -/
theorem hasShrinkableSha_of_hasShaTateCover (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U] [Finite U]
    [TopologicalSpace U] (n : ℕ) (S : Type) [Group S] [Finite S] (hS : IsPGroup ℓ S) (j : ℕ)
    {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] (φ : Gal(Ω/k) →* U)
    (T : Set (Subgroup Gal(Ω/k))) (W : Rep (ZMod ℓ) U) [Module.Finite (ZMod ℓ) W]
    (hcov : ∀ N : ℕ, HasShaTateCover ℓ U N S j φ T W) :
    HasShrinkableSha ℓ U n S j φ T := by
  obtain ⟨N, hN⟩ := exists_operatorHom_h1_eq_zero U n S hS (j := j) (t := 1) W
  refine ⟨N, fun ε hε => ?_⟩
  obtain ⟨x, hx⟩ := hcov N ε hε
  obtain ⟨α, hα, hsurj, hkill⟩ := hN fun _ : Fin 1 => x
  exact ⟨α, hα, hsurj, hx n α hα (hkill 0)⟩

end InverseGalois.Shafarevich

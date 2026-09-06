/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.ShaTate

/-!
# Complete cohomology of a level covers the everywhere locally trivial classes of degree two

Global duality for a finite module over a number field says that the everywhere locally trivial
classes of the second cohomology are the characters of the everywhere locally trivial classes of
the first cohomology of the Cartier dual.  Read against the pairing of a cyclic representation with
the maps out of it, that identification has a consequence about a finite Galois level: since every
character of the locally trivial classes of degree one is the pairing against a single class of
complete cohomology of the level in degree minus two, **the complete cohomology of the level in
degree minus two covers the everywhere locally trivial classes of the second cohomology.**

That covering is what an embedding problem wants.  Its obstruction is a class of the second
cohomology which the local conditions have already made everywhere locally trivial; a covering
turns that single class into a single class of complete cohomology of a finite group, where the
group-theoretic constructions that shrink an obstruction apply.

This file names the duality and draws the consequence.  The duality is used only through the
comparison of the two groups of everywhere locally trivial classes; everything else - the injection
of the locally trivial classes into the cohomology of the level, the pairing of the maps into a
cyclic representation with the maps out of it, and the extension of a character along an injection
- is already available, so the covering follows formally.

## Main definitions

* `InverseGalois.CFT.HasPoitouTateDuality`: **the everywhere locally trivial classes of the second
  cohomology are the characters of the everywhere locally trivial classes of the first cohomology
  of the Cartier dual.**
* `InverseGalois.CFT.HasShaDualInjection`: the half of that statement an embedding problem consumes
  - the everywhere locally trivial classes of the second cohomology are read injectively as such
  characters.
* `InverseGalois.CFT.shaCharacter`: the character of the everywhere locally trivial classes cut out
  by a class of complete cohomology in degree minus two.
* `InverseGalois.CFT.shaDualHom`: the resulting map of complete cohomology in degree minus two into
  the everywhere locally trivial classes of the second cohomology.

## Main results

* `InverseGalois.CFT.exists_shaCharacter_eq`: every character of the everywhere locally trivial
  classes of the first cohomology is cut out by a class of complete cohomology.
* `InverseGalois.CFT.hasShaDualInjection_of_hasPoitouTateDuality`,
  `InverseGalois.CFT.hasShaDualInjection_of_subsingleton`: the injective reading follows from the
  duality, and holds for free when there are no everywhere locally trivial classes of the second
  cohomology.
* `InverseGalois.CFT.exists_injective_forall_shaCharacter_eq`: **every everywhere locally trivial
  class of the second cohomology is cut out by a class of complete cohomology of the level, and is
  determined by the character it cuts out.**
* `InverseGalois.CFT.shaDualHom_surjective`,
  `InverseGalois.CFT.exists_surjective_of_hasPoitouTateDuality`: **complete cohomology of the level
  in degree minus two covers the everywhere locally trivial classes of the second cohomology.**

## Tags

Poitou-Tate, global duality, local-global principle, complete cohomology, embedding problem
-/

namespace InverseGalois.CFT

open CategoryTheory groupCohomology Tate

noncomputable section

attribute [local instance] repMulDistribMulAction

section Duality

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  (F : IntermediateField k Ω) [FiniteDimensional k F] [IsGalois k F] [NumberField ↥F]
  (A B : Rep ℤ (↥F ≃ₐ[k] ↥F)) [IsAddCyclic ↥A.V] [Finite ↥A.V] [Finite ↥B.V]
  [MulDistribMulAction Gal(Ω/k) (Multiplicative ↥B.V)]
  [MulDistribMulAction Gal(Ω/k) (Multiplicative ↥(linHomObj B A).V)]

/-- **Global duality for the everywhere locally trivial classes**: the classes of the second
cohomology that die on every decomposition subgroup are the characters of the classes of the first
cohomology of the Cartier dual that die on every decomposition subgroup.  Both groups are cut out
by the same local conditions, one degree apart and on coefficients traded for their dual, and the
duality says the two conditions are exactly complementary. -/
def HasPoitouTateDuality : Prop :=
  Nonempty (Additive ↥(sha2 (Multiplicative ↥B.V) (decompositionSubgroups k Ω)) ≃+
    (Additive ↥(sha1 (Multiplicative ↥(linHomObj B A).V) (decompositionSubgroups k Ω)) →ₗ[ℤ]
      AddCircle (1 : ℚ)))

/-- **One half of global duality**: the everywhere locally trivial classes of the second cohomology
are read *injectively* as characters of the everywhere locally trivial classes of the first
cohomology of the Cartier dual.  Only this half is consumed by an embedding problem: a class of the
second cohomology is then pinned down by the character it cuts out, and the characters are already
exhausted by the complete cohomology of a finite level. -/
def HasShaDualInjection : Prop :=
  ∃ α : Additive ↥(sha2 (Multiplicative ↥B.V) (decompositionSubgroups k Ω)) →+
      (Additive ↥(sha1 (Multiplicative ↥(linHomObj B A).V) (decompositionSubgroups k Ω)) →ₗ[ℤ]
        AddCircle (1 : ℚ)),
    Function.Injective α

omit [IsGalois k Ω] [FiniteDimensional k ↥F] [IsGalois k ↥F] [NumberField ↥F]
  [IsAddCyclic ↥A.V] [Finite ↥A.V] [Finite ↥B.V] in
/-- A duality between the two groups of everywhere locally trivial classes gives the injective
reading. -/
theorem hasShaDualInjection_of_hasPoitouTateDuality (hd : HasPoitouTateDuality F A B) :
    HasShaDualInjection F A B :=
  hd.elim fun D => ⟨D.toAddMonoidHom, D.injective⟩

omit [IsGalois k Ω] [FiniteDimensional k ↥F] [IsGalois k ↥F] [NumberField ↥F]
  [IsAddCyclic ↥A.V] [Finite ↥A.V] [Finite ↥B.V] in
/-- Where there are no everywhere locally trivial classes of the second cohomology at all, the zero
reading is injective. -/
theorem hasShaDualInjection_of_subsingleton
    (h : Subsingleton ↥(sha2 (Multiplicative ↥B.V) (decompositionSubgroups k Ω))) :
    HasShaDualInjection F A B :=
  ⟨0, fun x y _ =>
    Additive.toMul.injective (h.allEq (Additive.toMul x) (Additive.toMul y))⟩

variable (hπ : ∀ (g : Gal(Ω/k)) (m : Multiplicative ↥(linHomObj B A).V),
    g • m = AlgEquiv.restrictNormalHom F g • m)

include hπ

/-- The everywhere locally trivial classes of the first cohomology, inside the complete cohomology
of the level in the degree that the pairing with degree minus two asks for. -/
def shaTateShift :
    Additive ↥(sha1 (Multiplicative ↥(linHomObj B A).V) (decompositionSubgroups k Ω)) →ₗ[ℤ]
      ↥(tateModule (linHomObj B A) (-(-2 : ℤ) - 1)) :=
  shaTateLinear F A B hπ

omit [IsAddCyclic ↥A.V] [Finite ↥A.V] [Finite ↥B.V]
  [MulDistribMulAction Gal(Ω/k) (Multiplicative ↥B.V)] in
/-- The everywhere locally trivial classes are a copy of a submodule of the complete cohomology of
the level. -/
theorem shaTateShift_injective : Function.Injective (shaTateShift F A B hπ) :=
  shaTateLinear_injective F A B hπ

variable (hB : ∀ b : ↥B.V, Nat.card ↥A.V • b = 0)

include hB

/-- **The character of the everywhere locally trivial classes of the first cohomology cut out by a
class of complete cohomology of the level in degree minus two**, through the pairing of the maps
into a cyclic representation with the maps out of it. -/
def shaCharacter (x : ↥(tateModule (linHomObj A B) (-2))) :
    Additive ↥(sha1 (Multiplicative ↥(linHomObj B A).V) (decompositionSubgroups k Ω)) →ₗ[ℤ]
      AddCircle (1 : ℚ) :=
  (cartierPairing A B hB (-2) x).comp (shaTateShift F A B hπ)

omit [MulDistribMulAction Gal(Ω/k) (Multiplicative ↥B.V)] in
/-- The zero class cuts out the zero character. -/
theorem shaCharacter_zero : shaCharacter F A B hπ hB 0 = 0 := by
  rw [shaCharacter, _root_.map_zero, LinearMap.zero_comp]

omit [MulDistribMulAction Gal(Ω/k) (Multiplicative ↥B.V)] in
/-- A sum of classes cuts out the sum of the characters. -/
theorem shaCharacter_add (x y : ↥(tateModule (linHomObj A B) (-2))) :
    shaCharacter F A B hπ hB (x + y)
      = shaCharacter F A B hπ hB x + shaCharacter F A B hπ hB y := by
  rw [shaCharacter, shaCharacter, shaCharacter, _root_.map_add, LinearMap.add_comp]

omit [MulDistribMulAction Gal(Ω/k) (Multiplicative ↥B.V)] in
/-- **Every character of the everywhere locally trivial classes of the first cohomology is cut out
by a class of complete cohomology of the level in degree minus two.** -/
theorem exists_shaCharacter_eq
    (χ : Additive ↥(sha1 (Multiplicative ↥(linHomObj B A).V) (decompositionSubgroups k Ω)) →ₗ[ℤ]
      AddCircle (1 : ℚ)) :
    ∃ x, shaCharacter F A B hπ hB x = χ := by
  obtain ⟨x, hx⟩ := exists_cartierPairing_eq A B hB (-2) (shaTateShift F A B hπ)
    (shaTateShift_injective F A B hπ) χ
  exact ⟨x, LinearMap.ext hx⟩

/-- **What an embedding problem consumes.**  Given the injective reading of the everywhere locally
trivial classes of the second cohomology as characters, every such class is cut out by a class of
complete cohomology of the level in degree minus two, and is determined by the character it cuts
out.  A class of complete cohomology that dies under a change of coefficients therefore forces the
locally trivial class it came from to die with it. -/
theorem exists_injective_forall_shaCharacter_eq (h : HasShaDualInjection F A B) :
    ∃ α : Additive ↥(sha2 (Multiplicative ↥B.V) (decompositionSubgroups k Ω)) →+
        (Additive ↥(sha1 (Multiplicative ↥(linHomObj B A).V) (decompositionSubgroups k Ω)) →ₗ[ℤ]
          AddCircle (1 : ℚ)),
      Function.Injective α ∧ ∀ ε, ∃ x : ↥(tateModule (linHomObj A B) (-2)),
        shaCharacter F A B hπ hB x = α ε :=
  h.elim fun α hα => ⟨α, hα, fun ε => exists_shaCharacter_eq F A B hπ hB (α ε)⟩

/-- **Complete cohomology of the level in degree minus two, in the everywhere locally trivial
classes of the second cohomology**, read through a duality between those classes and the characters
of the locally trivial classes of the first cohomology of the Cartier dual. -/
def shaDualHom
    (D : Additive ↥(sha2 (Multiplicative ↥B.V) (decompositionSubgroups k Ω)) ≃+
      (Additive ↥(sha1 (Multiplicative ↥(linHomObj B A).V) (decompositionSubgroups k Ω)) →ₗ[ℤ]
        AddCircle (1 : ℚ))) :
    ↥(tateModule (linHomObj A B) (-2)) →+
      Additive ↥(sha2 (Multiplicative ↥B.V) (decompositionSubgroups k Ω)) where
  toFun x := D.symm (shaCharacter F A B hπ hB x)
  map_zero' :=
    (congrArg D.symm (shaCharacter_zero F A B hπ hB)).trans (_root_.map_zero D.symm)
  map_add' x y :=
    (congrArg D.symm (shaCharacter_add F A B hπ hB x y)).trans (_root_.map_add D.symm _ _)

/-- **The map onto the everywhere locally trivial classes of the second cohomology is surjective**:
a duality partner of a locally trivial class is a character, and every character is cut out by a
class of complete cohomology. -/
theorem shaDualHom_surjective
    (D : Additive ↥(sha2 (Multiplicative ↥B.V) (decompositionSubgroups k Ω)) ≃+
      (Additive ↥(sha1 (Multiplicative ↥(linHomObj B A).V) (decompositionSubgroups k Ω)) →ₗ[ℤ]
        AddCircle (1 : ℚ))) :
    Function.Surjective (shaDualHom F A B hπ hB D) := by
  intro a
  obtain ⟨x, hx⟩ := exists_shaCharacter_eq F A B hπ hB (D a)
  exact ⟨x, (congrArg D.symm hx).trans (D.symm_apply_apply a)⟩

/-- **Under global duality the complete cohomology of the level in degree minus two covers the
everywhere locally trivial classes of the second cohomology.** -/
theorem exists_surjective_of_hasPoitouTateDuality (hd : HasPoitouTateDuality F A B) :
    ∃ Φ : ↥(tateModule (linHomObj A B) (-2)) →+
        Additive ↥(sha2 (Multiplicative ↥B.V) (decompositionSubgroups k Ω)),
      Function.Surjective Φ :=
  hd.elim fun D => ⟨shaDualHom F A B hπ hB D, shaDualHom_surjective F A B hπ hB D⟩

end Duality

end

end InverseGalois.CFT

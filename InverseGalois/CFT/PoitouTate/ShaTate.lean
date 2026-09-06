/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.CyclicTate
import InverseGalois.CFT.Profinite.Discrete
import InverseGalois.CFT.TateCohomology.CyclicDual
import InverseGalois.CFT.Units.HasseDecomposition

/-!
# The everywhere locally trivial classes as characters of complete cohomology

Take a Galois extension of a number field and a finite module for its Galois group on which the
action is trivial on a finite Galois level.  A class of the first cohomology that dies on every
decomposition subgroup is then inflated from that level, and inflation from a level is injective,
so the everywhere locally trivial classes are a copy of a subgroup of the first cohomology of the
finite Galois group of the level.  On a finite group carrying the discrete topology the smoothness
condition on a cochain is empty, so that first cohomology is the ordinary first cohomology of the
additive copy of the coefficients, which is complete cohomology in degree one.  The everywhere
locally trivial classes therefore sit inside the complete cohomology of the level in degree one.

Now let the coefficients be the maps of a finite module into a finite cyclic one which kills it.
Complete cohomology in degree one of those maps is dual to complete cohomology in degree minus two
of the maps the other way, and the rational circle is injective, so a character of a subgroup
extends to the whole.  Every character of the everywhere locally trivial classes is consequently
the pairing against a single class of complete cohomology in degree minus two of the maps out of
the cyclic module: the complete cohomology of the level in that degree exhausts the characters of
the everywhere locally trivial classes.

## Main definitions

* `InverseGalois.CFT.h1AddEquiv`: the first cohomology of the action attached to a representation
  is the first cohomology of the representation.
* `InverseGalois.CFT.smoothH1RepHom`: the smooth first cohomology of a discrete group, read in the
  first cohomology of a representation.
* `InverseGalois.CFT.restrictRepAction`: the action of a whole Galois group on a representation of
  a finite level, through restriction to that level.
* `InverseGalois.CFT.shaTateLinear`: **the everywhere locally trivial classes of the first
  cohomology, inside the complete cohomology of the level in degree one.**

## Main results

* `InverseGalois.CFT.smoothH1RepHom_injective`,
  `InverseGalois.CFT.shaTateLinear_injective`: the two comparisons are injective.
* `InverseGalois.CFT.exists_cartierPairing_sha_eq`: **every character of the everywhere locally
  trivial classes of the first cohomology of the maps into a cyclic representation is realised by
  a class of complete cohomology in degree minus two of the maps out of it.**

## Tags

Galois cohomology, local-global principle, complete cohomology, Tate cohomology, duality
-/

namespace InverseGalois.CFT

open CategoryTheory groupCohomology Tate

noncomputable section

attribute [local instance] repMulDistribMulAction

/-! ### The smooth cohomology of a finite group as complete cohomology -/

section Level

variable {G : Type} [Group G]

/-- The first cohomology of the action attached to a representation is the first cohomology of the
representation. -/
def h1AddEquiv (A : Rep ℤ G) :
    ↥(H1 (Rep.ofMulDistribMulAction G (Multiplicative ↥A.V))) ≃+ ↥(H1 A) :=
  ((groupCohomology.functor ℤ G 1).mapIso (repIso A)).toLinearEquiv.toAddEquiv

variable [TopologicalSpace G] [DiscreteTopology G]

/-- **The smooth first cohomology of a discrete group, in the first cohomology of a
representation.** -/
def smoothH1RepHom (A : Rep ℤ G) :
    Additive (SmoothH1 G (Multiplicative ↥A.V)) →+ ↥(H1 A) where
  toFun z := h1AddEquiv A
    (Multiplicative.toAdd (discreteSmoothH1Equiv G (Multiplicative ↥A.V) (Additive.toMul z)))
  map_zero' := by
    show h1AddEquiv A (Multiplicative.toAdd
      (discreteSmoothH1Equiv G (Multiplicative ↥A.V) 1)) = 0
    rw [_root_.map_one]
    exact _root_.map_zero _
  map_add' x y := by
    show h1AddEquiv A (Multiplicative.toAdd (discreteSmoothH1Equiv G (Multiplicative ↥A.V)
      (Additive.toMul x * Additive.toMul y))) = _
    rw [_root_.map_mul]
    exact _root_.map_add _ _ _

/-- The comparison is injective: on a discrete group every cocycle is smooth, and a cocycle whose
additive class vanishes is a coboundary. -/
theorem smoothH1RepHom_injective (A : Rep ℤ G) : Function.Injective (smoothH1RepHom A) := by
  intro x y h
  have h1 : discreteSmoothH1Equiv G (Multiplicative ↥A.V) (Additive.toMul x)
      = discreteSmoothH1Equiv G (Multiplicative ↥A.V) (Additive.toMul y) :=
    Multiplicative.toAdd.injective ((h1AddEquiv A).injective h)
  exact Additive.toMul.injective ((discreteSmoothH1Equiv G (Multiplicative ↥A.V)).injective h1)

end Level

/-! ### The everywhere locally trivial classes in the complete cohomology of a level -/

section Sha

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  (F : IntermediateField k Ω) [FiniteDimensional k F] [IsGalois k F] [NumberField ↥F]

/-- The action of a whole Galois group on the multiplicative copy of a representation of a finite
level, through restriction to that level. -/
def restrictRepAction (X : Rep ℤ (↥F ≃ₐ[k] ↥F)) :
    MulDistribMulAction Gal(Ω/k) (Multiplicative ↥X.V) :=
  MulDistribMulAction.compHom _ (AlgEquiv.restrictNormalHom F)

omit [IsGalois k Ω] [FiniteDimensional k ↥F] [NumberField ↥F] in
/-- The action through restriction is the action of the restriction. -/
theorem restrictRepAction_smul (X : Rep ℤ (↥F ≃ₐ[k] ↥F)) :
    letI := restrictRepAction F X
    ∀ (g : Gal(Ω/k)) (m : Multiplicative ↥X.V), g • m = AlgEquiv.restrictNormalHom F g • m :=
  fun _ _ => rfl

variable (A B : Rep ℤ (↥F ≃ₐ[k] ↥F)) [IsAddCyclic ↥A.V] [Finite ↥A.V] [Finite ↥B.V]
  [MulDistribMulAction Gal(Ω/k) (Multiplicative ↥(linHomObj B A).V)]
  (hπ : ∀ (g : Gal(Ω/k)) (m : Multiplicative ↥(linHomObj B A).V),
    g • m = AlgEquiv.restrictNormalHom F g • m)

include hπ

/-- **The everywhere locally trivial classes of the first cohomology of the maps into a cyclic
representation, in the first cohomology of the level.** -/
def shaTateHom :
    Additive ↥(sha1 (Multiplicative ↥(linHomObj B A).V) (decompositionSubgroups k Ω)) →+
      ↥(tateModule (linHomObj B A) 1) :=
  haveI : IsSmoothAction Gal(Ω/k) (Multiplicative ↥(linHomObj B A).V) :=
    isSmoothAction_of_isOpenNormal_ker _ hπ (isOpenNormal_ker_restrictNormalHom F)
  { toFun := fun z => smoothH1RepHom (linHomObj B A)
      (Additive.ofMul (shaInflH1 _ F hπ (Additive.toMul z)))
    map_zero' := by
      show smoothH1RepHom (linHomObj B A) (Additive.ofMul (shaInflH1 _ F hπ 1)) = 0
      rw [_root_.map_one]
      exact _root_.map_zero _
    map_add' := fun x y => by
      show smoothH1RepHom (linHomObj B A) (Additive.ofMul (shaInflH1 _ F hπ
        (Additive.toMul x * Additive.toMul y))) = _
      rw [_root_.map_mul]
      exact _root_.map_add _ _ _ }

omit [IsAddCyclic ↥A.V] [Finite ↥A.V] [Finite ↥B.V] in
/-- An everywhere locally trivial class is determined by the class of the level it gives. -/
theorem shaTateHom_injective : Function.Injective (shaTateHom F A B hπ) := by
  haveI : IsSmoothAction Gal(Ω/k) (Multiplicative ↥(linHomObj B A).V) :=
    isSmoothAction_of_isOpenNormal_ker _ hπ (isOpenNormal_ker_restrictNormalHom F)
  intro x y h
  have h1 : shaInflH1 (Multiplicative ↥(linHomObj B A).V) F hπ (Additive.toMul x)
      = shaInflH1 (Multiplicative ↥(linHomObj B A).V) F hπ (Additive.toMul y) :=
    Additive.ofMul.injective (smoothH1RepHom_injective (linHomObj B A) h)
  exact Additive.toMul.injective
    (shaInflH1_injective (Multiplicative ↥(linHomObj B A).V) F hπ h1)

/-- **The everywhere locally trivial classes of the first cohomology, inside the complete
cohomology of the level in degree one.** -/
def shaTateLinear :
    Additive ↥(sha1 (Multiplicative ↥(linHomObj B A).V) (decompositionSubgroups k Ω)) →ₗ[ℤ]
      ↥(tateModule (linHomObj B A) 1) :=
  intLinear (shaTateHom F A B hπ)

omit [IsAddCyclic ↥A.V] [Finite ↥A.V] [Finite ↥B.V] in
/-- The everywhere locally trivial classes are a copy of a submodule of the complete cohomology of
the level. -/
theorem shaTateLinear_injective : Function.Injective (shaTateLinear F A B hπ) :=
  shaTateHom_injective F A B hπ

/-- **Every character of the everywhere locally trivial classes of the first cohomology of the maps
into a cyclic representation is realised by a class of complete cohomology in degree minus two of
the maps out of it.** -/
theorem exists_cartierPairing_sha_eq (hB : ∀ b : ↥B.V, Nat.card ↥A.V • b = 0)
    (χ : Additive ↥(sha1 (Multiplicative ↥(linHomObj B A).V) (decompositionSubgroups k Ω)) →ₗ[ℤ]
      AddCircle (1 : ℚ)) :
    ∃ x : ↥(tateModule (linHomObj A B) (-2)),
      ∀ t, cartierPairing A B hB (-2) x (shaTateLinear F A B hπ t) = χ t := by
  have h := exists_cartierPairing_eq A B hB (-2) (shaTateLinear F A B hπ)
    (shaTateLinear_injective F A B hπ) χ
  exact h

end Sha

end

end InverseGalois.CFT

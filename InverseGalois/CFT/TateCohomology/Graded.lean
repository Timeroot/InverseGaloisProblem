/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Exact
import InverseGalois.CFT.TateCohomology.HomologyJunction

/-!
# The complete cohomology of a finite group

The complete cohomology of a finite group is graded by all of the integers.  In a positive degree
it is the ordinary cohomology, in degree zero the invariants modulo the norms, in degree minus one
the classes of the coinvariants killed by the norm, and in a degree below minus one the ordinary
homology of the degree shifted by one.  A map of representations induces a map in every degree, in
the four ranges by the corresponding four constructions.

A short exact sequence of representations has a connecting map in every degree.  Above degree zero
it is the connecting map of the ordinary cohomology, out of degree zero it is the descent of that
map to the invariants modulo norms, out of degree minus one it is the snake of the ladder of the
norms, out of degree minus two it is the corestriction of the connecting map of the ordinary
homology, and below that it is the connecting map of the ordinary homology.  The resulting
sequence, running through all of the integers, is exact at every one of its spots.

## Main definitions

* `InverseGalois.CFT.Tate.tateModule`: the complete cohomology in an arbitrary integer degree.
* `InverseGalois.CFT.Tate.tateMap`: the map it induces from a map of representations.
* `InverseGalois.CFT.Tate.tateδ`: the connecting map of a short exact sequence.

## Main results

* `InverseGalois.CFT.Tate.tateExact_map_map`, `InverseGalois.CFT.Tate.tateExact_map_δ`,
  `InverseGalois.CFT.Tate.tateExact_δ_map`: **the long exact sequence of the complete cohomology**,
  exact at the three kinds of spot in every integer degree.

## Tags

Tate cohomology, long exact sequence, connecting homomorphism
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

variable {k : Type u} [CommRing k]

/-! ### Exactness of a short complex of modules -/

/-- **A short complex of modules is exact exactly when the two underlying maps are.** -/
theorem functionExact_of_exact {S : ShortComplex (ModuleCat.{u} k)} (hS : S.Exact) :
    Function.Exact ⇑S.f ⇑S.g :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS

variable {G : Type u} [Group G] [Finite G]

/-! ### The graded object -/

/-- **The complete cohomology of a finite group in an arbitrary integer degree.** -/
def tateModule (A : Rep k G) (n : ℤ) : ModuleCat k :=
  match n with
  | .ofNat 0 => ModuleCat.of k (H0 A.ρ)
  | .ofNat (m + 1) => groupCohomology A (m + 1)
  | .negSucc 0 => ModuleCat.of k (Hm1 A.ρ)
  | .negSucc (m + 1) => groupHomology A (m + 1)

theorem tateModule_zero (A : Rep k G) : tateModule A 0 = ModuleCat.of k (H0 A.ρ) := rfl

theorem tateModule_natCast_succ (A : Rep k G) (m : ℕ) :
    tateModule A ((m : ℤ) + 1) = groupCohomology A (m + 1) := rfl

theorem tateModule_neg_one (A : Rep k G) : tateModule A (-1) = ModuleCat.of k (Hm1 A.ρ) := rfl

theorem tateModule_neg_natCast_succ_succ (A : Rep k G) (m : ℕ) :
    tateModule A (-((m : ℤ) + 2)) = groupHomology A (m + 1) := rfl

/-- **The map induced on the complete cohomology by a map of representations.** -/
def tateMap {A B : Rep k G} (φ : A ⟶ B) (n : ℤ) : tateModule A n ⟶ tateModule B n :=
  match n with
  | .ofNat 0 => ModuleCat.ofHom (H0map φ.hom.hom (hom_equivariant φ))
  | .ofNat (m + 1) => groupCohomology.map (MonoidHom.id G) φ (m + 1)
  | .negSucc 0 => ModuleCat.ofHom (Hm1map φ.hom.hom (hom_equivariant φ))
  | .negSucc (m + 1) => groupHomology.map (MonoidHom.id G) φ (m + 1)

/-! ### The connecting map -/

section LongExactSequence

variable {X : ShortComplex (Rep k G)} (hX : X.ShortExact)

include hX

omit [Finite G] in
/-- The map from the sub is injective. -/
theorem shortExact_injective : Function.Injective X.f.hom.hom :=
  (Rep.mono_iff_injective X.f).1 hX.mono_f

omit [Finite G] in
/-- The map to the quotient is surjective. -/
theorem shortExact_surjective : Function.Surjective X.g.hom.hom :=
  (Rep.epi_iff_surjective X.g).1 hX.epi_g

omit [Finite G] in
/-- The image of the sub is the kernel of the map to the quotient. -/
theorem shortExact_range_eq_ker :
    LinearMap.range X.f.hom.hom = LinearMap.ker X.g.hom.hom :=
  (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker

/-- **The connecting map in degree minus one**, from the classes of the quotient killed by the norm
to the invariants of the sub modulo the norms. -/
def deltaMid : Hm1 X.X₃.ρ →ₗ[k] H0 X.X₁.ρ :=
  delta X.f.hom.hom (hom_equivariant X.f) X.g.hom.hom (hom_equivariant X.g)
    (shortExact_injective hX) (shortExact_surjective hX) (shortExact_range_eq_ker hX)

/-- **The connecting map of the complete cohomology.** -/
def tateδ (n : ℤ) : tateModule X.X₃ n ⟶ tateModule X.X₁ (n + 1) :=
  match n with
  | .ofNat 0 => ModuleCat.ofHom (H0toH1 hX)
  | .ofNat (m + 1) => groupCohomology.δ hX (m + 1) (m + 2) rfl
  | .negSucc 0 => ModuleCat.ofHom (deltaMid hX)
  | .negSucc 1 => ModuleCat.ofHom (H1toHm1 hX)
  | .negSucc (m + 2) => groupHomology.δ hX (m + 2) (m + 1) rfl

/-! ### Exactness -/

/-- **Exactness at the complete cohomology of the middle term.** -/
theorem tateExact_map_map (n : ℤ) :
    Function.Exact (tateMap X.f n) (tateMap X.g n) := by
  match n with
  | .ofNat 0 =>
    exact exact_H0_H0 X.f.hom.hom (hom_equivariant X.f) X.g.hom.hom (hom_equivariant X.g)
      (shortExact_injective hX) (shortExact_surjective hX) (shortExact_range_eq_ker hX)
  | .ofNat (m + 1) =>
    exact functionExact_of_exact (groupCohomology.mapShortComplex₂_exact hX (m + 1))
  | .negSucc 0 =>
    exact exact_Hm1_Hm1 X.f.hom.hom (hom_equivariant X.f) X.g.hom.hom (hom_equivariant X.g)
      (shortExact_injective hX) (shortExact_surjective hX) (shortExact_range_eq_ker hX)
  | .negSucc (m + 1) =>
    exact functionExact_of_exact (groupHomology.mapShortComplex₂_exact hX (m + 1))

/-- **Exactness at the complete cohomology of the quotient.** -/
theorem tateExact_map_δ (n : ℤ) :
    Function.Exact (tateMap X.g n) (tateδ hX n) := by
  match n with
  | .ofNat 0 => exact exact_H0_H0toH1 hX
  | .ofNat (m + 1) =>
    exact functionExact_of_exact
      (groupCohomology.mapShortComplex₃_exact hX (i := m + 1) (j := m + 2) rfl)
  | .negSucc 0 =>
    exact exact_Hm1_delta X.f.hom.hom (hom_equivariant X.f) X.g.hom.hom (hom_equivariant X.g)
      (shortExact_injective hX) (shortExact_surjective hX) (shortExact_range_eq_ker hX)
  | .negSucc 1 => exact exact_H1_H1toHm1 hX
  | .negSucc (m + 2) =>
    exact functionExact_of_exact
      (groupHomology.mapShortComplex₃_exact hX (i := m + 2) (j := m + 1) rfl)

/-- **Exactness at the complete cohomology of the sub.** -/
theorem tateExact_δ_map (n : ℤ) :
    Function.Exact (tateδ hX n) (tateMap X.f (n + 1)) := by
  match n with
  | .ofNat 0 => exact exact_H0toH1_H1 hX
  | .ofNat (m + 1) =>
    exact functionExact_of_exact
      (groupCohomology.mapShortComplex₁_exact hX (i := m + 1) (j := m + 2) rfl)
  | .negSucc 0 =>
    exact exact_delta_H0 X.f.hom.hom (hom_equivariant X.f) X.g.hom.hom (hom_equivariant X.g)
      (shortExact_injective hX) (shortExact_surjective hX) (shortExact_range_eq_ker hX)
  | .negSucc 1 => exact exact_H1toHm1_Hm1 hX
  | .negSucc (m + 2) =>
    exact functionExact_of_exact
      (groupHomology.mapShortComplex₁_exact hX (i := m + 2) (j := m + 1) rfl)

end LongExactSequence

end

end InverseGalois.CFT.Tate

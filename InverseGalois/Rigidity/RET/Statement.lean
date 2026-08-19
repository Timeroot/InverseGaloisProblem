/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The honest Riemann Existence Theorem: its recognizable conclusion

This file names the **textbook conclusion** of the rigidity method — the object the honest
Riemann Existence Theorem actually produces — so that the axiom cut can be phrased against a
statement one would recognize from Völklein, *Groups as Galois Groups* (Thm 2.13) or Serre,
*Topics in Galois Theory* (§8): *a finite group with a rigid, rational, generating,
product-one tuple occurs as the Galois group of a **regular** extension of `ℚ(T)`.*

The now-retired axiom `riemann_existence_ax` was **over-specified**: it handed over the entire
`of_regular_family` polynomial bundle — a monic `ℚ[T][X]` family, an absolutely irreducible
resolvent, cofinite separability, and the *per-specialization* landing/root certificates.  A
textbook RET produces none of that arithmetic model; it produces a **field extension**.  It has
been replaced by the covers-form theorem `riemann_existence_cover` (`RET.Existence`), whose output
is exactly such a field extension.  This file defines that field extension as
`IsRegularInverseGalois`, the honest target: the two Mathlib-blocked steps

* `RigidityCertificate G → IsRegularInverseGalois G` (RET + branch-cycle descent), and
* `IsRegularInverseGalois G → IsInverseGalois G` (specialization / Hilbert irreducibility),

can then each be stated recognizably, instead of being smuggled together into one bundle.

The same conclusion makes sense over any base field, and the rigidity method reaches `ℚ` only
when the prescribed classes are rational.  When they are merely stable under a subgroup of the
cyclotomic action the method still applies, but lands over the corresponding subfield of a
cyclotomic field — so the definition below is stated over an arbitrary base field `K`, with the
`ℚ` case named separately.

## Main definitions

* `IsRegularGaloisGroupOverBase k F G` — there is a finite Galois extension `L / F` with
  `Gal(L / F) ≃* G` in which the constant field `k` stays relatively algebraically closed.  Stated
  for an abstract base `F / k` so that the base can be a rational function field presented either
  as `RatFunc K` or as an intermediate field `K(T)` of a bigger tower.
* `IsRegularGaloisGroupOver K G` — the case `F = K(T)`: a regular Galois extension `L / K(T)` with
  `Gal(L / K(T)) ≃* G`, "regular" meaning `K` is relatively algebraically closed in `L` (the
  field of constants of `L` is exactly `K`, i.e. `algebraicClosure K L = ⊥`).
* `IsRegularInverseGalois G` — the base `ℚ(T)`, i.e. `IsRegularGaloisGroupOver ℚ G`.

## Main results

* `IsRegularGaloisGroupOverBase.of_algEquiv` — the base may be replaced by any `k`-isomorphic
  field, which is what lets a base realized as a subfield of a tower be recognized as `K(T)`.
* `isRegularGaloisGroupOverBase_rat_iff`, `isRegularInverseGalois_of_overBase` — over `ℚ` the
  predicate does not depend on which of the two available `ℚ`-algebra structures the base is
  presented with.
* `IsRegularGaloisGroupOverBase.of_mulEquiv`, `IsRegularGaloisGroupOver.of_mulEquiv`,
  `IsRegularInverseGalois.of_mulEquiv` — invariance under group isomorphism.
-/

open Polynomial

/-- A group `G` is a **regular Galois group over the base `F / k`** if there is a finite Galois
extension `L / F` with `Gal(L / F) ≃* G` that is **regular over `k`**: the constant field `k` is
relatively algebraically closed in `L`, i.e. `algebraicClosure k L = ⊥`.

The intended `F` is a rational function field `k(T)`, but leaving it abstract matters: in the
descent the base appears as an intermediate field `K(T)` of a fixed tower `Ω / ℚ(T)`, and only
afterwards is it recognized as a copy of `RatFunc K`. -/
def IsRegularGaloisGroupOverBase (k : Type*) [Field k] (F : Type*) [Field F] [Algebra k F]
    (G : Type*) [Group G] : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : Algebra F L) (_ : FiniteDimensional F L) (_ : IsGalois F L)
    (_ : Algebra k L) (_ : IsScalarTower k F L),
    algebraicClosure k L = ⊥ ∧ Nonempty ((L ≃ₐ[F] L) ≃* G)

/-- A group `G` is a **regular Galois group over `K(T)`** if there is a finite Galois extension
`L / K(T)` with `Gal(L / K(T)) ≃* G` that is **regular**: `K` is relatively algebraically closed
in `L`, i.e. the relative algebraic closure `algebraicClosure K L` is the bottom intermediate
field `⊥ = K` (`L` gains no new constants over `K`).

This is the recognizable conclusion of the rigidity method (Völklein, *Groups as Galois Groups*,
Thm 2.13).  Regularity is exactly what makes the extension specialize: over a number field it
descends to a genuine `K`-Galois extension with the same group at infinitely many values of `T`
(Hilbert irreducibility). -/
def IsRegularGaloisGroupOver (K : Type*) [Field K] (G : Type*) [Group G] : Prop :=
  IsRegularGaloisGroupOverBase K (RatFunc K) G

/-- A group `G` is a **regular inverse Galois group** if it is a regular Galois group over `ℚ(T)`:
there is a finite Galois extension `L / ℚ(T)` with `Gal(L / ℚ(T)) ≃* G` in which `ℚ` is relatively
algebraically closed.

Regularity is exactly what makes the extension specialize: it descends to a genuine `ℚ`-Galois
extension with the same group at infinitely many values of `T` (Hilbert irreducibility), giving
`IsInverseGalois G`. -/
def IsRegularInverseGalois (G : Type*) [Group G] : Prop :=
  IsRegularGaloisGroupOver ℚ G

/-- **The base's rational structure is irrelevant.**  A field carries at most one `ℚ`-algebra
structure, so the two ways elaboration can present `ℚ → ℚ(T)` — the localization action and the
rational structure of a field of characteristic zero — define the same predicate. -/
theorem isRegularGaloisGroupOverBase_rat_iff {F : Type*} [Field F] {G : Type*} [Group G]
    (inst₁ inst₂ : Algebra ℚ F) :
    @IsRegularGaloisGroupOverBase ℚ _ F _ inst₁ G _ ↔
      @IsRegularGaloisGroupOverBase ℚ _ F _ inst₂ G _ := by
  rw [Subsingleton.elim inst₁ inst₂]

/-- A regular realization over `ℚ(T)` is a regular inverse Galois realization, whichever of the
two `ℚ`-algebra structures on `ℚ(T)` the hypothesis is stated with. -/
theorem isRegularInverseGalois_of_overBase {G : Type*} [Group G] (inst : Algebra ℚ (RatFunc ℚ))
    (h : @IsRegularGaloisGroupOverBase ℚ _ (RatFunc ℚ) _ inst G _) : IsRegularInverseGalois G := by
  unfold IsRegularInverseGalois IsRegularGaloisGroupOver
  exact (isRegularGaloisGroupOverBase_rat_iff inst _).mp h

namespace IsRegularGaloisGroupOverBase

variable {k : Type*} [Field k] {F : Type*} [Field F] [Algebra k F] {G H : Type*} [Group G] [Group H]

/-- Invariance under group isomorphism. -/
theorem of_mulEquiv (hG : IsRegularGaloisGroupOverBase k F G) (e : G ≃* H) :
    IsRegularGaloisGroupOverBase k F H := by
  obtain ⟨L, hF, hA, hFD, hGal, hAk, hST, hreg, ⟨φ⟩⟩ := hG
  exact ⟨L, hF, hA, hFD, hGal, hAk, hST, hreg, ⟨φ.trans e⟩⟩

end IsRegularGaloisGroupOverBase

namespace IsRegularGaloisGroupOver

variable {K : Type*} [Field K] {G H : Type*} [Group G] [Group H]

/-- The rational-function-field case of `IsRegularGaloisGroupOverBase`, unfolded. -/
theorem eq_overBase : IsRegularGaloisGroupOver K G = IsRegularGaloisGroupOverBase K (RatFunc K) G :=
  rfl

/-- Invariance under group isomorphism: a regular Galois realization of `G` is also one of any
group isomorphic to `G`. -/
theorem of_mulEquiv (hG : IsRegularGaloisGroupOver K G) (e : G ≃* H) :
    IsRegularGaloisGroupOver K H :=
  IsRegularGaloisGroupOverBase.of_mulEquiv hG e

end IsRegularGaloisGroupOver

namespace IsRegularInverseGalois

variable {G H : Type*} [Group G] [Group H]

/-- Invariance under group isomorphism: a regular Galois realization of `G` is also one of any
group isomorphic to `G`. -/
theorem of_mulEquiv (hG : IsRegularInverseGalois G) (e : G ≃* H) :
    IsRegularInverseGalois H :=
  IsRegularGaloisGroupOver.of_mulEquiv (K := ℚ) hG e

end IsRegularInverseGalois

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Rigidity.RET.Pi1.Topological.CircleGroup
import InverseGalois.Rigidity.RET.Presentation
import Mathlib.GroupTheory.CoprodI
import Mathlib.Algebra.FreeAbelianGroup.Finsupp

/-!
# The wedge-of-circles model of the sphere group

Classically the `r`-punctured Riemann sphere is homotopy-equivalent to a wedge of `r - 1` circles,
so its fundamental group is the **free product of `r - 1` copies of `ℤ`** — one infinite-cyclic
factor for each independent loop, i.e. for each local monodromy (inertia) generator that survives
the single global relation `x₀···x_{r-1} = 1`.  This file records that identification purely
algebraically, on the presentation group `Γ_r` (`SphereGroup r`):

* `Monoid.CoprodI.congr` — a free product transports along a family of factorwise isomorphisms
  (the coproduct is functorial in its factors); missing from Mathlib.
* `Rigidity.RET.freeGroupUnitMulEquivInt : FreeGroup Unit ≃* Multiplicative ℤ`.
* `Rigidity.RET.freeGroupMulEquivCoprodInt : FreeGroup ι ≃* CoprodI (fun _ : ι => Multiplicative ℤ)`
  — a free group **is** the free product of copies of `ℤ`, the `π₁` of a wedge of circles / of the
  punctured plane.
* `Rigidity.RET.sphereGroup_mulEquiv_coprodInt` — **`Γ_r ≅ ⋆_{r-1} ℤ`** for `r ≥ 1`: the sphere
  group is the free product of `r - 1` copies of `ℤ`.
* `Rigidity.RET.sphereGroup_mulEquiv_coprod_pi1Units` — the same factors displayed as the local
  fundamental groups `π₁(ℂˣ)`: `Γ_r ≅ ⋆_{r-1} π₁(ℂˣ)`.

Combined with `Complex.fundamentalGroupUnits` (`π₁(ℂˣ) ≅ ℤ`), this is the *algebraic* half of the
Riemann-existence comparison `π₁^top(S² ∖ r pts) ≅ Γ_r` for link **C**: it exhibits `Γ_r` as the
free product of the local monodromy groups.  The remaining, genuinely topological, half — that the
punctured sphere's *topological* `π₁` realizes this free product — is supplied by the
Seifert–van Kampen theorem of `VanKampen/` and carried out in `PuncturedPlane.lean`.
-/

open scoped Multiplicative

namespace Monoid.CoprodI

variable {ι : Type*} {M N : ι → Type*} [∀ i, Monoid (M i)] [∀ i, Monoid (N i)]

/-- **Functoriality of the free product in its factors.**  A family of monoid isomorphisms
`e i : M i ≃* N i` induces an isomorphism of free products `CoprodI M ≃* CoprodI N`, sending the
`i`-th factor by `e i`.  Built from the universal property (`CoprodI.lift`): both directions are the
lifts of the factorwise maps, and they are mutually inverse because they agree with the identity on
each factor. -/
def congr (e : ∀ i, M i ≃* N i) : CoprodI M ≃* CoprodI N where
  toFun := CoprodI.lift (fun i => CoprodI.of.comp (e i).toMonoidHom)
  invFun := CoprodI.lift (fun i => CoprodI.of.comp (e i).symm.toMonoidHom)
  left_inv := by
    have h : (CoprodI.lift (fun i => CoprodI.of.comp (e i).symm.toMonoidHom)).comp
        (CoprodI.lift (fun i => CoprodI.of.comp (e i).toMonoidHom)) = MonoidHom.id (CoprodI M) := by
      ext i x
      simp
    exact DFunLike.congr_fun h
  right_inv := by
    have h : (CoprodI.lift (fun i => CoprodI.of.comp (e i).toMonoidHom)).comp
        (CoprodI.lift (fun i => CoprodI.of.comp (e i).symm.toMonoidHom)) = MonoidHom.id (CoprodI N) := by
      ext i x
      simp
    exact DFunLike.congr_fun h
  map_mul' := map_mul _

@[simp]
theorem congr_of (e : ∀ i, M i ≃* N i) {i : ι} (x : M i) :
    congr e (CoprodI.of x) = CoprodI.of (e i x) := by
  simp [congr]

end Monoid.CoprodI

namespace Rigidity.RET

open Monoid

/-- The free group on the one-point type is infinite cyclic: `FreeGroup Unit ≃* Multiplicative ℤ`,
sending the generator to `ofAdd 1`.  (The `Unit`-indexed companion of `freeGroupFin1MulEquivInt`,
used as the per-factor isomorphism in `freeGroupMulEquivCoprodInt`.) -/
noncomputable def freeGroupUnitMulEquivInt : FreeGroup Unit ≃* Multiplicative ℤ where
  toFun := FreeGroup.lift (fun _ => Multiplicative.ofAdd (1 : ℤ))
  invFun := zpowersHom (FreeGroup Unit) (FreeGroup.of ())
  left_inv w := by
    have h : (zpowersHom (FreeGroup Unit) (FreeGroup.of ())).comp
        (FreeGroup.lift (fun _ => Multiplicative.ofAdd (1 : ℤ))) = MonoidHom.id _ :=
      FreeGroup.ext_hom _ _ (fun _ => by simp [FreeGroup.lift_apply_of])
    exact DFunLike.congr_fun h w
  right_inv n := by
    have h : (FreeGroup.lift (fun _ => Multiplicative.ofAdd (1 : ℤ))).comp
        (zpowersHom (FreeGroup Unit) (FreeGroup.of ())) = MonoidHom.id _ :=
      MonoidHom.ext_mint (by simp [FreeGroup.lift_apply_of])
    exact DFunLike.congr_fun h n
  map_mul' := map_mul _

/-- **A free group is a free product of copies of `ℤ`.**  `FreeGroup ι ≃* ⋆_{ι} ℤ`: composing
Mathlib's `freeGroupEquivCoprodI` (`FreeGroup ι ≃* CoprodI (fun _ => FreeGroup Unit)`) with the
factorwise `FreeGroup Unit ≃* ℤ`.  This is the fundamental group of a wedge of `|ι|` circles (or of
the `|ι|`-punctured plane): one free `ℤ` per loop, with no relations among them. -/
noncomputable def freeGroupMulEquivCoprodInt (ι : Type*) :
    FreeGroup ι ≃* CoprodI (fun _ : ι => Multiplicative ℤ) :=
  freeGroupEquivCoprodI.trans (CoprodI.congr (fun _ => freeGroupUnitMulEquivInt))

/-- **`Γ_r ≅ ⋆_{r-1} ℤ`.**  For `r ≥ 1` the sphere presentation group is the free product of `r - 1`
copies of `ℤ`.  This is the algebraic shadow of the classical homotopy equivalence between the
`r`-punctured sphere and a wedge of `r - 1` circles: the single relation `x₀···x_{r-1} = 1`
eliminates one of the `r` local loops, leaving `r - 1` free infinite-cyclic factors, one per
surviving inertia generator. -/
theorem sphereGroup_mulEquiv_coprodInt (hr : 1 ≤ r) :
    Nonempty (SphereGroup r ≃* CoprodI (fun _ : Fin (r - 1) => Multiplicative ℤ)) :=
  (sphereGroup_mulEquiv_free hr).map fun e => e.trans (freeGroupMulEquivCoprodInt (Fin (r - 1)))

/-- **`H₁` of the `r`-punctured sphere is `ℤ^{r-1}`.**  Abelianizing `Γ_r ≅ FreeGroup (Fin (r-1))`
(the free product of `r - 1` copies of `ℤ` from `sphereGroup_mulEquiv_coprodInt`) yields the free
abelian group of rank `r - 1`, presented as `Fin (r - 1) →₀ ℤ`.  This is the first integral homology
group of the `r`-punctured sphere: the abelianized monodromy, on which the various Galois-theoretic
winding-number counts are read.  (`MulEquiv.abelianizationCongr` transports the free identification
to abelianizations; `FreeAbelianGroup.equivFinsupp` presents the free abelian group as a `Finsupp`.) -/
noncomputable def sphereGroup_abelianization_addEquiv
    (e : SphereGroup r ≃* FreeGroup (Fin (r - 1))) :
    Additive (Abelianization (SphereGroup r)) ≃+ (Fin (r - 1) →₀ ℤ) :=
  (MulEquiv.toAdditive e.abelianizationCongr).trans (FreeAbelianGroup.equivFinsupp (Fin (r - 1)))

/-- **`Γ_r ≅ ⋆_{r-1} π₁(ℂˣ)`.**  The same identification with the free `ℤ` factors displayed as the
local fundamental groups `π₁(ℂˣ) ≅ ℤ` (`Complex.fundamentalGroupUnits`): the sphere group is the
free product of `r - 1` copies of the fundamental group of the punctured plane.  Reading `ℂˣ` as a
punctured neighbourhood of a branch point, each factor is the local monodromy (inertia) group of one
puncture, and `Γ_r` is their free product modulo the eliminated global loop. -/
noncomputable def sphereGroup_mulEquiv_coprod_pi1Units
    (e : SphereGroup r ≃* CoprodI (fun _ : Fin (r - 1) => Multiplicative ℤ)) :
    SphereGroup r ≃* CoprodI (fun _ : Fin (r - 1) => FundamentalGroup ℂˣ Complex.expUnit) :=
  e.trans (CoprodI.congr (fun _ => Complex.fundamentalGroupUnits.symm))

end Rigidity.RET

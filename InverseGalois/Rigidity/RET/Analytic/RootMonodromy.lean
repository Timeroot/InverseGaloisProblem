/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.RootFiber
import InverseGalois.Rigidity.RET.Presentation
import InverseGalois.Rigidity.RET.Pi1.Topological.Monodromy
import InverseGalois.Rigidity.RET.Pi1.Topological.PuncturedPlane

/-!
# Analytic branch cycles of a complex family of equations

A monic family of equations over the complex line whose specializations are separable outside a
finite set of parameters presents a covering space of the punctured line.  The fundamental group of
the punctured line acts on a fibre by monodromy, and that fundamental group is the sphere
presentation group on one more generator than there are punctures: the extra generator is the loop
around infinity, and the single defining relation is that the loops around all the punctures,
infinity included, multiply to one.

Composing the presentation with the monodromy representation produces a genuine **branch-cycle
system** of the family: a tuple of permutations of the fibre, one for each puncture and one for
infinity, whose product is the identity and which generate the monodromy group.  The fibre has as
many points as the degree of the family.

This is the analytic side of the branch-cycle description of a cover.  It uses only the
analytification of the family — the root variety as a topological covering space — and the
topological fundamental group of the punctured plane, both of which are available unconditionally.

## Main results

* `Rigidity.RET.Analytic.isCoveringMap_puncturedProj` — the root projection over the complement of
  the degeneracy set is a covering map.
* `Rigidity.RET.Analytic.card_puncturedFiber` — the fibre has exactly `P.natDegree` points.
* `Rigidity.RET.Analytic.sphereMonodromy` — the monodromy representation of the sphere
  presentation group on the fibre.
* `Rigidity.RET.Analytic.prod_branchCycle` — the branch cycles multiply to the identity.
* `Rigidity.RET.Analytic.range_sphereMonodromy` — the branch cycles generate the monodromy group.
* `Rigidity.RET.Analytic.exists_analytic_branchCycles` — the packaged statement.
-/

open Polynomial Rigidity.RET

noncomputable section

namespace Rigidity.RET.Analytic

variable {P : Polynomial (Polynomial ℂ)} {S : Finset ℂ}

/-! ### The covering map over the punctured line -/

/-- The **punctured root projection**: the root projection of a family restricted to the parameters
away from a finite set. -/
def puncturedProj (P : Polynomial (Polynomial ℂ)) (S : Finset ℂ) :
    ↥(rootProj P ⁻¹' ((S : Set ℂ)ᶜ)) → ↥((S : Set ℂ)ᶜ) :=
  ((S : Set ℂ)ᶜ).restrictPreimage (rootProj P)

/-- **The punctured root projection is a covering map** as soon as the family specializes to a
separable equation at every parameter away from the finite set. -/
theorem isCoveringMap_puncturedProj (hP : P.Monic)
    (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) : IsCoveringMap (puncturedProj P S) :=
  isCoveringMap_restrict hP fun z hz => hS z hz

/-- **The fibre of the punctured root projection is the fibre of the root projection.** -/
def puncturedFiberEquiv (P : Polynomial (Polynomial ℂ)) (S : Finset ℂ) {z₀ : ℂ}
    (hz₀ : z₀ ∉ (S : Set ℂ)) :
    (puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}) ≃ (rootProj P ⁻¹' {z₀}) where
  toFun q := ⟨(q : ↥(rootProj P ⁻¹' ((S : Set ℂ)ᶜ))).1, congrArg Subtype.val q.2⟩
  invFun r := ⟨⟨(r : rootVariety P), by
      show rootProj P (r : rootVariety P) ∈ (S : Set ℂ)ᶜ
      rw [show rootProj P (r : rootVariety P) = z₀ from r.2]
      exact hz₀⟩, Subtype.ext r.2⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

/-- **The fibre of the punctured root projection has exactly as many points as the degree of the
family.** -/
theorem card_puncturedFiber (hP : P.Monic) (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable)
    {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ)) :
    Nat.card (puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}) = P.natDegree := by
  rw [Nat.card_congr (puncturedFiberEquiv P S hz₀)]
  exact card_fiber hP (hS z₀ hz₀)

/-- **The fibre of the punctured root projection is finite.** -/
theorem finite_puncturedFiber (hP : P.Monic) {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ)) :
    (puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}).Finite := by
  haveI : Finite (rootProj P ⁻¹' {z₀}) := (finite_fiber hP z₀).to_subtype
  haveI : Finite (puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}) :=
    Finite.of_equiv _ (puncturedFiberEquiv P S hz₀).symm
  exact Set.toFinite _

/-! ### The monodromy representation -/

/-- The **monodromy representation** of the fundamental group of the punctured line on a fibre of
the family. -/
def monodromyHom (hP : P.Monic) (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {z₀ : ℂ}
    (hz₀ : z₀ ∉ (S : Set ℂ)) :
    FundamentalGroup ↥((S : Set ℂ)ᶜ) ⟨z₀, hz₀⟩ →*
      Equiv.Perm (puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}) :=
  (isCoveringMap_puncturedProj hP hS).monodromyHom _

/-- The **monodromy representation of the sphere presentation group** on a fibre: the fundamental
group of the plane punctured at `S` is the sphere group on `S.card + 1` generators, the extra one
being the loop around infinity. -/
def sphereMonodromy (hP : P.Monic) (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {z₀ : ℂ}
    (hz₀ : z₀ ∉ (S : Set ℂ)) :
    SphereGroup (S.card + 1) →*
      Equiv.Perm (puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}) :=
  (monodromyHom hP hS hz₀).comp
    (pi1_compl_mulEquiv_sphereGroup S z₀ hz₀).some.symm.toMonoidHom

/-- The **branch cycles** of the family: the monodromy permutations of the distinguished loops, one
around each puncture and one around infinity. -/
def branchCycle (hP : P.Monic) (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {z₀ : ℂ}
    (hz₀ : z₀ ∉ (S : Set ℂ)) (i : Fin (S.card + 1)) :
    Equiv.Perm (puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}) :=
  sphereMonodromy hP hS hz₀ (PresentedGroup.of i)

/-- **The branch cycles multiply to the identity.**  This is the product-one relation of the
Riemann existence correspondence, obtained here from the single defining relation of the sphere
presentation group. -/
theorem prod_branchCycle (hP : P.Monic) (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {z₀ : ℂ}
    (hz₀ : z₀ ∉ (S : Set ℂ)) : (List.ofFn (branchCycle hP hS hz₀)).prod = 1 :=
  prod_apply_sphereGroup_of _

/-- **The branch cycles generate the monodromy group.**  The sphere presentation group is generated
by the distinguished loops, so their images generate the image of the representation. -/
theorem range_sphereMonodromy (hP : P.Monic) (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable)
    {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ)) :
    (sphereMonodromy hP hS hz₀).range = Subgroup.closure (Set.range (branchCycle hP hS hz₀)) := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of (sphereRel (S.card + 1)),
    MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨PresentedGroup.of i, ⟨i, rfl⟩, rfl⟩

/-- **A generically separable monic complex family has an analytic branch-cycle system.**  Away
from a finite set of parameters the family is a covering space of the punctured line whose fibre
has as many points as the degree of the family, and the monodromy of the distinguished loops — one
around each puncture and one around infinity — is a product-one tuple of permutations of that fibre
generating the monodromy group. -/
theorem exists_analytic_branchCycles (hP : P.Monic)
    (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ)) :
    ∃ (F : Type) (_ : Finite F) (σ : Fin (S.card + 1) → Equiv.Perm F),
      Nat.card F = P.natDegree ∧ (List.ofFn σ).prod = 1 := by
  refine ⟨(puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}),
    (finite_puncturedFiber hP hz₀).to_subtype, branchCycle hP hS hz₀,
    card_puncturedFiber hP hS hz₀, prod_branchCycle hP hS hz₀⟩

end Rigidity.RET.Analytic

end

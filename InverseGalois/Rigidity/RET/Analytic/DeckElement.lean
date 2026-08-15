/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.LocalCycles
import InverseGalois.Rigidity.RET.Pi1.Topological.MonodromyPath

/-!
# Naming a monodromy element by a deck transformation

A group of root formulas of the right size acts simply transitively on a fibre of the root cover,
so a point of the fibre is named by exactly one group element once a base point is chosen.  The
monodromy of a loop is a permutation of the fibre commuting with the formulas, so it too is named
by a single group element: the one carrying the base point to the point the monodromy comes back
to.  Reading the name off the *inverse* permutation makes the assignment a homomorphism, and
transitivity of monodromy on a connected cover makes it surjective.

What this naming buys, and what the identification of the monodromy group with the group of
formulas does not, is a computation rule: the monodromy of a loop moves *every* point of the fibre
by right multiplication with the name of the loop.  A deck transformation that the monodromy
realizes at a single point of the fibre is therefore conjugate to the name of the loop — which is
how a local computation at one branch of the roots determines the global monodromy element up to
conjugacy.

## Main definitions

* `Rigidity.RET.Analytic.RationalDeck.deckCycle` — the monodromy representation of the punctured
  plane on the group of formulas itself.

## Main results

* `Rigidity.RET.Analytic.RationalDeck.monodromyHom_orbitFibre` — monodromy commutes with the
  formulas.
* `Rigidity.RET.Analytic.RationalDeck.monodromyHom_orbitFibre_base` — the monodromy of a loop
  moves every point of the fibre by right multiplication with its name.
* `Rigidity.RET.Analytic.RationalDeck.surjective_deckCycle` — every element of the group is the
  name of a loop.
* `Rigidity.RET.Analytic.RationalDeck.deckCycle_conj` — a formula that the monodromy of a loop
  realizes at one point of the fibre is conjugate to the inverse of the name of that loop.
* `Rigidity.RET.Analytic.RationalDeck.exists_localizedNames`,
  `Rigidity.RET.Analytic.RationalDeck.exists_localizedNames_degen` — the names of a system of loops
  winding around the individual branch points generate the group.
-/

open Polynomial Rigidity.RET

noncomputable section

namespace Rigidity.RET.Analytic

variable {P : Polynomial (Polynomial ℂ)} {S : Finset ℂ} {G : Type} [Group G]

namespace RationalDeck

variable (D : RationalDeck P S G)

/-! ### The action of the formulas on a fibre -/

theorem smul_one_eq (e : ↥(rootProj P ⁻¹' ((S : Set ℂ)ᶜ))) : D.smul 1 e = e := by
  refine Subtype.ext (Subtype.ext ?_)
  rw [coe_smul, D.act_one (fst_notMem e) (isRoot_snd e)]

theorem smul_smul_eq (g h : G) (e : ↥(rootProj P ⁻¹' ((S : Set ℂ)ᶜ))) :
    D.smul g (D.smul h e) = D.smul (g * h) e := by
  refine Subtype.ext (Subtype.ext ?_)
  rw [coe_smul, coe_smul, coe_smul, D.act_mul g h (fst_notMem e) (isRoot_snd e)]

theorem orbitFibre_one {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ))
    (e₀ : puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}) :
    D.orbitFibre hz₀ e₀ 1 = e₀ :=
  Subtype.ext (D.smul_one_eq _)

theorem orbitFibre_orbitFibre {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ))
    (Y : puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}) (g h : G) :
    D.orbitFibre hz₀ (D.orbitFibre hz₀ Y g) h = D.orbitFibre hz₀ Y (h * g) :=
  Subtype.ext (D.smul_smul_eq _ _ _)

/-- **The monodromy of a loop commutes with the formulas.**  Lifting a path after moving its
starting point by a formula is the same as moving the lift. -/
theorem monodromyHom_orbitFibre (hP : P.Monic) (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable)
    {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ)) (γ : FundamentalGroup ↥((S : Set ℂ)ᶜ) ⟨z₀, hz₀⟩) (g : G)
    (Y : puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}) :
    monodromyHom hP hS hz₀ γ (D.orbitFibre hz₀ Y g)
      = D.orbitFibre hz₀ (monodromyHom hP hS hz₀ γ Y) g :=
  Subtype.ext ((isCoveringMap_puncturedProj hP hS).monodromy_comp_deck (D.continuous_smul g)
    (D.puncturedProj_smul g) γ.toPath Y)

/-- **Transport along a path commutes with the formulas.**  Lifting a path after moving its
starting point by a formula is the same as moving the lift, whether or not the path is a loop. -/
theorem fibreEquiv_orbitFibre (hP : P.Monic) (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable)
    {z₀ z₁ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ)) (hz₁ : z₁ ∉ (S : Set ℂ))
    (q : Path.Homotopic.Quotient (⟨z₁, hz₁⟩ : ↥((S : Set ℂ)ᶜ)) (⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ)))
    (Y : puncturedProj P S ⁻¹' {(⟨z₁, hz₁⟩ : ↥((S : Set ℂ)ᶜ))}) (g : G) :
    IsCoveringMap.fibreEquiv (isCoveringMap_puncturedProj hP hS) q (D.orbitFibre hz₁ Y g)
      = D.orbitFibre hz₀
          (IsCoveringMap.fibreEquiv (isCoveringMap_puncturedProj hP hS) q Y) g :=
  Subtype.ext ((isCoveringMap_puncturedProj hP hS).monodromy_comp_deck (D.continuous_smul g)
    (D.puncturedProj_smul g) q Y)

/-! ### The name of a loop -/

variable [Finite G]

/-- The formula carrying the base point of the fibre to the point the monodromy of a loop comes
back from. -/
def deckCycleFun (hP : P.Monic) (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {z₀ : ℂ}
    (hz₀ : z₀ ∉ (S : Set ℂ)) (hcard : Nat.card G = P.natDegree)
    (e₀ : puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))})
    (γ : FundamentalGroup ↥((S : Set ℂ)ᶜ) ⟨z₀, hz₀⟩) : G :=
  (D.surjective_orbitFibre hP hS hz₀ hcard e₀ ((monodromyHom hP hS hz₀ γ)⁻¹ e₀)).choose

theorem orbitFibre_deckCycleFun (hP : P.Monic)
    (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ))
    (hcard : Nat.card G = P.natDegree)
    (e₀ : puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))})
    (γ : FundamentalGroup ↥((S : Set ℂ)ᶜ) ⟨z₀, hz₀⟩) :
    D.orbitFibre hz₀ e₀ (D.deckCycleFun hP hS hz₀ hcard e₀ γ)
      = (monodromyHom hP hS hz₀ γ)⁻¹ e₀ :=
  (D.surjective_orbitFibre hP hS hz₀ hcard e₀ _).choose_spec

/-- **The monodromy of a loop moves the base point by the inverse of its name.** -/
theorem monodromyHom_base (hP : P.Monic)
    (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ))
    (hcard : Nat.card G = P.natDegree)
    (e₀ : puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))})
    (γ : FundamentalGroup ↥((S : Set ℂ)ᶜ) ⟨z₀, hz₀⟩) :
    monodromyHom hP hS hz₀ γ e₀ = D.orbitFibre hz₀ e₀ (D.deckCycleFun hP hS hz₀ hcard e₀ γ)⁻¹ := by
  obtain ⟨u, hu⟩ := D.surjective_orbitFibre hP hS hz₀ hcard e₀ (monodromyHom hP hS hz₀ γ e₀)
  have h2 : D.orbitFibre hz₀ (monodromyHom hP hS hz₀ γ e₀)
      (D.deckCycleFun hP hS hz₀ hcard e₀ γ) = e₀ := by
    rw [← D.monodromyHom_orbitFibre hP hS hz₀ γ, D.orbitFibre_deckCycleFun hP hS hz₀ hcard e₀ γ]
    exact Equiv.apply_symm_apply _ _
  rw [← hu, D.orbitFibre_orbitFibre] at h2
  have hmul : D.deckCycleFun hP hS hz₀ hcard e₀ γ * u = 1 :=
    D.injective_orbitFibre hz₀ e₀ (h2.trans (D.orbitFibre_one hz₀ e₀).symm)
  rw [← hu, inv_eq_of_mul_eq_one_right hmul]

/-- **The monodromy of a loop moves every point of the fibre by right multiplication with the
inverse of its name.** -/
theorem monodromyHom_orbitFibre_base (hP : P.Monic)
    (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ))
    (hcard : Nat.card G = P.natDegree)
    (e₀ : puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))})
    (γ : FundamentalGroup ↥((S : Set ℂ)ᶜ) ⟨z₀, hz₀⟩) (h : G) :
    monodromyHom hP hS hz₀ γ (D.orbitFibre hz₀ e₀ h)
      = D.orbitFibre hz₀ e₀ (h * (D.deckCycleFun hP hS hz₀ hcard e₀ γ)⁻¹) := by
  rw [D.monodromyHom_orbitFibre hP hS hz₀ γ, D.monodromyHom_base hP hS hz₀ hcard e₀ γ,
    D.orbitFibre_orbitFibre]

/-- **The monodromy representation of the punctured plane on the group of formulas itself**: a
loop is named by the formula carrying the base point of the fibre to the point its monodromy comes
back from. -/
def deckCycle (hP : P.Monic) (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {z₀ : ℂ}
    (hz₀ : z₀ ∉ (S : Set ℂ)) (hcard : Nat.card G = P.natDegree)
    (e₀ : puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}) :
    FundamentalGroup ↥((S : Set ℂ)ᶜ) ⟨z₀, hz₀⟩ →* G :=
  MonoidHom.mk' (D.deckCycleFun hP hS hz₀ hcard e₀) (by
    intro γ δ
    have hkey : D.orbitFibre hz₀ e₀ (D.deckCycleFun hP hS hz₀ hcard e₀ (γ * δ))⁻¹
        = D.orbitFibre hz₀ e₀ (D.deckCycleFun hP hS hz₀ hcard e₀ γ
            * D.deckCycleFun hP hS hz₀ hcard e₀ δ)⁻¹ := by
      rw [← D.monodromyHom_base hP hS hz₀ hcard e₀ (γ * δ), map_mul, Equiv.Perm.mul_apply,
        D.monodromyHom_base hP hS hz₀ hcard e₀ δ,
        D.monodromyHom_orbitFibre_base hP hS hz₀ hcard e₀ γ, mul_inv_rev]
    exact inv_injective (D.injective_orbitFibre hz₀ e₀ hkey))

theorem deckCycle_apply (hP : P.Monic) (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {z₀ : ℂ}
    (hz₀ : z₀ ∉ (S : Set ℂ)) (hcard : Nat.card G = P.natDegree)
    (e₀ : puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))})
    (γ : FundamentalGroup ↥((S : Set ℂ)ᶜ) ⟨z₀, hz₀⟩) :
    D.deckCycle hP hS hz₀ hcard e₀ γ = D.deckCycleFun hP hS hz₀ hcard e₀ γ := rfl

/-- **Every formula is the name of a loop**: the monodromy of a connected cover is transitive on
the fibre, and the formulas are pinned down by where they send the base point. -/
theorem surjective_deckCycle (hP : P.Monic) (hdeg : 0 < P.natDegree) (hirr : Irreducible P)
    (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ))
    (hcard : Nat.card G = P.natDegree)
    (e₀ : puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}) :
    Function.Surjective (D.deckCycle hP hS hz₀ hcard e₀) := by
  haveI := pathConnectedSpace_punctured hP hdeg hirr hS
  intro g
  obtain ⟨γ, hγ⟩ := (isCoveringMap_puncturedProj hP hS).orbitMap_surjective
    (⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ)) e₀ (D.orbitFibre hz₀ e₀ g⁻¹)
  refine ⟨γ, ?_⟩
  rw [deckCycle_apply]
  refine inv_injective (D.injective_orbitFibre hz₀ e₀ ?_)
  rw [← D.monodromyHom_base hP hS hz₀ hcard e₀ γ]
  exact hγ

/-- **A formula that the monodromy of a loop realizes at one point of the fibre is conjugate to
the inverse of the name of that loop.**  The monodromy moves every point of the fibre by right
multiplication with that inverse, so matching it against a formula at one point is a single
equation between two formulas, and the equation says exactly that they are conjugate. -/
theorem deckCycle_conj (hP : P.Monic) (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {z₀ : ℂ}
    (hz₀ : z₀ ∉ (S : Set ℂ)) (hcard : Nat.card G = P.natDegree)
    (e₀ : puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))})
    (γ : FundamentalGroup ↥((S : Set ℂ)ᶜ) ⟨z₀, hz₀⟩) {τ : G}
    {Y : puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}}
    (hY : monodromyHom hP hS hz₀ γ Y = D.orbitFibre hz₀ Y τ) :
    ∃ c : G, D.deckCycle hP hS hz₀ hcard e₀ γ = c⁻¹ * τ⁻¹ * c := by
  obtain ⟨c, rfl⟩ := D.surjective_orbitFibre hP hS hz₀ hcard e₀ Y
  refine ⟨c, ?_⟩
  rw [D.monodromyHom_orbitFibre_base hP hS hz₀ hcard e₀ γ c, D.orbitFibre_orbitFibre] at hY
  have hc := D.injective_orbitFibre hz₀ e₀ hY
  have hg : (D.deckCycleFun hP hS hz₀ hcard e₀ γ)⁻¹ = c⁻¹ * (τ * c) := by
    rw [← hc]; group
  rw [deckCycle_apply, ← inv_inv (D.deckCycleFun hP hS hz₀ hcard e₀ γ), hg]
  group

/-! ### The branch-cycle system of names -/

/-- **A loop with trivial monodromy has trivial name.** -/
theorem deckCycle_eq_one (hP : P.Monic) (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {z₀ : ℂ}
    (hz₀ : z₀ ∉ (S : Set ℂ)) (hcard : Nat.card G = P.natDegree)
    (e₀ : puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))})
    {γ : FundamentalGroup ↥((S : Set ℂ)ᶜ) ⟨z₀, hz₀⟩} (h : monodromyHom hP hS hz₀ γ = 1) :
    D.deckCycle hP hS hz₀ hcard e₀ γ = 1 := by
  have hbase := D.monodromyHom_base hP hS hz₀ hcard e₀ γ
  rw [h, Equiv.Perm.one_apply] at hbase
  have h2 : D.orbitFibre hz₀ e₀ 1
      = D.orbitFibre hz₀ e₀ (D.deckCycleFun hP hS hz₀ hcard e₀ γ)⁻¹ := by
    rw [D.orbitFibre_one]
    exact hbase
  have hone : (1 : G) = (D.deckCycleFun hP hS hz₀ hcard e₀ γ)⁻¹ :=
    D.injective_orbitFibre hz₀ e₀ h2
  rw [deckCycle_apply, ← inv_inv (D.deckCycleFun hP hS hz₀ hcard e₀ γ), ← hone, inv_one]

/-- **A loop whose monodromy fixes one point of the fibre has trivial name.**  The monodromy of a
loop moves every point of the fibre by right multiplication with the inverse of its name, so a
single fixed point already pins the name down. -/
theorem deckCycle_eq_one_of_fixed (hP : P.Monic)
    (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ))
    (hcard : Nat.card G = P.natDegree)
    (e₀ : puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))})
    (γ : FundamentalGroup ↥((S : Set ℂ)ᶜ) ⟨z₀, hz₀⟩)
    {Y : puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}}
    (hY : monodromyHom hP hS hz₀ γ Y = Y) : D.deckCycle hP hS hz₀ hcard e₀ γ = 1 := by
  obtain ⟨c, hc⟩ := D.deckCycle_conj hP hS hz₀ hcard e₀ γ (τ := 1) (Y := Y)
    (by rw [hY, D.orbitFibre_one])
  rw [hc, inv_one, mul_one, inv_mul_cancel]

/-- **A loop around a parameter at which the family stays separable has trivial name.** -/
theorem deckCycle_eq_one_of_isPunctureLoop (hP : P.Monic)
    (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ))
    (hcard : Nat.card G = P.natDegree)
    (e₀ : puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}) {s : ℂ}
    (hsep : (spec P s).Separable) {γ : FundamentalGroup ↥((S : Set ℂ)ᶜ) ⟨z₀, hz₀⟩}
    (hγ : IsPunctureLoop ((S : Set ℂ)ᶜ) s hz₀ γ) : D.deckCycle hP hS hz₀ hcard e₀ γ = 1 :=
  D.deckCycle_eq_one hP hS hz₀ hcard e₀ (monodromyHom_eq_one_of_isPunctureLoop hP hS hz₀ hsep hγ)

/-- **A branch-cycle system of names indexed by the branch points themselves.**  Each entry is the
name of a loop winding around its own branch point, and together the entries generate the group. -/
theorem exists_localizedNames (hP : P.Monic) (hdeg : 0 < P.natDegree) (hirr : Irreducible P)
    (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ))
    (hcard : Nat.card G = P.natDegree)
    (e₀ : puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}) :
    ∃ γ : ℂ → FundamentalGroup ↥((S : Set ℂ)ᶜ) ⟨z₀, hz₀⟩,
      (∀ s ∈ (S : Set ℂ), IsPunctureLoop ((S : Set ℂ)ᶜ) s hz₀ (γ s)) ∧
        Subgroup.closure ((fun s => D.deckCycle hP hS hz₀ hcard e₀ (γ s)) '' (S : Set ℂ)) = ⊤ := by
  obtain ⟨γ, hγ, htop⟩ := exists_punctureLoops_compl S.finite_toSet (z₀ := z₀) hz₀
  refine ⟨γ, hγ, ?_⟩
  rw [show (fun s => D.deckCycle hP hS hz₀ hcard e₀ (γ s)) '' (S : Set ℂ)
      = (D.deckCycle hP hS hz₀ hcard e₀) '' (γ '' (S : Set ℂ)) from (Set.image_image _ _ _).symm]
  exact closure_image_eq_top (D.surjective_deckCycle hP hdeg hirr hS hz₀ hcard e₀) htop

/-- **A branch-cycle system of names indexed by the genuine branch points.**  Only the parameters
at which the family acquires a repeated root are needed. -/
theorem exists_localizedNames_degen (hP : P.Monic) (hdeg : 0 < P.natDegree) (hirr : Irreducible P)
    (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ))
    (hcard : Nat.card G = P.natDegree)
    (e₀ : puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}) :
    ∃ γ : ℂ → FundamentalGroup ↥((S : Set ℂ)ᶜ) ⟨z₀, hz₀⟩,
      (∀ s ∈ degenLocus P, IsPunctureLoop ((S : Set ℂ)ᶜ) s hz₀ (γ s)) ∧
        Subgroup.closure ((fun s => D.deckCycle hP hS hz₀ hcard e₀ (γ s)) '' degenLocus P) = ⊤ := by
  classical
  obtain ⟨γ, hγ, htop⟩ := exists_punctureLoops_compl S.finite_toSet (z₀ := z₀) hz₀
  have hdsub : degenLocus P ⊆ (S : Set ℂ) := degenLocus_subset hS
  set f := D.deckCycle hP hS hz₀ hcard e₀ with hfdef
  have hfull : Subgroup.closure ((fun s => f (γ s)) '' (S : Set ℂ)) = ⊤ := by
    rw [show (fun s => f (γ s)) '' (S : Set ℂ) = f '' (γ '' (S : Set ℂ)) from
      (Set.image_image _ _ _).symm]
    exact closure_image_eq_top (D.surjective_deckCycle hP hdeg hirr hS hz₀ hcard e₀) htop
  refine ⟨γ, fun s hs => hγ s (hdsub hs), ?_⟩
  rw [← hfull]
  refine le_antisymm (Subgroup.closure_mono (Set.image_mono hdsub)) ((Subgroup.closure_le _).2 ?_)
  rintro y ⟨s, hs, rfl⟩
  by_cases hsd : s ∈ degenLocus P
  · exact Subgroup.subset_closure ⟨s, hsd, rfl⟩
  · show f (γ s) ∈ Subgroup.closure _
    rw [show f (γ s) = 1 from D.deckCycle_eq_one_of_isPunctureLoop hP hS hz₀ hcard e₀
      (separable_of_notMem_degenLocus hsd) (hγ s hs)]
    exact one_mem _

end RationalDeck

end Rigidity.RET.Analytic

end

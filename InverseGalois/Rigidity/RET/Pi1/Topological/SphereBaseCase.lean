/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Rigidity.RET.Pi1.Topological.CircleGroup
import InverseGalois.Rigidity.RET.Pi1.Topological.TameMonodromy
import InverseGalois.Rigidity.RET.Presentation
import InverseGalois.Rigidity.RET.Pi1.SphereCompletion
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible

/-!
# Link C, base case: `π₁(ℂˣ) ≅ SphereGroup 2`

The sphere presentation group `Γ_r = ⟨x₀,…,x_{r-1} | ∏ xᵢ = 1⟩` is the algebraic shadow of the
fundamental group of the `r`-punctured sphere.  For `r = 2` the relation `x₀x₁ = 1` collapses the
two generators to a single free generator, so `Γ_2 ≅ ℤ`.  On the analytic side the twice-punctured
sphere `ℙ¹(ℂ) ∖ {0, ∞}` is `ℂˣ`, whose fundamental group we computed to be `ℤ`
(`Complex.fundamentalGroupUnits`).  This file proves both facts and matches them:

* `Rigidity.RET.freeGroupFin1MulEquivInt : FreeGroup (Fin 1) ≃* Multiplicative ℤ`;
* `Rigidity.RET.sphereGroup_two_mulEquiv_int : SphereGroup 2 ≃* Multiplicative ℤ`;
* `Rigidity.RET.pi1_units_mulEquiv_sphereGroup_two : FundamentalGroup ℂˣ _ ≃* SphereGroup 2`.

This is the `r = 2` instance of the Riemann Existence comparison `π₁^top(S² ∖ r pts) ≅ Γ_r` of link
**C** in `GAGA_DREAM.md`: for two branch points the topological and presentation-theoretic
fundamental groups agree, both being the infinite cyclic group.  The general `r` case is settled
in `PuncturedPlane.lean` by the Seifert–van Kampen theorem built in `VanKampen/`.
-/

open scoped Multiplicative

namespace Rigidity.RET

/-- The free group on one generator is infinite cyclic: `FreeGroup (Fin 1) ≃* Multiplicative ℤ`,
sending the generator to `ofAdd 1`.  (This packages the classical `FreeGroup Unit ≃ ℤ` as a group
isomorphism.) -/
noncomputable def freeGroupFin1MulEquivInt : FreeGroup (Fin 1) ≃* Multiplicative ℤ where
  toFun := FreeGroup.lift (fun _ => Multiplicative.ofAdd (1 : ℤ))
  invFun := zpowersHom (FreeGroup (Fin 1)) (FreeGroup.of 0)
  left_inv w := by
    have h : (zpowersHom (FreeGroup (Fin 1)) (FreeGroup.of 0)).comp
        (FreeGroup.lift (fun _ => Multiplicative.ofAdd (1 : ℤ))) = MonoidHom.id _ :=
      FreeGroup.ext_hom _ _ (fun a => by
        fin_cases a
        simp [FreeGroup.lift_apply_of])
    exact DFunLike.congr_fun h w
  right_inv n := by
    have h : (FreeGroup.lift (fun _ => Multiplicative.ofAdd (1 : ℤ))).comp
        (zpowersHom (FreeGroup (Fin 1)) (FreeGroup.of 0)) = MonoidHom.id _ :=
      MonoidHom.ext_mint (by simp [FreeGroup.lift_apply_of])
    exact DFunLike.congr_fun h n
  map_mul' := map_mul _

/-- **`Γ_2 ≅ ℤ`.**  The two-branch-point sphere group is infinite cyclic: the relation `x₀x₁ = 1`
eliminates one generator, leaving a single free generator. -/
noncomputable def sphereGroup_two_mulEquiv_int : SphereGroup 2 ≃* Multiplicative ℤ :=
  (sphereGroup_mulEquiv_free (r := 2) (by norm_num)).some.trans freeGroupFin1MulEquivInt

/-- **Link C, base case `r = 2`.**  The fundamental group of the twice-punctured sphere
`ℙ¹(ℂ) ∖ {0, ∞} = ℂˣ` is isomorphic to the sphere presentation group `Γ_2`.  Both are the infinite
cyclic group; the isomorphism is the `r = 2` instance of the Riemann Existence comparison
`π₁^top(S² ∖ r pts) ≅ Γ_r`. -/
noncomputable def pi1_units_mulEquiv_sphereGroup_two :
    FundamentalGroup ℂˣ Complex.expUnit ≃* SphereGroup 2 :=
  Complex.fundamentalGroupUnits.trans sphereGroup_two_mulEquiv_int.symm

open CategoryTheory ProfiniteGrp ProfiniteGrp.ProfiniteCompletion

/-- **The profinite (étale) side of the base case `r = 2`.**  Applying the profinite-completion
functor to `Γ_2 ≅ ℤ` identifies the algebraic tame fundamental group `sphereCompletion 2` of the
twice-punctured line with the profinite completion of `ℤ`, i.e. `Ẑ`.  This is the `r = 2` instance of
link **D** composed with the base case, the profinite shadow of
`pi1_units_mulEquiv_sphereGroup_two`: the topological `π₁(ℂˣ) ≅ ℤ` completes to `π̂₁ ≅ Ẑ`. -/
noncomputable def sphereCompletion_two_iso_intCompletion :
    sphereCompletion 2 ≅ profiniteCompletion.obj (GrpCat.of (Multiplicative ℤ)) :=
  profiniteCompletion.mapIso
    (MulEquiv.toGrpIso (X := GrpCat.of (SphereGroup 2)) (Y := GrpCat.of (Multiplicative ℤ))
      sphereGroup_two_mulEquiv_int)

/-!
## The degenerate rung `r ≤ 1`

Below the first interesting case `r = 2` sit the two degenerate branch counts, and both close
unconditionally.  The sphere presentation group is *trivial* for `r ∈ {0, 1}`: with no generators
(`r = 0`) there is nothing to present, and with a single generator killed by the relation `x₀ = 1`
(`r = 1`) the group collapses.  These match the topology exactly:

* `r = 0` — the whole sphere `ℙ¹(ℂ) = S²` has no punctures and is simply connected, so `π₁ = 1`;
* `r = 1` — the once-punctured sphere `ℙ¹(ℂ) ∖ {∞}` is the plane `ℂ`, which is contractible, so
  again `π₁ = 1`.

Mathlib has no Riemann sphere, so as with `r = 2` (modelled by `ℂˣ`) we take the *plane* `ℂ` itself
as the model of the once-punctured sphere; its fundamental group is trivial by contractibility
(`Complex.fundamentalGroup_subsingleton`), and the comparison `π₁(ℂ) ≅ Γ_1` (`r = 1`) holds with
both sides the trivial group.
-/

/-- A group isomorphism between any two trivial (subsingleton) groups: everything maps to `1`. -/
def mulEquivOfSubsingleton {A B : Type*} [Group A] [Group B] [Subsingleton A] [Subsingleton B] :
    A ≃* B where
  toFun _ := 1
  invFun _ := 1
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
  map_mul' _ _ := Subsingleton.elim _ _

/-- **`Γ_1` is trivial.**  For a single branch point the relation `x₀ = 1` kills the only generator,
so the sphere group collapses; equivalently `Γ_1 ≅ FreeGroup (Fin 0)` is free of rank `0`. -/
instance sphereGroup_one_subsingleton : Subsingleton (SphereGroup 1) :=
  have : Subsingleton (FreeGroup (Fin (1 - 1))) :=
    inferInstanceAs (Subsingleton (FreeGroup (Fin 0)))
  (sphereGroup_mulEquiv_free (r := 1) le_rfl).some.symm.surjective.subsingleton

/-- **`Γ_0` is trivial.**  With no branch points there are no generators, so the presentation group
is the quotient of the trivial free group `FreeGroup (Fin 0)`. -/
instance sphereGroup_zero_subsingleton : Subsingleton (SphereGroup 0) :=
  (QuotientGroup.mk'_surjective _).subsingleton

/-- **The plane has trivial fundamental group.**  `ℂ` is a real topological vector space, hence
contractible, hence simply connected, so every fundamental group `π₁(ℂ, z)` is trivial.  This is the
topological side of the `r = 1` branch count: the once-punctured sphere is the plane. -/
instance Complex.fundamentalGroup_subsingleton (z : ℂ) : Subsingleton (FundamentalGroup ℂ z) :=
  inferInstanceAs (Subsingleton (Path.Homotopic.Quotient z z))

/-- **Link C, degenerate case `r = 1`.**  The fundamental group of the once-punctured sphere —
modelled by the plane `ℂ` — is isomorphic to the sphere presentation group `Γ_1`.  Both are trivial;
this is the `r = 1` instance of the Riemann Existence comparison `π₁^top(S² ∖ r pts) ≅ Γ_r`. -/
noncomputable def pi1_plane_mulEquiv_sphereGroup_one (z : ℂ) :
    FundamentalGroup ℂ z ≃* SphereGroup 1 :=
  mulEquivOfSubsingleton

/-!
## Base-case realization of cyclic monodromy (`r = 2`)

The comparison `Γ_2 ≅ π₁(ℂˣ)` is only the *statement* of the base case; its *use* in the Riemann
Existence `←` direction is that surjections `Γ_r ↠ G` produce covers with monodromy group `G`.  For
`r = 2` we can realize this concretely: the degree-`n` tame cover `z ↦ zⁿ` of the twice-punctured
sphere has an `n`-point fibre on which `π₁ ≅ Γ_2 ≅ ℤ` acts transitively (`npow_tame_monodromy`), so
`Γ_2` itself acts transitively — the cyclic monodromy group `ℤ/n` is realized as a quotient of the
sphere group `Γ_2`.
-/

/-- **Base-case realization: `Γ_2` acts transitively via tame monodromy.**  Transporting the
degree-`n` tame monodromy across `Γ_2 ≅ ℤ` (`sphereGroup_two_mulEquiv_int`), the sphere presentation
group `Γ_2` acts transitively on the `n`-point fibre of the cover `z ↦ zⁿ`.  This is the `r = 2`,
cyclic-`G` instance of the Riemann Existence `←` direction: a surjection `Γ_2 ↠ ℤ/n` realizes the
cyclic group as the monodromy (deck) group of a degree-`n` tame cover of the twice-punctured
sphere. -/
theorem sphereGroup_two_monodromy_transitive (n : ℕ) [NeZero n] (e₀ : ℂˣ) :
    Function.Surjective (fun γ : SphereGroup 2 =>
      Complex.npowMonodromyInt n e₀ (sphereGroup_two_mulEquiv_int γ) ⟨e₀, rfl⟩) :=
  (Complex.npowMonodromyInt_orbit_surjective n e₀).comp
    sphereGroup_two_mulEquiv_int.surjective

end Rigidity.RET

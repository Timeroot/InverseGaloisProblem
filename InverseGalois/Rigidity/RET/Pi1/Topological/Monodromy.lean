/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The monodromy representation of the fundamental group on a fibre

For a covering map `p : E → X` and a basepoint `x : X`, the fundamental group `π₁(X, x)` acts on
the fibre `p ⁻¹' {x}` by monodromy: a loop is lifted starting at each fibre point, and it sends
that point to the endpoint of the lift.  Mathlib provides the underlying groupoid action
(`IsCoveringMap.monodromy`, `IsCoveringMap.monodromyFunctor`); this file packages the vertex-group
action as a genuine group homomorphism into the permutation group of the fibre,

* `IsCoveringMap.monodromyHom : FundamentalGroup X x →* Equiv.Perm (p ⁻¹' {x})`,

and proves the classification of the fibre by the fundamental group when the total space is simply
connected:

* `IsCoveringMap.orbitMap_bijective` — for a path-connected, simply connected total space the
  orbit map `γ ↦ monodromy γ e₀` is a bijection onto the fibre, packaged as
  `IsCoveringMap.orbitEquiv : FundamentalGroup X x ≃ p ⁻¹' {x}`.

This is the covering-space half of the Riemann Existence comparison (link **C** of
`GAGA_DREAM.md`): the fibre of a covering is a principal homogeneous `π₁`-set, and for the
universal (simply connected) cover it is `π₁` itself.
-/

open CategoryTheory Topology unitInterval

namespace IsCoveringMap

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}
  (cov : IsCoveringMap p)

/-- The monodromy action of the fundamental group `π₁(X, x)` on the fibre `p ⁻¹' {x}`, as a group
homomorphism into the permutation group of the fibre.  A loop `γ` acts by sending each fibre point
`e` to the endpoint of the lift of `γ` that starts at `e`. -/
noncomputable def monodromyHom (x : X) :
    FundamentalGroup X x →* Equiv.Perm (p ⁻¹' {x}) where
  toFun γ := Equiv.ofBijective _ (cov.monodromy_bijective γ.toPath)
  map_one' := by
    refine Equiv.ext fun e => ?_
    show cov.monodromy (FundamentalGroup.toPath 1) e = e
    rw [show (FundamentalGroup.toPath (1 : FundamentalGroup X x))
          = Path.Homotopic.Quotient.refl x from rfl, cov.monodromy_refl]
    rfl
  map_mul' a b := by
    refine Equiv.ext fun e => ?_
    show cov.monodromy (FundamentalGroup.toPath (a * b)) e
        = cov.monodromy a.toPath (cov.monodromy b.toPath e)
    rw [show FundamentalGroup.toPath (a * b) = b.toPath.trans a.toPath from rfl,
      cov.monodromy_trans_apply]

@[simp] theorem monodromyHom_apply (x : X) (γ : FundamentalGroup X x) (e : p ⁻¹' {x}) :
    cov.monodromyHom x γ e = cov.monodromy γ.toPath e := rfl

/-- The orbit map of the monodromy action based at a fibre point `e₀`, sending a loop class to the
endpoint of its lift starting at `e₀`.  This is `monodromyHom` evaluated at `e₀`. -/
noncomputable def orbitMap (x : X) (e₀ : p ⁻¹' {x}) : FundamentalGroup X x → p ⁻¹' {x} :=
  fun γ => cov.monodromy γ.toPath e₀

@[simp] theorem orbitMap_apply (x : X) (e₀ : p ⁻¹' {x}) (γ : FundamentalGroup X x) :
    cov.orbitMap x e₀ γ = cov.monodromy γ.toPath e₀ := rfl

/-- The underlying point of the monodromy action on a *representative* loop is the endpoint of the
lifted path.  This is the computation rule behind the orbit map. -/
theorem monodromy_mk_val {x y : X} (q : Path x y) (e : p ⁻¹' {x}) :
    (cov.monodromy (Path.Homotopic.Quotient.mk q) e : E)
      = cov.liftPath q e.val (q.source.trans e.2.symm) 1 := rfl

/-- **Monodromy commutes with deck transformations.**  If `g : E → E` is a continuous self-map of
the total space lying over the identity (`p (g e) = p e` for all `e`, a "deck transformation"),
then lifting a path after applying `g` to the starting point agrees with applying `g` to the lift:
`monodromy` is `g`-equivariant on fibres.  This is the uniqueness of path lifting in disguise. -/
theorem monodromy_comp_deck {g : E → E} (hg : Continuous g) (hgp : ∀ e, p (g e) = p e)
    {x y : X} (q : Path.Homotopic.Quotient x y) (e : p ⁻¹' {x}) :
    (cov.monodromy q ⟨g e.1, (hgp e.1).trans e.2⟩ : E) = g (cov.monodromy q e) := by
  obtain ⟨Q, rfl⟩ := Path.Homotopic.Quotient.mk_surjective q
  rw [cov.monodromy_mk_val, cov.monodromy_mk_val]
  have hcomp : (⟨g, hg⟩ : C(E, E)).comp (cov.liftPath Q e.1 (Q.source.trans e.2.symm))
      = cov.liftPath Q (g e.1) (Q.source.trans ((hgp e.1).trans e.2).symm) := by
    rw [cov.eq_liftPath_iff']
    refine ⟨?_, ?_⟩
    · ext t
      show p (g (cov.liftPath Q e.1 (Q.source.trans e.2.symm) t)) = Q t
      rw [hgp]
      exact congr_fun (cov.liftPath_lifts Q e.1 (Q.source.trans e.2.symm)) t
    · show g (cov.liftPath Q e.1 (Q.source.trans e.2.symm) 0) = g e.1
      rw [cov.liftPath_zero]
  rw [← hcomp]
  rfl

/-- **Surjectivity of the orbit map.**  When the total space is path connected, every point of the
fibre is hit by monodromy: lift a path joining `e₀` to the target point, and the loop it projects
to sends `e₀` to that point.  The fibre is a single monodromy orbit. -/
theorem orbitMap_surjective [PathConnectedSpace E] (x : X) (e₀ : p ⁻¹' {x}) :
    Function.Surjective (cov.orbitMap x e₀) := by
  intro e₁
  set δ : Path e₀.val e₁.val := PathConnectedSpace.somePath e₀.val e₁.val with hδ
  set q : Path x x := (δ.map cov.continuous).cast e₀.2.symm e₁.2.symm with hq
  refine ⟨FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q), Subtype.ext ?_⟩
  show (cov.monodromy (Path.Homotopic.Quotient.mk q) e₀ : E) = e₁.val
  rw [cov.monodromy_mk_val]
  have hlift : cov.liftPath q e₀.val (q.source.trans e₀.2.symm) = (δ : C(I, E)) := by
    symm
    rw [cov.eq_liftPath_iff']
    refine ⟨?_, δ.source⟩
    ext t
    show p (δ t) = q t
    rw [hq]
    simp only [Path.cast_coe, Path.map_coe, Function.comp_apply]
  rw [hlift]
  exact δ.target

/-- **Injectivity of the orbit map.**  When the total space is simply connected, two loop classes
with the same monodromy endpoint are equal: lift both loops from `e₀`; they share an endpoint, so
the lifts are homotopic rel endpoints (simple connectivity), and pushing that homotopy down by `p`
identifies the two loop classes downstairs. -/
theorem orbitMap_injective [SimplyConnectedSpace E] (x : X) (e₀ : p ⁻¹' {x}) :
    Function.Injective (cov.orbitMap x e₀) := by
  intro a b hab
  suffices h : a.toPath = b.toPath from h
  obtain ⟨α, hα⟩ := Path.Homotopic.Quotient.mk_surjective a.toPath
  obtain ⟨β, hβ⟩ := Path.Homotopic.Quotient.mk_surjective b.toPath
  -- The two lifts of `α`, `β` starting at `e₀`.
  set Lα := cov.liftPath α e₀.val (α.source.trans e₀.2.symm) with hLα
  set Lβ := cov.liftPath β e₀.val (β.source.trans e₀.2.symm) with hLβ
  -- Their common endpoint, forced by the monodromy hypothesis `hab`.
  have hval : Lα 1 = Lβ 1 := by
    have h1 : (cov.monodromy a.toPath e₀ : E) = (cov.monodromy b.toPath e₀ : E) := by
      rw [show cov.monodromy a.toPath e₀ = cov.orbitMap x e₀ a from rfl,
        show cov.monodromy b.toPath e₀ = cov.orbitMap x e₀ b from rfl, hab]
    rw [← hα, ← hβ, cov.monodromy_mk_val, cov.monodromy_mk_val] at h1
    exact h1
  -- The lifts land in the fibre... over `x`.
  have hpL : p (Lα 1) = x := by
    have h := congr_fun (cov.liftPath_lifts α e₀.val (α.source.trans e₀.2.symm)) 1
    rw [Function.comp_apply] at h
    rw [← hLα] at h
    rw [h]; exact α.target
  -- Represent both loops downstairs as the projection of a lifted path from `e₀`; simple
  -- connectivity of `E` makes those two lifted paths homotopic, hence equal after projection.
  set Pα : Path e₀.val (Lα 1) := ⟨Lα, cov.liftPath_zero .., rfl⟩ with hPα
  set Pβ : Path e₀.val (Lα 1) := ⟨Lβ, cov.liftPath_zero .., hval.symm⟩ with hPβ
  have key : ∀ (P : Path e₀.val (Lα 1)) (γ : Path x x),
      (⇑P : I → E) = cov.liftPath γ e₀.val (γ.source.trans e₀.2.symm) →
      ((Path.Homotopic.Quotient.mk P).map ⟨p, cov.continuous⟩).cast e₀.2.symm hpL.symm
        = Path.Homotopic.Quotient.mk γ := by
    intro P γ hP
    rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast]
    congr 1
    ext t
    simp only [Path.cast_coe, Path.map_coe, Function.comp_apply]
    rw [show (P t) = cov.liftPath γ e₀.val (γ.source.trans e₀.2.symm) t from congr_fun hP t]
    exact congr_fun (cov.liftPath_lifts γ e₀.val (γ.source.trans e₀.2.symm)) t
  have Cα := key Pα α (by rw [hPα]; rfl)
  have Cβ := key Pβ β (by rw [hPβ]; rfl)
  rw [← hα, ← hβ]
  calc Path.Homotopic.Quotient.mk α
      = ((Path.Homotopic.Quotient.mk Pα).map ⟨p, cov.continuous⟩).cast e₀.2.symm hpL.symm :=
        Cα.symm
    _ = ((Path.Homotopic.Quotient.mk Pβ).map ⟨p, cov.continuous⟩).cast e₀.2.symm hpL.symm := by
        rw [Subsingleton.elim (Path.Homotopic.Quotient.mk Pα) (Path.Homotopic.Quotient.mk Pβ)]
    _ = Path.Homotopic.Quotient.mk β := Cβ

/-- **Classification of the fibre by the fundamental group.**  For a covering map with path
connected, simply connected total space, the monodromy orbit map based at any fibre point is a
bijection `π₁(X, x) ≃ p ⁻¹' {x}`.  This is the covering-space input to the Riemann Existence
comparison (link **C**): the fibre of the universal cover is a `π₁`-torsor. -/
noncomputable def orbitEquiv [SimplyConnectedSpace E] (x : X) (e₀ : p ⁻¹' {x}) :
    FundamentalGroup X x ≃ p ⁻¹' {x} :=
  Equiv.ofBijective (cov.orbitMap x e₀)
    ⟨cov.orbitMap_injective x e₀, cov.orbitMap_surjective x e₀⟩

@[simp] theorem orbitEquiv_apply [SimplyConnectedSpace E] (x : X) (e₀ : p ⁻¹' {x})
    (γ : FundamentalGroup X x) :
    cov.orbitEquiv x e₀ γ = cov.monodromy γ.toPath e₀ := rfl

end IsCoveringMap

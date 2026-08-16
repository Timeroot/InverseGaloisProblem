/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Pi1.Topological.CoverDeck

/-!
# Lifting paths to the cover attached to a monodromy homomorphism

A path of the region lifts to the cover of `RET/Pi1/Topological/CoverTopology.lean`, and the lift
is written down explicitly: over the point `γ t` of the path put the label of `γ 1` transported
along the part of `γ` that is still to come.  At the end of the path the transport is along the
constant path, so the lift ends at the prescribed point of the fibre; at the start it is along the
whole of `γ`, so the lift starts at the transport of that point.

The lift is continuous because a short piece of a path stays inside a flat piece of the region, and
inside a flat piece transport is along straight segments — so the lift stays in one sheet, where
the total space is a product.  The label transported along the whole of a short piece is the label
transported along the rest and then along the segment, which is precisely the statement that the
subpaths of a path concatenate.

Two consequences: the fibres of the cover over the points of a path are joined inside the total
space, and the fibre over the base point is joined to itself by the lifts of the loops, moving a
label by the monodromy.  When the monodromy homomorphism is surjective and every point of the
region can be joined to the base point, the two together make the total space path-connected: the
cover is connected, which is what makes it the Galois cover of the group.

## Main definitions

* `Rigidity.RET.toPath` — a continuous map from the unit interval read as a path.
* `Rigidity.RET.subClass` — the homotopy class of the part of a path still to come.
* `Rigidity.RET.MonodromyData.lift` — the lift of a path to the cover.

## Main results

* `Rigidity.RET.MonodromyData.continuous_lift` — the lift is continuous.
* `Rigidity.RET.MonodromyData.joined_restrict` — transport along a path joins the total space.
* `Rigidity.RET.MonodromyData.pathConnectedSpace_total` — the cover of a surjective monodromy
  homomorphism is path-connected.
-/

open scoped unitInterval

noncomputable section

namespace Rigidity.RET

/-! ### Paths, their subpaths, and short pieces of them -/

/-- A continuous map from the unit interval, read as a path between its own endpoints. -/
def toPath {Y : Type*} [TopologicalSpace Y] (γ : C(I, Y)) : Path (γ 0) (γ 1) := ⟨γ, rfl, rfl⟩

@[simp] theorem coe_toPath {Y : Type*} [TopologicalSpace Y] (γ : C(I, Y)) :
    ⇑(toPath γ) = γ := rfl

/-- The whole of a path is a subpath of it. -/
theorem subpath_zero_one {Y : Type*} [TopologicalSpace Y] (γ : C(I, Y)) :
    (toPath γ).subpath 0 1 = toPath γ := by
  ext t
  show γ (Path.subpathAux 0 1 t) = γ t
  congr 1
  exact Subtype.ext (by simp)

/-- **The homotopy class of the part of a path still to come.** -/
def subClass {Y : Type*} [TopologicalSpace Y] (γ : C(I, Y)) (t : I) :
    Path.Homotopic.Quotient (γ t) (γ 1) :=
  Path.Homotopic.Quotient.mk ((toPath γ).subpath t 1)

theorem subClass_def {Y : Type*} [TopologicalSpace Y] (γ : C(I, Y)) (t : I) :
    subClass γ t = Path.Homotopic.Quotient.mk ((toPath γ).subpath t 1) := rfl

theorem subClass_zero {Y : Type*} [TopologicalSpace Y] (γ : C(I, Y)) :
    subClass γ 0 = Path.Homotopic.Quotient.mk (toPath γ) := by
  show Path.Homotopic.Quotient.mk ((toPath γ).subpath 0 1) = _
  rw [subpath_zero_one]

theorem subClass_one {Y : Type*} [TopologicalSpace Y] (γ : C(I, Y)) :
    subClass γ 1 = Path.Homotopic.Quotient.refl (γ 1) := by
  show Path.Homotopic.Quotient.mk ((toPath γ).subpath 1 1) = _
  rw [Path.subpath_self, Path.Homotopic.Quotient.mk_refl]
  rfl

/-- **A subpath joining two nearby parameters stays close to them.** -/
theorem mem_ball_of_mem_uIcc {ε : ℝ} {t₀ t u : I} (hu : u ∈ Set.uIcc t t₀)
    (ht : t ∈ Metric.ball t₀ ε) : u ∈ Metric.ball t₀ ε := by
  rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, abs_lt] at ht ⊢
  rcases Set.mem_uIcc.mp hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h1' : (t : ℝ) ≤ (u : ℝ) := h1
    have h2' : (u : ℝ) ≤ (t₀ : ℝ) := h2
    constructor <;> linarith [ht.1, ht.2]
  · have h1' : (t₀ : ℝ) ≤ (u : ℝ) := h1
    have h2' : (u : ℝ) ≤ (t : ℝ) := h2
    constructor <;> linarith [ht.1, ht.2]

/-- The parameters of a subpath lie between its endpoints. -/
theorem subpathAux_mem_uIcc (t₀ t₁ u : I) : Path.subpathAux t₀ t₁ u ∈ Set.uIcc t₀ t₁ := by
  have hu : Path.subpathAux t₀ t₁ u ∈ Set.range (Path.subpathAux t₀ t₁) := ⟨u, rfl⟩
  rwa [Path.range_subpathAux] at hu

namespace MonodromyData

variable {X : Set ℂ} {x₀ : ↥X} {H : Type*} [Group H] (D : MonodromyData x₀ H)

/-! ### A criterion for continuity into the total space -/

/-- **A map into the total space that stays in one sheet is continuous** as soon as its composition
with the projection is: inside a sheet the total space is the graph of a transport. -/
theorem continuousOn_of_mapsTo_sheet {Z : Type*} [TopologicalSpace Z] {f : Z → D.Total} {U : Set Z}
    {K : Set ℂ} (hK : IsFlat X K) {x : ↥X} (hx : (x : ℂ) ∈ K) (s : D.Fib x)
    (hmaps : ∀ z ∈ U, f z ∈ D.sheet hK hx s)
    (hcont : ContinuousOn (fun z => D.proj (f z)) U) : ContinuousOn f U := by
  rw [continuousOn_iff_continuous_restrict] at hcont ⊢
  have hmem : ∀ z : ↥U, ((D.proj (f z) : ↥X) : ℂ) ∈ K := fun z => (hmaps z z.2).choose
  have hfeq : U.restrict f = fun z : ↥U => D.flatSection hK hx ⟨D.proj (f z), hmem z⟩ s := by
    funext z
    show f z = (⟨D.proj (f z), D.restrict (segClass hK (hmem z) hx) s⟩ : D.Total)
    refine Sigma.ext rfl ?_
    exact heq_of_eq (D.snd_eq_of_mem_sheet hK hx s (hmaps z z.2) (hmem z))
  rw [hfeq]
  exact (D.continuous_flatSection hK hx).comp
    ((hcont.subtype_mk hmem).prodMk continuous_const)

/-! ### The lift of a path -/

variable (γ : C(I, ↥X))

/-- **The lift of a path to the cover**, starting from a prescribed label at its endpoint: over
`γ t` put the label at `γ 1` transported along the part of the path still to come. -/
def lift (e : D.Fib (γ 1)) (t : I) : D.Total := ⟨γ t, D.restrict (subClass γ t) e⟩

@[simp] theorem proj_lift (e : D.Fib (γ 1)) (t : I) : D.proj (D.lift γ e t) = γ t := rfl

theorem lift_one (e : D.Fib (γ 1)) : D.lift γ e 1 = ⟨γ 1, e⟩ := by
  show (⟨γ 1, D.restrict (subClass γ 1) e⟩ : D.Total) = ⟨γ 1, e⟩
  rw [subClass_one, D.restrict_refl]

theorem lift_zero (e : D.Fib (γ 1)) :
    D.lift γ e 0 = ⟨γ 0, D.restrict (Path.Homotopic.Quotient.mk (toPath γ)) e⟩ := by
  show (⟨γ 0, D.restrict (subClass γ 0) e⟩ : D.Total) = _
  rw [subClass_zero]

/-- **The lift of a path is continuous.**  A short piece of the path stays inside a flat piece of
the region, and there the lift stays in one sheet, because the transport along the piece that is
still to come is the transport along a straight segment followed by the transport along the rest. -/
theorem continuous_lift (e : D.Fib (γ 1)) : Continuous (D.lift γ e) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  obtain ⟨K, hK, hK0⟩ := exists_isFlat_mem D.isOpen_region (γ t₀).2
  have hVopen : IsOpen ((fun t : I => ((γ t : ↥X) : ℂ)) ⁻¹' K) :=
    hK.isOpen.preimage (continuous_subtype_val.comp γ.continuous)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hVopen t₀ hK0
  refine ContinuousOn.continuousAt ?_
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε))
  refine D.continuousOn_of_mapsTo_sheet hK hK0 (D.restrict (subClass γ t₀) e) ?_
    (Continuous.continuousOn (by simpa using γ.continuous))
  intro t ht
  have hK1 : ((γ t : ↥X) : ℂ) ∈ K := hball ht
  refine ⟨hK1, ?_⟩
  -- the piece of the path between `t` and `t₀` runs inside the flat piece
  have hpiece : ∀ u : I, (((toPath γ).subpath t t₀) u : ℂ) ∈ K := by
    intro u
    exact hball (mem_ball_of_mem_uIcc (subpathAux_mem_uIcc t t₀ u) ht)
  have hseg : Path.Homotopic.Quotient.mk ((toPath γ).subpath t t₀) = segClass hK hK1 hK0 :=
    eq_segClass_of_mem hK hK1 hK0 _ hpiece
  have hcat : Path.Homotopic.Quotient.mk
      (((toPath γ).subpath t t₀).trans ((toPath γ).subpath t₀ 1))
      = Path.Homotopic.Quotient.mk ((toPath γ).subpath t 1) :=
    Path.Homotopic.Quotient.eq.mpr ⟨Path.Homotopy.subpathTransSubpath (toPath γ) t t₀ 1⟩
  show D.restrict (subClass γ t) e
    = D.restrict (segClass hK hK1 hK0) (D.restrict (subClass γ t₀) e)
  rw [D.restrict_restrict, ← hseg]
  simp only [subClass_def]
  rw [← Path.Homotopic.Quotient.mk_trans, hcat]

/-! ### The fibres over a path are joined -/

/-- **Transport along a path joins the total space**: a label and its transport along a path lie in
the same path component of the cover. -/
theorem joined_restrict_continuousMap (e : D.Fib (γ 1)) :
    Joined (X := D.Total) ⟨γ 0, D.restrict (Path.Homotopic.Quotient.mk (toPath γ)) e⟩ ⟨γ 1, e⟩ :=
  ⟨{  toFun := D.lift γ e
      continuous_toFun := D.continuous_lift γ e
      source' := D.lift_zero γ e
      target' := D.lift_one γ e }⟩

variable {γ}

/-- **Transport along a path joins the total space.** -/
theorem joined_restrict_path {a b : ↥X} (p : Path a b) (e : D.Fib b) :
    Joined (X := D.Total) ⟨a, D.restrict (Path.Homotopic.Quotient.mk p) e⟩ ⟨b, e⟩ := by
  obtain ⟨q, hsrc, htgt⟩ := p
  subst hsrc
  subst htgt
  exact D.joined_restrict_continuousMap q e

/-- **Transport along a homotopy class joins the total space.** -/
theorem joined_restrict {a b : ↥X} (c : Path.Homotopic.Quotient a b) (e : D.Fib b) :
    Joined (X := D.Total) ⟨a, D.restrict c e⟩ ⟨b, e⟩ := by
  induction c using Quotient.inductionOn with
  | h p => exact D.joined_restrict_path p e

/-! ### The cover of a surjective monodromy homomorphism is connected -/

/-- The value at the constant path of a label transported along a loop. -/
theorem restrict_apply_refl (g : Path.Homotopic.Quotient x₀ x₀) (s : D.Fib x₀) :
    (D.restrict g s).1 (Path.Homotopic.Quotient.refl x₀)
      = D.toFun g * s.1 (Path.Homotopic.Quotient.refl x₀) := by
  rw [D.restrict_apply, Path.Homotopic.Quotient.refl_trans]
  conv_lhs => rw [← Path.Homotopic.Quotient.trans_refl g]
  exact s.2 g (Path.Homotopic.Quotient.refl x₀)

/-- **Two labels over the base point are joined in the cover** when the monodromy is surjective:
some loop carries one to the other. -/
theorem joined_of_surjective (hφ : Function.Surjective D.toFun) (s t : D.Fib x₀) :
    Joined (X := D.Total) ⟨x₀, s⟩ ⟨x₀, t⟩ := by
  set r : Path.Homotopic.Quotient x₀ x₀ := Path.Homotopic.Quotient.refl x₀ with hr
  obtain ⟨g, hg⟩ := hφ (s.1 r * (t.1 r)⁻¹)
  have hgt : D.restrict g t = s := by
    refine Fib.eq_of_apply_eq D r ?_
    rw [D.restrict_apply, hr, Path.Homotopic.Quotient.refl_trans]
    conv_lhs => rw [← Path.Homotopic.Quotient.trans_refl g]
    rw [t.2 g (Path.Homotopic.Quotient.refl x₀), hg, ← hr, inv_mul_cancel_right]
  have := D.joined_restrict g t
  rwa [hgt] at this

/-- **The cover attached to a surjective monodromy homomorphism is path-connected**, provided the
base point can be joined to every point of the region. -/
theorem pathConnectedSpace_total (hX : ∀ x : ↥X, Nonempty (Path.Homotopic.Quotient x₀ x))
    (hφ : Function.Surjective D.toFun) : PathConnectedSpace D.Total := by
  have hne : Nonempty D.Total :=
    ⟨⟨x₀, Fib.of D (Path.Homotopic.Quotient.refl x₀) 1⟩⟩
  refine ⟨hne, fun y z => ?_⟩
  obtain ⟨a, s⟩ := y
  obtain ⟨b, t⟩ := z
  obtain ⟨qa⟩ := hX a
  obtain ⟨qb⟩ := hX b
  have h1 : Joined (X := D.Total) ⟨x₀, D.restrict qa s⟩ ⟨a, s⟩ := D.joined_restrict qa s
  have h2 : Joined (X := D.Total) ⟨x₀, D.restrict qb t⟩ ⟨b, t⟩ := D.joined_restrict qb t
  exact (h1.symm.trans (D.joined_of_surjective hφ _ _)).trans h2

/-- The base point can be joined to every point of a path-connected region. -/
theorem nonempty_quotient_of_pathConnected [PathConnectedSpace ↥X] (x : ↥X) :
    Nonempty (Path.Homotopic.Quotient x₀ x) := by
  obtain ⟨p⟩ := PathConnectedSpace.joined x₀ x
  exact ⟨Path.Homotopic.Quotient.mk p⟩

end MonodromyData

end Rigidity.RET

end

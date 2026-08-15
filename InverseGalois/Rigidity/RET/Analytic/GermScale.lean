/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Rigidity.RET.Analytic.GermLift

/-!
# Scaling the Kummer coordinate, and the invariance of the germ place

The Kummer coordinate `u` with `T = s + u ^ d` is only defined up to a `d`-th root of unity: the
substitution `u ↦ c u` with `c ^ d = 1` leaves the parameter `T` untouched.  Such a scaling is an
automorphism of the field of meromorphic germs at the origin, it fixes the image of the Kummer
substitution pointwise, and — being a change of coordinate with nonvanishing derivative — it leaves
the order of vanishing of every germ unchanged.

That last property is what the place construction needs.  The place cut out by a germ consists of
the elements of the integral model whose germ vanishes, so it only sees orders; an automorphism of
the integral model which changes the germ by a scaling of the coordinate therefore fixes the place.
This is the inertia half of the germ construction, and it is where the local monodromy enters: the
monodromy of the small loop at `s` rotates the Kummer coordinate.

## Main definitions

* `Rigidity.RET.Analytic.scaleFun` — the scaling `u ↦ c u` of the coordinate.
* `Rigidity.RET.Analytic.scaleGerm` — the induced endomorphism of the field of germs.

## Main results

* `Rigidity.RET.Analytic.ord_scaleGerm` — scaling does not change the order of vanishing.
* `Rigidity.RET.Analytic.scaleGerm_one`, `Rigidity.RET.Analytic.scaleGerm_scaleGerm` — the
  scalings compose, and the trivial one is the identity.
* `Rigidity.RET.Analytic.scaleGerm_kummerRatHom` — scaling by a `d`-th root of unity fixes the
  Kummer substitution.
* `Rigidity.RET.Analytic.germPlace_comap_eq_self_of_scale` — an automorphism acting on the germ by
  a scaling of the coordinate fixes the place cut out by the germ.
-/

open Filter Topology Polynomial

noncomputable section

namespace Rigidity.RET.Analytic

open MeroGerm

/-- Scaling the Kummer coordinate: `u ↦ c * u`. -/
def scaleFun (c : ℂ) : ℂ → ℂ := fun u => c * u

@[simp] theorem scaleFun_apply (c u : ℂ) : scaleFun c u = c * u := rfl

@[simp] theorem scaleFun_zero (c : ℂ) : scaleFun c 0 = 0 := by simp [scaleFun]

theorem analyticAt_scaleFun (c : ℂ) : AnalyticAt ℂ (scaleFun c) 0 :=
  analyticAt_const.mul analyticAt_id

@[simp] theorem deriv_scaleFun (c : ℂ) : deriv (scaleFun c) 0 = c := by
  have h : HasDerivAt (scaleFun c) (c * 1) 0 := (hasDerivAt_id (0 : ℂ)).const_mul c
  simpa using h.deriv

theorem tendsto_scaleFun {c : ℂ} (hc : c ≠ 0) :
    Tendsto (scaleFun c) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h : ContinuousAt (scaleFun c) 0 := (analyticAt_scaleFun c).continuousAt
    rw [ContinuousAt, scaleFun_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with u hu
    exact mul_ne_zero hc (by simpa using hu)

/-- Scaling the coordinate, on germs at the punctured origin. -/
def scalePunct {c : ℂ} (hc : c ≠ 0) : PunctGerm (0 : ℂ) →+* PunctGerm (0 : ℂ) where
  toFun g := g.compTendsto (scaleFun c) (tendsto_scaleFun hc)
  map_one' := rfl
  map_zero' := rfl
  map_mul' x y := by
    induction x using Filter.Germ.inductionOn with
    | _ f =>
      induction y using Filter.Germ.inductionOn with
      | _ g => rfl
  map_add' x y := by
    induction x using Filter.Germ.inductionOn with
    | _ f =>
      induction y using Filter.Germ.inductionOn with
      | _ g => rfl

@[simp] theorem scalePunct_coe {c : ℂ} (hc : c ≠ 0) (f : ℂ → ℂ) :
    scalePunct hc (f : PunctGerm (0 : ℂ)) = ((f ∘ scaleFun c : ℂ → ℂ) : PunctGerm (0 : ℂ)) :=
  rfl

theorem meromorphicAt_comp_scaleFun {c : ℂ} {f : ℂ → ℂ} (hf : MeromorphicAt f 0) :
    MeromorphicAt (f ∘ scaleFun c) 0 :=
  (show MeromorphicAt f (scaleFun c 0) by rwa [scaleFun_zero]).comp_analyticAt
    (analyticAt_scaleFun c)

theorem scalePunct_mem {c : ℂ} (hc : c ≠ 0) {a : PunctGerm (0 : ℂ)} (ha : a ∈ meroGerms 0) :
    scalePunct hc a ∈ meroGerms 0 := by
  obtain ⟨f, hf, rfl⟩ := ha
  exact ⟨f ∘ scaleFun c, meromorphicAt_comp_scaleFun hf, (scalePunct_coe hc f).symm⟩

/-- **Scaling the Kummer coordinate, as an automorphism of the germ field.** -/
def scaleGerm {c : ℂ} (hc : c ≠ 0) : MeroGerm (0 : ℂ) →+* MeroGerm (0 : ℂ) :=
  RingHom.codRestrict ((scalePunct hc).comp (meroGerms (0 : ℂ)).subtype) (meroGerms 0)
    fun a => scalePunct_mem hc a.2

@[simp] theorem scaleGerm_of {c : ℂ} (hc : c ≠ 0) {f : ℂ → ℂ} (hf : MeromorphicAt f 0) :
    scaleGerm hc (of hf) = of (meromorphicAt_comp_scaleFun (c := c) hf) :=
  Subtype.ext (scalePunct_coe hc f)

/-- **Scaling the coordinate does not change the order of vanishing.** -/
@[simp] theorem ord_scaleGerm {c : ℂ} (hc : c ≠ 0) (a : MeroGerm (0 : ℂ)) :
    ord (scaleGerm hc a) = ord a := by
  obtain ⟨f, hf, rfl⟩ := exists_of a
  rw [scaleGerm_of, ord_of, ord_of]
  have h := meromorphicOrderAt_comp_of_deriv_ne_zero (f := f) (g := scaleFun c)
    (x := (0 : ℂ)) (analyticAt_scaleFun c) (by rwa [deriv_scaleFun])
  rw [h, scaleFun_zero]

theorem scaleGerm_eq_zero_iff {c : ℂ} (hc : c ≠ 0) {a : MeroGerm (0 : ℂ)} :
    scaleGerm hc a = 0 ↔ a = 0 := by
  rw [← ord_eq_top_iff, ← ord_eq_top_iff, ord_scaleGerm]

theorem scaleGerm_congr {c c' : ℂ} (hc : c ≠ 0) (hc' : c' ≠ 0) (h : c = c')
    (a : MeroGerm (0 : ℂ)) : scaleGerm hc a = scaleGerm hc' a := by
  subst h; rfl

/-- The trivial scaling is the identity. -/
@[simp] theorem scaleGerm_one (a : MeroGerm (0 : ℂ)) :
    scaleGerm (one_ne_zero : (1 : ℂ) ≠ 0) a = a := by
  obtain ⟨f, hf, rfl⟩ := exists_of a
  rw [scaleGerm_of]
  refine of_congr _ _ ?_
  filter_upwards with u
  simp [scaleFun]

/-- Scalings compose: the scalings of the coordinate form a group. -/
theorem scaleGerm_scaleGerm {c c' : ℂ} (hc : c ≠ 0) (hc' : c' ≠ 0) (a : MeroGerm (0 : ℂ)) :
    scaleGerm hc (scaleGerm hc' a) = scaleGerm (mul_ne_zero hc' hc) a := by
  obtain ⟨f, hf, rfl⟩ := exists_of a
  rw [scaleGerm_of, scaleGerm_of, scaleGerm_of]
  refine of_congr _ _ ?_
  filter_upwards with u
  show f (c' * (c * u)) = f (c' * c * u)
  rw [mul_assoc]

/-! ### Scaling by a root of unity fixes the Kummer substitution -/

theorem scaleGerm_kummerHom {c : ℂ} (hc : c ≠ 0) {d : ℕ} (hcd : c ^ d = 1) (s : ℂ)
    (p : Polynomial ℂ) : scaleGerm hc (kummerHom s d p) = kummerHom s d p := by
  rw [kummerHom_apply, scaleGerm_of]
  refine of_congr _ _ ?_
  filter_upwards with u
  show (aeval (R := ℂ) (kummerFun s d) p : ℂ → ℂ) (scaleFun c u)
    = (aeval (R := ℂ) (kummerFun s d) p : ℂ → ℂ) u
  rw [kummerHom_eval, kummerHom_eval, scaleFun_apply, mul_pow, hcd, one_mul]

theorem scaleGerm_kummerRatHom {c : ℂ} (hc : c ≠ 0) {d : ℕ} (hd : d ≠ 0) (hcd : c ^ d = 1) (s : ℂ)
    (x : RatFunc ℂ) : scaleGerm hc (kummerRatHom s hd x) = kummerRatHom s hd x := by
  induction x using RatFunc.induction_on with
  | _ p q hq =>
    rw [map_div₀, map_div₀, kummerRatHom_algebraMap, kummerRatHom_algebraMap,
      scaleGerm_kummerHom hc hcd, scaleGerm_kummerHom hc hcd]

/-! ### The place is unchanged by a scaling of the coordinate -/

section Place

variable {B : Type*} [CommRing B] [Algebra (Polynomial ℂ) B] {s : ℂ} {d : ℕ}
  {Ψ : B →+* MeroGerm (0 : ℂ)}

/-- A ring endomorphism of the integral model preserving the orders of the germs preserves the
place cut out by the germ. -/
theorem germPlace_comap_eq_self
    (hΨ : ∀ p, Ψ (algebraMap (Polynomial ℂ) B p) = kummerHom s d p)
    (hint : ∀ b : B, IsIntegral (Polynomial ℂ) b) (σ : B →+* B)
    (hσ : ∀ b, ord (Ψ (σ b)) = ord (Ψ b)) :
    Ideal.comap σ (germPlace hΨ hint) = germPlace hΨ hint := by
  ext b
  rw [Ideal.mem_comap, mem_germPlace, mem_germPlace, hσ]

omit [Algebra (Polynomial ℂ) B] in
theorem ord_apply_eq_of_comp_eq_scale {c : ℂ} (hc : c ≠ 0) (σ : B →+* B)
    (h : Ψ.comp σ = (scaleGerm hc).comp Ψ) (b : B) : ord (Ψ (σ b)) = ord (Ψ b) := by
  have hb := RingHom.congr_fun h b
  rw [show Ψ (σ b) = (Ψ.comp σ) b from rfl, hb]
  exact ord_scaleGerm hc (Ψ b)

/-- **An automorphism acting on the germ by a scaling of the coordinate fixes the place.**  This is
the inertia half of the germ construction: the place cut out by an analytic branch is stable under
every automorphism that merely rotates the Kummer coordinate. -/
theorem germPlace_comap_eq_self_of_scale {c : ℂ} (hc : c ≠ 0)
    (hΨ : ∀ p, Ψ (algebraMap (Polynomial ℂ) B p) = kummerHom s d p)
    (hint : ∀ b : B, IsIntegral (Polynomial ℂ) b) (σ : B →+* B)
    (h : Ψ.comp σ = (scaleGerm hc).comp Ψ) :
    Ideal.comap σ (germPlace hΨ hint) = germPlace hΨ hint :=
  germPlace_comap_eq_self hΨ hint σ (ord_apply_eq_of_comp_eq_scale hc σ h)

end Place

end Rigidity.RET.Analytic

end

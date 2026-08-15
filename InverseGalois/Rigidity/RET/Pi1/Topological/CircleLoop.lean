/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Pi1.Topological.PunctureLocal

/-!
# The circle loop generates the fundamental group

The fundamental group of a punctured disc is infinite cyclic, and a generator can be produced
abstractly from that fact alone.  For the comparison of an analytic branch with the algebra of a
cover one needs more: an *explicit* generator, given by a formula, so that lifting it through a
covering map is a computation rather than an appeal to an isomorphism.

The explicit generator is of course the circle: the loop `t ↦ e ^ (2πit) · c` through a nonzero
point `c` of the plane, and its image `t ↦ s + e ^ (2πit) · (b - s)` in a punctured disc about `s`.
That the first one generates is read off the exponential covering `ℂ → ℂ ∖ {0}`: the loop lifts to
the straight segment from a logarithm of `c` to that logarithm plus `2πi`, so the deck
transformation it names is translation by `2πi`, which generates the deck group by construction.
The second follows from the first, because the radial stretch carrying a punctured disc onto the
punctured plane is a homeomorphism and carries one circle to the other on the nose.

## Main definitions

* `Rigidity.RET.circleLoop` — the loop of the punctured plane running once around the origin
  through a given point.
* `Rigidity.RET.discLoop` — the loop of a punctured disc running once around the centre through a
  given point.

## Main results

* `Rigidity.RET.zpowers_circleLoop_eq_top` — the circle loop generates the fundamental group of the
  punctured plane.
* `Rigidity.RET.zpowers_discLoop_eq_top` — the circle loop of a punctured disc generates its
  fundamental group.
-/

open Topology unitInterval

noncomputable section

namespace Rigidity.RET

/-! ### Two explicit paths -/

/-- The loop of the punctured plane running once around the origin through a nonzero point. -/
def circleLoop (c : {z : ℂ // z ≠ 0}) : Path c c where
  toFun t :=
    ⟨Complex.exp (((t : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * (c : ℂ),
      mul_ne_zero (Complex.exp_ne_zero _) c.2⟩
  continuous_toFun := by fun_prop
  source' := by
    refine Subtype.ext ?_
    simp
  target' := by
    refine Subtype.ext ?_
    simp [Complex.exp_two_pi_mul_I]

@[simp] theorem coe_circleLoop (c : {z : ℂ // z ≠ 0}) (t : I) :
    ((circleLoop c t : {z : ℂ // z ≠ 0}) : ℂ)
      = Complex.exp (((t : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * (c : ℂ) := rfl

/-- The straight segment of the plane from a point to that point translated by `2πi`; it is the
lift of the circle loop through the exponential covering. -/
def logSegment (a : ℂ) : Path a (a + 2 * (Real.pi : ℂ) * Complex.I) where
  toFun t := a + ((t : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by
    simp only [Set.Icc.coe_one, Complex.ofReal_one, one_mul]

/-! ### The circle loop generates -/

/-- An element of the group of multiples of a complex number that is that number itself generates
the group of its multiples. -/
theorem zpowers_ofAdd_eq_top_of_coe_eq {a : ℂ} (g : AddSubgroup.zmultiples a) (hg : (g : ℂ) = a) :
    Subgroup.zpowers (Multiplicative.ofAdd g) = ⊤ := by
  refine eq_top_iff.mpr fun y _ => ?_
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp (Multiplicative.toAdd y).2
  refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
  refine (Multiplicative.toAdd (α := AddSubgroup.zmultiples a)).injective ?_
  refine Subtype.ext ?_
  rw [show Multiplicative.toAdd (Multiplicative.ofAdd g ^ n) = n • g from rfl,
    AddSubgroup.coe_zsmul, hg, hn]

/-- **The circle loop generates the fundamental group of the punctured plane.**  The exponential is
a covering of the punctured plane by the plane, with deck group the translations by the multiples of
`2πi`; the circle loop lifts to the straight segment from a logarithm of the basepoint to that
logarithm plus `2πi`, so it names the translation by `2πi`, a generator of the deck group. -/
theorem zpowers_circleLoop_eq_top (c : {z : ℂ // z ≠ 0}) :
    Subgroup.zpowers
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (circleLoop c))) = ⊤ := by
  obtain ⟨c, hc⟩ := c
  obtain ⟨a, rfl⟩ : ∃ a : ℂ, Complex.exp a = c := ⟨Complex.log c, Complex.exp_log hc⟩
  set p : ℂ → {z : ℂ // z ≠ 0} := fun z => ⟨Complex.exp z, z.exp_ne_zero⟩ with hp
  set cov : IsCoveringMap p := Complex.isCoveringMap_exp with hcov
  set hq := Complex.isAddQuotientCoveringMap_exp.toMultiplicative with hqdef
  set γ : FundamentalGroup {z : ℂ // z ≠ 0} (p a) :=
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (circleLoop (p a))) with hγ
  -- the lift of the circle loop from `a` is the straight segment
  have hsrc : (circleLoop (p a)) 0 = p a := Path.source _
  have hlift : cov.liftPath (circleLoop (p a)) a (hsrc.trans rfl) = (logSegment a : C(I, ℂ)) := by
    symm
    rw [cov.eq_liftPath_iff']
    refine ⟨funext fun t => ?_, ?_⟩
    · refine Subtype.ext ?_
      show Complex.exp (a + ((t : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
        = Complex.exp (((t : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * Complex.exp a
      rw [Complex.exp_add, mul_comm]
    · show a + ((((0 : I) : ℝ)) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) = a
      simp
  -- so its monodromy translates the basepoint by `2πi`
  have hmono : (cov.monodromy (Path.Homotopic.Quotient.mk (circleLoop (p a)))
      ⟨a, rfl⟩ : ℂ) = a + 2 * (Real.pi : ℂ) * Complex.I := by
    rw [cov.monodromy_mk_val, hlift]
    exact (logSegment a).target
  -- hence the deck transformation it names is translation by `2πi`
  have hdeck : ((Multiplicative.toAdd (hq.deckMap a γ) : AddSubgroup.zmultiples
      (2 * (Real.pi : ℂ) * Complex.I)) : ℂ) = 2 * (Real.pi : ℂ) * Complex.I := by
    have h := hq.deckMap_smul a γ
    rw [show ((hq.deckMap a γ) • a : ℂ)
        = ((Multiplicative.toAdd (hq.deckMap a γ) : AddSubgroup.zmultiples
            (2 * (Real.pi : ℂ) * Complex.I)) : ℂ) + a from rfl] at h
    rw [show γ.toPath = Path.Homotopic.Quotient.mk (circleLoop (p a)) from rfl] at h
    rw [hmono] at h
    have := h.trans (by ring : a + 2 * (Real.pi : ℂ) * Complex.I
      = 2 * (Real.pi : ℂ) * Complex.I + a)
    exact add_right_cancel this
  -- a generator of the deck group is a generator of the fundamental group
  have hgen : Subgroup.zpowers (hq.fundamentalGroupMulEquiv a γ) = ⊤ := by
    rw [IsQuotientCoveringMap.fundamentalGroupMulEquiv_apply, Subgroup.zpowers_inv]
    exact zpowers_ofAdd_eq_top_of_coe_eq _ hdeck
  have := zpowers_mulEquiv_eq_top (hq.fundamentalGroupMulEquiv a).symm hgen
  rwa [MulEquiv.symm_apply_apply] at this

/-! ### The circle loop of a punctured disc -/

theorem norm_exp_two_pi_mul_I (t : ℝ) :
    ‖Complex.exp ((t : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))‖ = 1 := by
  rw [show (t : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) = ((t * (2 * Real.pi) : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem circle_mem_puncturedDisc {s : ℂ} {ρ : ℝ} {b : ℂ} (hb : b ∈ puncturedDisc s ρ) (t : ℝ) :
    s + Complex.exp ((t : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * (b - s)
      ∈ puncturedDisc s ρ := by
  have hne : Complex.exp ((t : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * (b - s) ≠ 0 :=
    mul_ne_zero (Complex.exp_ne_zero _) (sub_ne_zero_of_mem_puncturedDisc hb)
  refine mem_puncturedDisc.mpr ⟨?_, ?_⟩
  · rw [add_sub_cancel_left, norm_mul, norm_exp_two_pi_mul_I, one_mul]
    exact norm_sub_lt_of_mem_puncturedDisc hb
  · intro h
    exact hne (by simpa using congrArg (fun z => z - s) h)

/-- The loop of a punctured disc running once around the centre through a given point. -/
def discLoop (s : ℂ) {ρ : ℝ} (b : ↥(puncturedDisc s ρ)) : Path b b where
  toFun t :=
    ⟨s + Complex.exp ((((t : ℝ)) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * ((b : ℂ) - s),
      circle_mem_puncturedDisc b.2 _⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  source' := by
    refine Subtype.ext ?_
    simp
  target' := by
    refine Subtype.ext ?_
    simp [Complex.exp_two_pi_mul_I]

@[simp] theorem coe_discLoop (s : ℂ) {ρ : ℝ} (b : ↥(puncturedDisc s ρ)) (t : I) :
    ((discLoop s b t : ↥(puncturedDisc s ρ)) : ℂ)
      = s + Complex.exp ((((t : ℝ)) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * ((b : ℂ) - s) := rfl

/-- The radial stretch carries the circle loop of a punctured disc to the circle loop of the
punctured plane, on the nose: the stretch depends only on the distance to the centre, which is
constant along the loop. -/
theorem map_discLoop (s : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (b : ↥(puncturedDisc s ρ)) :
    (discLoop s b).map (puncturedDiscHomeo s hρ).continuous
      = circleLoop (puncturedDiscHomeo s hρ b) := by
  refine Path.ext (funext fun t => Subtype.ext ?_)
  show discOut s ρ (s + Complex.exp ((((t : ℝ)) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
      * ((b : ℂ) - s))
    = Complex.exp ((((t : ℝ)) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * discOut s ρ (b : ℂ)
  rw [discOut, discOut, add_sub_cancel_left, norm_mul, norm_exp_two_pi_mul_I, one_mul,
    Complex.real_smul, Complex.real_smul]
  ring

/-- **The circle loop of a punctured disc generates its fundamental group.**  The radial stretch
onto the punctured plane is a homeomorphism, hence an isomorphism on fundamental groups, and it
carries the circle loop of the disc to the circle loop of the plane. -/
theorem zpowers_discLoop_eq_top (s : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (b : ↥(puncturedDisc s ρ)) :
    Subgroup.zpowers
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (discLoop s b))) = ⊤ := by
  set φ := puncturedDiscHomeo s hρ with hφ
  set F := FundamentalGroup.map (φ.toHomotopyEquiv.toFun) b with hF
  have hinj : Function.Injective F := (fundamentalGroup_map_bijective φ.toHomotopyEquiv b).1
  have hFγ : F (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (discLoop s b)))
      = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (circleLoop (φ b))) := by
    show Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.mk (discLoop s b))
        φ.toHomotopyEquiv.toFun = Path.Homotopic.Quotient.mk (circleLoop (φ b))
    rw [← Path.Homotopic.Quotient.mk_map, map_discLoop]
  refine eq_top_iff.mpr fun y _ => ?_
  have hmem : F y ∈ Subgroup.zpowers
      (F (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (discLoop s b)))) := by
    rw [hFγ, zpowers_circleLoop_eq_top]
    exact Subgroup.mem_top _
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
  exact Subgroup.mem_zpowers_iff.mpr ⟨n, hinj (by rwa [map_zpow])⟩

end Rigidity.RET

end

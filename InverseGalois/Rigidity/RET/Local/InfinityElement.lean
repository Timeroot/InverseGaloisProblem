/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.DeckElement
import InverseGalois.Rigidity.RET.Analytic.InfinityBranch
import InverseGalois.Rigidity.RET.Analytic.InfinityPuiseux
import InverseGalois.Rigidity.RET.Analytic.InfinitySection
import InverseGalois.Rigidity.RET.Local.BranchGeneration
import InverseGalois.Rigidity.RET.Pi1.Topological.ExteriorLoop

/-!
# The loop at infinity of a cover unramified at infinity

A cover of the line that is unramified at the point at infinity should have nothing to say about
loops that wind around that point: such a loop ought to name the identity.  Here that is proved.

The argument at infinity mirrors the argument at a point of the line, with the parameter
`T = (uᵈ)⁻¹` in place of the Kummer coordinate `T = s + uᵉ`.  Reading the equation of the cover in
that parameter over a small punctured disc of the variable `u` produces a continuous branch of the
roots; unramifiedness at infinity says the branch is invariant under rotation of `u` by a `d`-th
root of unity, but only in the sense of germs at the origin.  A punctured disc is connected and two
branches of the roots over it are two lifts through a covering map, so the germwise identity
propagates to the whole disc.  Following the branch along the arc of angle `2π/d` then lifts the
circle at infinity through the cover and comes back to where it started, so the monodromy of the
loop at infinity fixes a point of the fibre.  Transporting that fixed point to the global base
point and reading off the name finishes the argument, because the monodromy of a loop moves every
point of the fibre by right multiplication with the inverse of its name.

## Main results

* `Rigidity.RET.LineCover.exists_fixed_extCycle` — over a cover unramified at infinity the
  monodromy of the circle at infinity fixes a point of the fibre.
* `Rigidity.RET.LineCover.deckCycle_eq_one_of_isInfinityLoop` — a loop winding around the point at
  infinity has trivial name.
-/

open Polynomial Filter Topology GeomAKLB Rigidity.RET.Analytic
open scoped unitInterval

noncomputable section

namespace Rigidity.RET

theorem extIncl_eq_subsetIncl {X : Set ℂ} {R : ℝ} (h : extRegion R ⊆ X) :
    extIncl h = subsetIncl h := rfl

namespace Analytic

variable {P : Polynomial (Polynomial ℂ)} {S : Finset ℂ}

/-- **The monodromy of the loop at infinity**, as a permutation of the fibre of the root cover
above the basepoint of an exterior region. -/
def extCycle (hP : P.Monic) (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {R : ℝ}
    (hsub : extRegion R ⊆ ((S : Set ℂ))ᶜ) (b : ↥(extRegion R)) :
    Equiv.Perm ↥(puncturedProj P S ⁻¹' {subsetIncl hsub b}) :=
  (isCoveringMap_puncturedProj hP hS).monodromyHom (subsetIncl hsub b)
    (FundamentalGroup.map (subsetIncl hsub) b
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (extLoop b))))

end Analytic

namespace LineCover

/-! ### The circle at infinity fixes a point of the fibre -/

/-- **Over a cover unramified at infinity the monodromy of the circle at infinity fixes a point of
the fibre.**  A branch of the roots in the parameter at infinity is invariant under rotation of
that parameter by a `d`-th root of unity, so following it along the arc of angle `2π/d` — which
covers the circle at infinity once — returns to the point it started from. -/
theorem exists_fixed_extCycle (L : LineCover) [Algebra k ℂ] {α : L.M}
    (hα : IsIntegral (Polynomial k) α)
    (hgen : IntermediateField.adjoin (RatFunc k) {α} = ⊤)
    {S : Finset ℂ}
    (hS : ∀ z ∉ (S : Set ℂ), (Analytic.spec (complexEquation α) z).Separable)
    (hinf : L.IsUnramifiedAtInfinity)
    {R : ℝ} (hR : 0 < R) (hsub : extRegion R ⊆ ((S : Set ℂ))ᶜ) (b : ↥(extRegion R)) :
    ∃ Y, Analytic.extCycle (monic_complexEquation hα) hS hsub b Y = Y := by
  classical
  set P : Polynomial (Polynomial ℂ) := complexEquation α with hPdef
  set hP : P.Monic := monic_complexEquation hα with hPmdef
  have hdeg : 0 < P.natDegree := by
    rw [hPdef, natDegree_complexEquation]
    exact minpoly.natDegree_pos hα
  obtain ⟨d, hdfac, hdpos⟩ : ∃ d : ℕ, Nat.factorial P.natDegree ∣ d ∧ 0 < d :=
    ⟨Nat.factorial P.natDegree, dvd_rfl, Nat.factorial_pos _⟩
  -- a `d`-th root of the inverse of the base point
  have hb0 : (b : ℂ) ≠ 0 := ne_zero_of_mem_extRegion hR.le b.2
  obtain ⟨u₀, hu₀⟩ : ∃ u : ℂ, u ^ d = (b : ℂ)⁻¹ := IsAlgClosed.exists_pow_nat_eq _ hdpos
  have hu₀0 : u₀ ≠ 0 := by
    intro h
    rw [h, zero_pow hdpos.ne'] at hu₀
    exact inv_ne_zero hb0 hu₀.symm
  have hbu : ((u₀ ^ d)⁻¹) = (b : ℂ) := by rw [hu₀, inv_inv]
  -- a radius for the disc of the parameter at infinity
  have hlt : ‖u₀‖ ^ d < R⁻¹ := by
    rw [← norm_pow, hu₀, norm_inv]
    exact (inv_lt_inv₀ (norm_pos_iff.2 hb0) hR).2 b.2
  obtain ⟨ρ', hρ'pow, hρ'gt⟩ : ∃ x : ℝ, x ^ d < R⁻¹ ∧ ‖u₀‖ < x := by
    have hev : ∀ᶠ x in 𝓝[>] ‖u₀‖, x ^ d < R⁻¹ :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (((continuous_pow d).tendsto ‖u₀‖).eventually_lt_const hlt)
    obtain ⟨x, hx1, hx2⟩ := (hev.and self_mem_nhdsWithin).exists
    exact ⟨x, hx1, hx2⟩
  have hρ' : 0 < ρ' := lt_of_le_of_lt (norm_nonneg _) hρ'gt
  have hρ0 : 0 < ρ' ^ d := pow_pos hρ' d
  have hinv : ∀ z ∈ puncturedDisc (0 : ℂ) (ρ' ^ d), z⁻¹ ∈ extRegion R :=
    inv_mem_extRegion hR hρ'pow.le
  have hmap : ∀ u ∈ puncturedDisc (0 : ℂ) ρ',
      (0 : ℂ) + u ^ d ∈ puncturedDisc (0 : ℂ) (ρ' ^ d) := by
    intro u hu
    obtain ⟨hlt', hne⟩ := mem_puncturedDisc.mp hu
    rw [sub_zero] at hlt'
    refine mem_puncturedDisc.mpr ⟨?_, ?_⟩
    · rw [zero_add, sub_zero, norm_pow]
      exact pow_lt_pow_left₀ hlt' (norm_nonneg u) hdpos.ne'
    · rw [zero_add]
      exact pow_ne_zero d hne
  have hext : ∀ u ∈ puncturedDisc (0 : ℂ) ρ', ((u ^ d)⁻¹) ∈ extRegion R := by
    intro u hu
    have h := hinv _ (hmap u hu)
    rwa [zero_add] at h
  have hnotS : ∀ u ∈ puncturedDisc (0 : ℂ) ρ', ((u ^ d)⁻¹) ∉ (S : Set ℂ) :=
    fun u hu => hsub (hext u hu)
  have hsep : ∀ u ∈ puncturedDisc (0 : ℂ) ρ', (Analytic.spec P ((u ^ d)⁻¹)).Separable :=
    fun u hu => hS _ (hnotS u hu)
  have hu₀mem : u₀ ∈ puncturedDisc (0 : ℂ) ρ' :=
    mem_puncturedDisc.mpr ⟨by rw [sub_zero]; exact hρ'gt, hu₀0⟩
  -- a branch of the roots in the parameter at infinity
  obtain ⟨y₀, hy₀⟩ : ∃ y : ℂ, (Analytic.spec P ((u₀ ^ d)⁻¹)).eval y = 0 := by
    have hnd : 0 < (Analytic.spec P ((u₀ ^ d)⁻¹)).natDegree := by
      rw [Analytic.natDegree_spec hP]
      exact hdeg
    obtain ⟨y, hy⟩ := Complex.exists_root (natDegree_pos_iff_degree_pos.mp hnd)
    exact ⟨y, hy⟩
  obtain ⟨gb, hgcont, -, hgroot⟩ :=
    Analytic.exists_root_on_puncturedDisc_inv hP hS hρ0 hρ' hdfac hsub hmap hinv
      ⟨u₀, hu₀mem⟩ hy₀
  -- it is a meromorphic germ at the origin, invariant under rotation of the parameter
  have hmero : MeromorphicAt gb 0 :=
    Analytic.meromorphicAt_of_root_inv hP hdeg hρ' hgcont hsep hgroot
  have hdiscmem : puncturedDisc (0 : ℂ) ρ' ∈ 𝓝[≠] (0 : ℂ) := by
    rw [show puncturedDisc (0 : ℂ) ρ' = Metric.ball (0 : ℂ) ρ' ∩ ({(0 : ℂ)}ᶜ) from
      Set.diff_eq _ _]
    exact Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ hρ'))
      self_mem_nhdsWithin
  have hrootev : ∀ᶠ u in 𝓝[≠] (0 : ℂ), (Analytic.spec P ((u ^ d)⁻¹)).eval (gb u) = 0 := by
    filter_upwards [hdiscmem] with u hu using hgroot u hu
  have hnormζ : ‖kummerRot d‖ = 1 := norm_kummerRot d
  have hζ0 : kummerRot d ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnormζ
    exact zero_ne_one hnormζ
  have hζpow : kummerRot d ^ d = 1 := kummerRot_pow hdpos
  have hev : ∀ᶠ u in 𝓝[≠] (0 : ℂ), gb u = gb (kummerRot d * u) :=
    Analytic.eventuallyEq_scale_of_isUnramifiedAtInfinity hdpos hα hgen hmero hrootev hinf hζpow
  -- the invariance holds on the whole disc, not only near the origin
  have hgζcont : ContinuousOn (fun u => gb (kummerRot d * u)) (puncturedDisc (0 : ℂ) ρ') := by
    refine hgcont.comp (continuous_const.mul continuous_id).continuousOn fun u hu => ?_
    exact LineCover.mul_mem_puncturedDisc hnormζ hζ0 hu
  have hgζroot : ∀ u ∈ puncturedDisc (0 : ℂ) ρ',
      (Analytic.spec P ((u ^ d)⁻¹)).eval (gb (kummerRot d * u)) = 0 := by
    intro u hu
    have h := hgroot (kummerRot d * u) (LineCover.mul_mem_puncturedDisc hnormζ hζ0 hu)
    rwa [mul_pow, hζpow, one_mul] at h
  obtain ⟨u₁, hu₁ev, hu₁mem⟩ := (hev.and hdiscmem).exists
  have hkey : gb u₀ = gb (kummerRot d * u₀) :=
    Analytic.eqOn_of_root_inv hP hS hρ' hnotS hgcont hgζcont hgroot hgζroot hu₁mem hu₁ev hu₀mem
  -- the explicit lift of the circle at infinity
  have harcmem : ∀ t : ℝ, kummerArc d u₀ t ∈ puncturedDisc (0 : ℂ) ρ' :=
    fun t => kummerArc_mem_puncturedDisc hu₀mem t
  have hroot_t : ∀ t : ℝ,
      (Analytic.spec P ((kummerArc d u₀ t ^ d)⁻¹)).eval (gb (kummerArc d u₀ t)) = 0 :=
    fun t => hgroot _ (harcmem t)
  have hmem_t : ∀ t : ℝ, ((kummerArc d u₀ t ^ d)⁻¹) ∉ (S : Set ℂ) :=
    fun t => hnotS _ (harcmem t)
  set cov := Analytic.isCoveringMap_puncturedProj hP hS with hcovdef
  set Γ : C(I, ↥(Analytic.rootProj P ⁻¹' ((S : Set ℂ)ᶜ))) :=
    ⟨fun t => ⟨⟨(((kummerArc d u₀ (t : ℝ) ^ d)⁻¹), gb (kummerArc d u₀ (t : ℝ))),
        hroot_t (t : ℝ)⟩, hmem_t (t : ℝ)⟩,
      by
        refine Continuous.subtype_mk (Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _) _
        · exact ((continuous_kummerArc d u₀).pow d).inv₀
            fun t => pow_ne_zero _ (mem_puncturedDisc.mp (harcmem (t : ℝ))).2
        · exact hgcont.comp_continuous (continuous_kummerArc d u₀)
            fun t => harcmem (t : ℝ)⟩ with hΓdef
  set q : Path (subsetIncl hsub b) (subsetIncl hsub b) :=
    (extLoop b).map (subsetIncl hsub).continuous with hqdef
  have hlift : ∀ t : I, Analytic.puncturedProj P S (Γ t) = q t := by
    intro t
    refine Subtype.ext ?_
    show ((kummerArc d u₀ (t : ℝ) ^ d)⁻¹) = ((extLoop b t : ↥(extRegion R)) : ℂ)
    rw [coe_extLoop, kummerArc_pow hdpos, mul_inv, hbu, neg_mul, Complex.exp_neg]
  have hpath : (FundamentalGroup.map (subsetIncl hsub) b
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (extLoop b)))).toPath
      = Path.Homotopic.Quotient.mk q := by
    show Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.mk (extLoop b))
      (subsetIncl hsub) = Path.Homotopic.Quotient.mk q
    rw [hqdef]
    exact (Path.Homotopic.Quotient.mk_map _ _).symm
  have hmem0 : Analytic.puncturedProj P S (Γ 0) = subsetIncl hsub b := (hlift 0).trans q.source
  refine ⟨⟨Γ 0, hmem0⟩, ?_⟩
  refine Subtype.ext ?_
  show (cov.monodromy (FundamentalGroup.map (subsetIncl hsub) b
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (extLoop b)))).toPath
      (⟨Γ 0, hmem0⟩ : ↥(Analytic.puncturedProj P S ⁻¹' {subsetIncl hsub b})) :
      ↥(Analytic.rootProj P ⁻¹' ((S : Set ℂ)ᶜ))) = Γ 0
  rw [hpath, cov.monodromy_of_lift q Γ hlift ⟨Γ 0, hmem0⟩ rfl]
  refine Subtype.ext (Subtype.ext ?_)
  show (((kummerArc d u₀ (((1 : I) : ℝ)) ^ d)⁻¹), gb (kummerArc d u₀ (((1 : I) : ℝ))))
    = (((kummerArc d u₀ (((0 : I) : ℝ)) ^ d)⁻¹), gb (kummerArc d u₀ (((0 : I) : ℝ))))
  rw [Set.Icc.coe_zero, Set.Icc.coe_one, kummerArc_zero, kummerArc_one, mul_pow, hζpow, one_mul,
    hkey]

/-- **Over a cover unramified at infinity every loop of an exterior region fixes a point of the
fibre.**  The circle at infinity generates the fundamental group of the exterior region, so its
fixed point is fixed by the monodromy of every loop there. -/
theorem exists_fixed_extLoopMap (L : LineCover) [Algebra k ℂ] {α : L.M}
    (hα : IsIntegral (Polynomial k) α)
    (hgen : IntermediateField.adjoin (RatFunc k) {α} = ⊤)
    {S : Finset ℂ}
    (hS : ∀ z ∉ (S : Set ℂ), (Analytic.spec (complexEquation α) z).Separable)
    (hinf : L.IsUnramifiedAtInfinity)
    {R : ℝ} (hR : 0 < R) (hsub : extRegion R ⊆ ((S : Set ℂ))ᶜ) (b : ↥(extRegion R))
    (g : FundamentalGroup ↥(extRegion R) b) :
    ∃ Y, (Analytic.isCoveringMap_puncturedProj (monic_complexEquation hα) hS).monodromyHom
      (subsetIncl hsub b) (FundamentalGroup.map (subsetIncl hsub) b g) Y = Y := by
  obtain ⟨Y, hY⟩ := L.exists_fixed_extCycle hα hgen hS hinf hR hsub b
  refine ⟨Y, ?_⟩
  set Ψ := ((Analytic.isCoveringMap_puncturedProj (monic_complexEquation hα) hS).monodromyHom
    (subsetIncl hsub b)).comp (FundamentalGroup.map (subsetIncl hsub) b) with hΨdef
  have hmem : Ψ g ∈ Subgroup.zpowers
      (Ψ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (extLoop b)))) := by
    rw [← MonoidHom.map_zpowers, zpowers_extLoop_eq_top hR b]
    exact ⟨g, trivial, rfl⟩
  have hstab : Subgroup.zpowers
      (Ψ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (extLoop b))))
      ≤ MulAction.stabilizer (Equiv.Perm _) Y :=
    Subgroup.zpowers_le.2 hY
  exact hstab hmem

/-! ### The name of a loop at infinity -/

/-- **A loop winding around the point at infinity of a cover unramified there has trivial name.**
The monodromy of such a loop fixes a point of the fibre, and the monodromy of a loop moves every
point of the fibre by right multiplication with the inverse of its name, so the name is trivial. -/
theorem deckCycle_eq_one_of_isInfinityLoop (L : LineCover) [Algebra k ℂ] {α : L.M}
    (D : DeckData α) (hα : IsIntegral (Polynomial k) α)
    (hgen : IntermediateField.adjoin (RatFunc k) {α} = ⊤)
    {S : Finset ℂ} (hbadS : (D.badSetC : Set ℂ) ⊆ (S : Set ℂ))
    (hS : ∀ z ∉ (S : Set ℂ), (Analytic.spec (complexEquation α) z).Separable)
    (hinf : L.IsUnramifiedAtInfinity)
    {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ))
    (e₀ : Analytic.puncturedProj (complexEquation α) S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))})
    {γ : FundamentalGroup ↥((S : Set ℂ)ᶜ) ⟨z₀, hz₀⟩}
    (hγ : IsInfinityLoop ((S : Set ℂ)ᶜ) hz₀ γ) :
    ((D.toIntegralDeck.toRationalDeck).mono hbadS).deckCycle (monic_complexEquation hα) hS hz₀
      (L.card_deck_eq_natDegree_complexEquation hα hgen) e₀ γ = 1 := by
  classical
  obtain ⟨R, hincl, b, g, δ, hR, -, hγeq⟩ := hγ
  set cov := Analytic.isCoveringMap_puncturedProj (monic_complexEquation hα) hS with hcovdef
  set RD : Analytic.RationalDeck (complexEquation α) S L.deck :=
    (D.toIntegralDeck.toRationalDeck).mono hbadS with hRDdef
  obtain ⟨Y, hY⟩ := L.exists_fixed_extLoopMap hα hgen hS hinf hR hincl b g
  refine RD.deckCycle_eq_one_of_fixed (monic_complexEquation hα) hS hz₀
    (L.card_deck_eq_natDegree_complexEquation hα hgen) e₀ γ
    (Y := cov.fibreEquiv (Path.Homotopic.Quotient.mk δ) Y) ?_
  rw [hγeq, show Analytic.monodromyHom (monic_complexEquation hα) hS hz₀
      (FundamentalGroup.fundamentalGroupMulEquivOfPath δ
        (FundamentalGroup.map (extIncl hincl) b g))
      = Equiv.permCongrHom (cov.fibreEquiv (Path.Homotopic.Quotient.mk δ))
          (cov.monodromyHom (subsetIncl hincl b)
            (FundamentalGroup.map (subsetIncl hincl) b g)) from
    cov.monodromyHom_transport (Path.Homotopic.Quotient.mk δ) _]
  show cov.fibreEquiv (Path.Homotopic.Quotient.mk δ)
      (cov.monodromyHom (subsetIncl hincl b) (FundamentalGroup.map (subsetIncl hincl) b g)
        ((cov.fibreEquiv (Path.Homotopic.Quotient.mk δ)).symm
          (cov.fibreEquiv (Path.Homotopic.Quotient.mk δ) Y))) = _
  rw [Equiv.symm_apply_apply, hY]

end LineCover

end Rigidity.RET

end

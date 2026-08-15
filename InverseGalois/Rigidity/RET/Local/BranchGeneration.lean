/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.DiscCycle
import InverseGalois.Rigidity.RET.Analytic.KummerSection
import InverseGalois.Rigidity.RET.Local.BranchInertia
import InverseGalois.Rigidity.RET.Local.DiscMonodromy

/-!
# The inertia group at a branch point is the local monodromy group

The order of the monodromy of a small loop around a parameter bounds the order of every inertia
element there, and an inertia element whose order reaches that bound generates the whole inertia
group.  What is proved here is the matching lower bound: there really is an inertia element whose
order is at least the order of the local monodromy.

The element is produced by following the branch of the roots that lives on the punctured disc once
around the circle.  Written in the Kummer coordinate `z = s + uᵉ`, the circle downstairs is the
image of an arc of angle `2π/e` upstairs, so the endpoint of the lifted loop is the branch
evaluated at the rotated variable — and the deck transformation carrying the branch to its rotation
is exactly the inertia element supplied by the branch.  The monodromy of the circle therefore
*acts as* that inertia element on one point of the fibre, and because the deck formulas are
transitive on the fibre and commute with the monodromy, a power of the inertia element that is
trivial forces the same power of the monodromy to be trivial everywhere.

## Main results

* `Rigidity.RET.LineCover.exists_isInertiaAt_orderOf_discCycle_dvd` — a Kummer coordinate on a
  punctured disc whose exponent annihilates the monodromy of the circle produces an inertia element
  whose order is a multiple of that monodromy's order.
* `Rigidity.RET.LineCover.exists_isInertiaGenAt_of_isLocalMonodromy` — a generator of the inertia
  group at any parameter carrying a local monodromy element.
-/

open Polynomial Filter Topology GeomAKLB unitInterval Rigidity.RET.Analytic

noncomputable section

namespace Rigidity.RET

/-! ### The rotation of the Kummer coordinate -/

/-- The rotation of the Kummer coordinate `z = s + uᵉ` that fixes the parameter and cycles the
`e` sheets. -/
def kummerRot (e : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (e : ℂ))

theorem norm_kummerRot (e : ℕ) : ‖kummerRot e‖ = 1 := by
  rw [kummerRot,
    show (2 * (Real.pi : ℂ) * Complex.I / (e : ℂ))
        = (((2 * Real.pi / e : ℝ)) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem kummerRot_pow {e : ℕ} (he : 0 < e) : kummerRot e ^ e = 1 := by
  have hne : ((e : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr he.ne'
  rw [kummerRot, ← Complex.exp_nat_mul,
    show ((e : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I / (e : ℂ))
        = 2 * (Real.pi : ℂ) * Complex.I by field_simp]
  exact Complex.exp_two_pi_mul_I

/-- The arc of angle `2π/e` in the Kummer coordinate whose image downstairs is the full circle. -/
def kummerArc (e : ℕ) (w : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (((t : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) / (e : ℂ)) * w

theorem norm_kummerArc_factor (e : ℕ) (t : ℝ) :
    ‖Complex.exp (((t : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) / (e : ℂ))‖ = 1 := by
  rw [show (((t : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) / (e : ℂ))
        = (((t * (2 * Real.pi) / e : ℝ)) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem kummerArc_zero (e : ℕ) (w : ℂ) : kummerArc e w 0 = w := by
  simp [kummerArc]

theorem kummerArc_one {e : ℕ} (w : ℂ) : kummerArc e w 1 = kummerRot e * w := by
  simp [kummerArc, kummerRot]

theorem kummerArc_pow {e : ℕ} (he : 0 < e) (w : ℂ) (t : ℝ) :
    kummerArc e w t ^ e = Complex.exp (((t : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I)) * w ^ e := by
  have hne : ((e : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr he.ne'
  rw [kummerArc, mul_pow, ← Complex.exp_nat_mul,
    show ((e : ℂ)) * (((t : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) / (e : ℂ))
        = ((t : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) by field_simp]

theorem continuous_kummerArc (e : ℕ) (w : ℂ) : Continuous fun t : I => kummerArc e w (t : ℝ) := by
  simp only [kummerArc]
  fun_prop

theorem kummerArc_mem_puncturedDisc {e : ℕ} {ρ : ℝ} {w : ℂ}
    (hw : w ∈ puncturedDisc (0 : ℂ) ρ) (t : ℝ) : kummerArc e w t ∈ puncturedDisc (0 : ℂ) ρ :=
  LineCover.mul_mem_puncturedDisc (norm_kummerArc_factor e t)
    (Complex.exp_ne_zero _) hw

namespace LineCover

variable (L : LineCover) [Algebra k ℂ] {s : k} {α : L.M}

/-! ### The circle monodromy is realized by an inertia element -/

/-- **A Kummer coordinate whose exponent annihilates the monodromy of the circle produces an
inertia element of at least that order.**  The exponent makes the roots single-valued on the
Kummer disc, so a branch of the roots lives there; a deck transformation carries that branch to
its rotation, and it is an inertia element.  Following the branch along the arc of angle `2π/e`
lifts the circle downstairs, so the monodromy of the circle moves one point of the fibre exactly
as that deck transformation does.  Since the deck formulas act transitively on the fibre and
commute with the monodromy, any power of the deck transformation that is trivial makes the
corresponding power of the monodromy trivial on all of the fibre. -/
theorem exists_isInertiaAt_orderOf_discCycle_dvd (D : DeckData α)
    (hα : IsIntegral (Polynomial k) α)
    (hgen : IntermediateField.adjoin (RatFunc k) {α} = ⊤)
    {S : Finset ℂ} (hbadS : (D.badSetC : Set ℂ) ⊆ (S : Set ℂ))
    (hS : ∀ z ∉ (S : Set ℂ), (Analytic.spec (complexEquation α) z).Separable)
    {ρ ρ' : ℝ} (hρ : 0 < ρ) (hρ' : 0 < ρ')
    (hincl : puncturedDisc (algebraMap k ℂ s) ρ ⊆ ((S : Set ℂ))ᶜ)
    {e : ℕ} (he : 0 < e)
    (hmap : ∀ u ∈ puncturedDisc (0 : ℂ) ρ',
      algebraMap k ℂ s + u ^ e ∈ puncturedDisc (algebraMap k ℂ s) ρ)
    (w : ↥(puncturedDisc (0 : ℂ) ρ'))
    (hfix : Analytic.discCycle (monic_complexEquation hα) hS hincl
        (kummerRegionMap (algebraMap k ℂ s) e hmap w) ^ e = 1) :
    ∃ τ : L.deck, L.IsInertiaAt s τ ∧
      orderOf (Analytic.discCycle (monic_complexEquation hα) hS hincl
        (kummerRegionMap (algebraMap k ℂ s) e hmap w)) ∣ orderOf τ := by
  classical
  set σc : ℂ := algebraMap k ℂ s with hσdef
  set P : Polynomial (Polynomial ℂ) := complexEquation α with hPdef
  set hP : P.Monic := monic_complexEquation hα with hPmdef
  set b : ↥(puncturedDisc σc ρ) := kummerRegionMap σc e hmap w with hbdef
  have hbcoe : ((b : ℂ)) = σc + (w : ℂ) ^ e := rfl
  set cov := Analytic.isCoveringMap_puncturedProj hP hS with hcovdef
  set x := Analytic.discCycle hP hS hincl b with hxdef
  -- the bad parameters are avoided on the whole Kummer disc
  have hbad : ∀ u ∈ puncturedDisc (0 : ℂ) ρ', σc + u ^ e ∉ (D.badSetC : Set ℂ) :=
    fun u hu hmem => hincl (hmap u hu) (hbadS hmem)
  -- some root above the basepoint
  obtain ⟨y₀, hy₀⟩ : ∃ y : ℂ, (Analytic.spec P (σc + (w : ℂ) ^ e)).eval y = 0 := by
    have hnd : 0 < (Analytic.spec P (σc + (w : ℂ) ^ e)).natDegree := by
      rw [Analytic.natDegree_spec hP, hPdef, natDegree_complexEquation]
      exact minpoly.natDegree_pos hα
    obtain ⟨y, hy⟩ := Complex.exists_root (natDegree_pos_iff_degree_pos.mp hnd)
    exact ⟨y, hy⟩
  -- a branch of the roots on the Kummer disc
  obtain ⟨gb, hgcont, -, hgroot⟩ :=
    Analytic.exists_root_on_puncturedDisc_of_gen hP hS hρ hρ' hincl hmap w hy₀
      (zpowers_discLoop_eq_top σc hρ b)
      (show (x ^ e) (Analytic.fibrePoint (subsetIncl hincl b) hy₀)
          = Analytic.fibrePoint (subsetIncl hincl b) hy₀ by rw [hfix]; rfl)
  -- the inertia element carrying the branch to its rotation
  obtain ⟨τ, hinert, hact⟩ :=
    L.exists_isInertiaAt_of_branch D hα hgen he (norm_kummerRot e) (kummerRot_pow he) hρ' hbad
      hgcont hgroot
  refine ⟨τ, hinert, ?_⟩
  -- the group of formulas, read away from the coarser exceptional set
  set RD : Analytic.RationalDeck P S L.deck := (D.toIntegralDeck.toRationalDeck).mono hbadS
    with hRDdef
  have hRDact : RD.act = D.toIntegralDeck.act := rfl
  haveI : Finite L.deck := inferInstance
  have hcard : Nat.card L.deck = P.natDegree :=
    L.card_deck_eq_natDegree_complexEquation hα hgen
  letI : MulAction L.deck ↥(Analytic.rootProj P ⁻¹' ((S : Set ℂ)ᶜ)) := RD.mulAction
  have hsm : ∀ (g : L.deck) (Y : ↥(Analytic.rootProj P ⁻¹' ((S : Set ℂ)ᶜ))),
      g • Y = RD.smul g Y := fun _ _ => rfl
  -- the explicit lift of the circle
  have harcmem : ∀ t : ℝ, kummerArc e (w : ℂ) t ∈ puncturedDisc (0 : ℂ) ρ' :=
    fun t => kummerArc_mem_puncturedDisc w.2 t
  have hroot_t : ∀ t : ℝ,
      (Analytic.spec P (σc + kummerArc e (w : ℂ) t ^ e)).eval (gb (kummerArc e (w : ℂ) t)) = 0 :=
    fun t => hgroot _ (harcmem t)
  have hmem_t : ∀ t : ℝ, σc + kummerArc e (w : ℂ) t ^ e ∉ (S : Set ℂ) :=
    fun t => hincl (hmap _ (harcmem t))
  set Γ : C(I, ↥(Analytic.rootProj P ⁻¹' ((S : Set ℂ)ᶜ))) :=
    ⟨fun t => ⟨⟨(σc + kummerArc e (w : ℂ) (t : ℝ) ^ e, gb (kummerArc e (w : ℂ) (t : ℝ))),
        hroot_t (t : ℝ)⟩, hmem_t (t : ℝ)⟩,
      by
        refine Continuous.subtype_mk (Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _) _
        · exact continuous_const.add ((continuous_kummerArc e (w : ℂ)).pow e)
        · exact hgcont.comp_continuous (continuous_kummerArc e (w : ℂ))
            fun t => harcmem (t : ℝ)⟩ with hΓdef
  -- it lies over the circle loop of the punctured disc
  set q : Path (subsetIncl hincl b) (subsetIncl hincl b) :=
    (discLoop σc b).map (subsetIncl hincl).continuous with hqdef
  have hlift : ∀ t : I, Analytic.puncturedProj P S (Γ t) = q t := by
    intro t
    refine Subtype.ext ?_
    show σc + kummerArc e (w : ℂ) (t : ℝ) ^ e
      = ((discLoop σc b t : ↥(puncturedDisc σc ρ)) : ℂ)
    rw [coe_discLoop, kummerArc_pow he, hbcoe]
    ring
  -- the loop it lies over is the loop naming the circle monodromy
  have hpath : (FundamentalGroup.map (subsetIncl hincl) b
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (discLoop σc b)))).toPath
      = Path.Homotopic.Quotient.mk q := by
    show Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.mk (discLoop σc b))
      (subsetIncl hincl) = Path.Homotopic.Quotient.mk q
    rw [hqdef]
    exact (Path.Homotopic.Quotient.mk_map _ _).symm
  have hxapply : ∀ Y : ↥(Analytic.puncturedProj P S ⁻¹' {subsetIncl hincl b}),
      ((x Y : ↥(Analytic.rootProj P ⁻¹' ((S : Set ℂ)ᶜ))))
        = (cov.monodromy (Path.Homotopic.Quotient.mk q) Y :
            ↥(Analytic.rootProj P ⁻¹' ((S : Set ℂ)ᶜ))) := by
    intro Y
    rw [hxdef]
    show ((cov.monodromy (FundamentalGroup.map (subsetIncl hincl) b
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (discLoop σc b)))).toPath Y :
        ↥(Analytic.rootProj P ⁻¹' ((S : Set ℂ)ᶜ)))) = _
    rw [hpath]
  -- the distinguished point of the fibre
  have hmem0 : Analytic.puncturedProj P S (Γ 0) = subsetIncl hincl b := (hlift 0).trans q.source
  set e₀ : ↥(Analytic.puncturedProj P S ⁻¹' {subsetIncl hincl b}) := ⟨Γ 0, hmem0⟩ with he₀def
  -- the monodromy of the circle moves it the way the inertia element does
  have hτe₀ : ((RD.orbitFibre (hincl b.2) e₀ τ :
      ↥(Analytic.puncturedProj P S ⁻¹' {subsetIncl hincl b})) :
      ↥(Analytic.rootProj P ⁻¹' ((S : Set ℂ)ᶜ))) = Γ 1 := by
    refine Subtype.ext (Subtype.ext ?_)
    have h1 : σc + kummerArc e (w : ℂ) 0 ^ e = σc + kummerArc e (w : ℂ) 1 ^ e := by
      rw [kummerArc_zero, kummerArc_one, mul_pow, kummerRot_pow he, one_mul]
    have h2 : RD.act τ (σc + kummerArc e (w : ℂ) 0 ^ e) (gb (kummerArc e (w : ℂ) 0))
        = gb (kummerArc e (w : ℂ) 1) := by
      rw [kummerArc_zero, kummerArc_one, hRDact]
      exact hact (w : ℂ) w.2
    show (σc + kummerArc e (w : ℂ) 0 ^ e,
        RD.act τ (σc + kummerArc e (w : ℂ) 0 ^ e) (gb (kummerArc e (w : ℂ) 0)))
      = (σc + kummerArc e (w : ℂ) 1 ^ e, gb (kummerArc e (w : ℂ) 1))
    simp only [Prod.mk.injEq]
    exact ⟨h1, h2⟩
  have hxe₀ : x e₀ = RD.orbitFibre (hincl b.2) e₀ τ := by
    refine Subtype.ext ?_
    rw [hxapply, cov.monodromy_of_lift q Γ hlift e₀ rfl]
    exact hτe₀.symm
  -- the monodromy commutes with the formulas
  have hcomm : ∀ (g : L.deck) (Y : ↥(Analytic.puncturedProj P S ⁻¹' {subsetIncl hincl b})),
      x (RD.orbitFibre (hincl b.2) Y g) = RD.orbitFibre (hincl b.2) (x Y) g := by
    intro g Y
    refine Subtype.ext ?_
    show ((x (RD.orbitFibre (hincl b.2) Y g) :
        ↥(Analytic.puncturedProj P S ⁻¹' {subsetIncl hincl b})) :
        ↥(Analytic.rootProj P ⁻¹' ((S : Set ℂ)ᶜ)))
      = RD.smul g ((x Y : ↥(Analytic.puncturedProj P S ⁻¹' {subsetIncl hincl b})) :
        ↥(Analytic.rootProj P ⁻¹' ((S : Set ℂ)ᶜ)))
    rw [hxapply, hxapply]
    exact cov.monodromy_comp_deck (RD.continuous_smul g) (RD.puncturedProj_smul g)
      (Path.Homotopic.Quotient.mk q) Y
  have hcommn : ∀ (n : ℕ) (g : L.deck)
      (Y : ↥(Analytic.puncturedProj P S ⁻¹' {subsetIncl hincl b})),
      (x ^ n) (RD.orbitFibre (hincl b.2) Y g)
        = RD.orbitFibre (hincl b.2) ((x ^ n) Y) g := by
    intro n
    induction n with
    | zero => intro g Y; rw [pow_zero]; rfl
    | succ n ih =>
      intro g Y
      rw [pow_succ', Equiv.Perm.mul_apply, ih, hcomm, ← Equiv.Perm.mul_apply, ← pow_succ']
  have horb : ∀ (g h : L.deck) (Y : ↥(Analytic.puncturedProj P S ⁻¹' {subsetIncl hincl b})),
      RD.orbitFibre (hincl b.2) (RD.orbitFibre (hincl b.2) Y g) h
        = RD.orbitFibre (hincl b.2) Y (h * g) := by
    intro g h Y
    refine Subtype.ext ?_
    show RD.smul h (RD.smul g (Y : ↥(Analytic.rootProj P ⁻¹' ((S : Set ℂ)ᶜ))))
      = RD.smul (h * g) (Y : ↥(Analytic.rootProj P ⁻¹' ((S : Set ℂ)ᶜ)))
    rw [← hsm, ← hsm, ← hsm, mul_smul]
  have hpowe : ∀ n : ℕ, (x ^ n) e₀ = RD.orbitFibre (hincl b.2) e₀ (τ ^ n) := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero, pow_zero, Equiv.Perm.one_apply]
      refine Subtype.ext ?_
      show (e₀ : ↥(Analytic.rootProj P ⁻¹' ((S : Set ℂ)ᶜ)))
        = RD.smul 1 (e₀ : ↥(Analytic.rootProj P ⁻¹' ((S : Set ℂ)ᶜ)))
      rw [← hsm, one_smul]
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih, hcomm, hxe₀, horb, ← pow_succ]
  -- conclude
  refine orderOf_dvd_of_pow_eq_one ?_
  have hfix0 : (x ^ orderOf τ) e₀ = e₀ := by
    rw [hpowe, pow_orderOf_eq_one]
    refine Subtype.ext ?_
    show RD.smul 1 (e₀ : ↥(Analytic.rootProj P ⁻¹' ((S : Set ℂ)ᶜ)))
      = (e₀ : ↥(Analytic.rootProj P ⁻¹' ((S : Set ℂ)ᶜ)))
    rw [← hsm, one_smul]
  refine Equiv.ext fun Y => ?_
  obtain ⟨g, rfl⟩ := RD.surjective_orbitFibre hP hS (hincl b.2) hcard e₀ Y
  rw [hcommn, hfix0]
  rfl

/-! ### The inertia generator -/

/-- **A local monodromy element at a parameter is matched by a generator of the inertia group
there.**  The order of the local monodromy bounds the order of every inertia element from above,
and the inertia element following a branch of the roots once around the circle reaches that bound;
an inertia element of maximal order generates the inertia group. -/
theorem exists_isInertiaGenAt_of_isLocalMonodromy (D : DeckData α)
    (hα : IsIntegral (Polynomial k) α)
    (hgen : IntermediateField.adjoin (RatFunc k) {α} = ⊤)
    {S : Finset ℂ} (hbadS : (D.badSetC : Set ℂ) ⊆ (S : Set ℂ))
    (hS : ∀ z ∉ (S : Set ℂ), (Analytic.spec (complexEquation α) z).Separable)
    {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ))
    {x : Equiv.Perm (Analytic.puncturedProj (complexEquation α) S ⁻¹'
      {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))})}
    (hx : Analytic.IsLocalMonodromy (monic_complexEquation hα) hS hz₀ (algebraMap k ℂ s) x) :
    ∃ τ : L.deck, L.IsInertiaGenAt s τ := by
  classical
  obtain ⟨γ, ⟨ρ, hincl, b, g, δ, hρ, hgtop, hγ⟩, hxγ⟩ := hx
  have hx' : Analytic.IsLocalMonodromy (monic_complexEquation hα) hS hz₀ (algebraMap k ℂ s) x :=
    ⟨γ, ⟨ρ, hincl, b, g, δ, hρ, hgtop, hγ⟩, hxγ⟩
  -- the order of the local monodromy is the order of the monodromy of the circle
  have hord : orderOf x
      = orderOf (Analytic.discCycle (monic_complexEquation hα) hS hincl b) := by
    subst hγ
    subst hxγ
    rw [Analytic.orderOf_discCycle (monic_complexEquation hα) hS hρ hincl b hgtop,
      ← FundamentalGroup.transport_mk]
    exact ((Analytic.isCoveringMap_puncturedProj (monic_complexEquation hα)
      hS).orderOf_monodromyHom_transport (Path.Homotopic.Quotient.mk δ) _)
  set n : ℕ := orderOf (Analytic.discCycle (monic_complexEquation hα) hS hincl b) with hndef
  haveI : Finite (Analytic.puncturedProj (complexEquation α) S ⁻¹'
      {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}) :=
    (Analytic.finite_puncturedFiber (monic_complexEquation hα) hz₀).to_subtype
  have hn : 0 < n := by
    rw [← hord]
    exact orderOf_pos_iff.mpr (isOfFinOrder_of_finite x)
  -- read the disc in the Kummer coordinate of that exponent
  obtain ⟨ρ', hρ', hmap, w, hw⟩ := exists_kummerRegionMap_eq hρ hn b
  have hordeq : orderOf (Analytic.discCycle (monic_complexEquation hα) hS hincl
      (kummerRegionMap (algebraMap k ℂ s) n hmap w)) = n := by
    rw [hw]
  have hfix : Analytic.discCycle (monic_complexEquation hα) hS hincl
      (kummerRegionMap (algebraMap k ℂ s) n hmap w) ^ n = 1 := by
    have hp := pow_orderOf_eq_one (Analytic.discCycle (monic_complexEquation hα) hS hincl
      (kummerRegionMap (algebraMap k ℂ s) n hmap w))
    rwa [hordeq] at hp
  obtain ⟨τ, hinert, hdvd⟩ :=
    L.exists_isInertiaAt_orderOf_discCycle_dvd D hα hgen hbadS hS hρ hρ' hincl hn hmap w hfix
  rw [hordeq] at hdvd
  refine ⟨τ, L.isInertiaGenAt_of_localMonodromy hα hgen hS hz₀ hx' hinert ?_⟩
  rw [hord]
  exact Nat.le_of_dvd (orderOf_pos_iff.mpr (isOfFinOrder_of_finite τ)) hdvd

end LineCover

end Rigidity.RET

end

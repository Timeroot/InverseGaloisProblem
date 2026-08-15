/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.LocalCycles
import InverseGalois.Rigidity.RET.Local.KummerBranch
import InverseGalois.Rigidity.RET.Pi1.Topological.MonodromyPath

/-!
# The local monodromy at a branch point bounds the Puiseux index

A Puiseux parametrisation of a cover at a point is produced by following a root of the equation of
the cover around the point in the Kummer coordinate of index `e`, and the construction works as
soon as `e` annihilates the monodromy of the loops of a small punctured disc around the point.
Two conveniences are still missing between that statement and the local monodromy as it is
actually presented.

The first is the basepoint inside the disc.  The construction reads the monodromy at the image of
the Kummer coordinate, whereas the local monodromy is presented at an arbitrary point of the
punctured disc; the two agree because every point of a punctured disc of radius `ρ` is the Kummer
image of a point of the punctured disc of radius `ρ ^ (1/e)`, the `e`-th root being available in
the complex numbers.

The second is the basepoint of the whole punctured plane.  A local monodromy element is the
monodromy of a loop of the punctured plane that winds once around the point, read at a global
basepoint, and it is obtained from a generator of the fundamental group of a small punctured disc
by transport along a path.  Transport conjugates the monodromy representation, so it preserves
exponents, and the exponent of the local monodromy element is an exponent of the monodromy inside
the disc.

## Main results

* `Rigidity.RET.exists_kummerRegionMap_eq` — every point of a punctured disc is the Kummer image
  of a point of a smaller punctured disc.
* `Rigidity.RET.exists_puiseuxEmbedding_of_discMonodromy` — an exponent for the monodromy of a
  generator of a punctured disc around the point gives a Puiseux parametrisation of that index.
* `Rigidity.RET.exists_puiseuxEmbedding_of_isLocalMonodromy` — an exponent for a local monodromy
  element at the point gives a Puiseux parametrisation of that index.
* `Rigidity.RET.LineCover.orderOf_isInertiaAt_le_orderOf_localMonodromy` — the order of the local
  monodromy at the point bounds the order of the inertia there.
* `Rigidity.RET.LineCover.isInertiaGenAt_of_localMonodromy` — an inertia element whose order
  reaches the order of the local monodromy generates its inertia group.
-/

open Polynomial Filter Topology GeomAKLB Rigidity.RET.Analytic

noncomputable section

namespace Rigidity.RET

/-! ### Every point of a punctured disc is a Kummer image -/

/-- **Every point of a punctured disc is the Kummer image of a point of a smaller punctured
disc.**  Extracting an `e`-th root of the displacement from the centre lands in the punctured disc
whose radius is the `e`-th root of the radius. -/
theorem exists_kummerRegionMap_eq {σ : ℂ} {ρ : ℝ} (hρ : 0 < ρ) {e : ℕ} (he : 0 < e)
    (b : ↥(puncturedDisc σ ρ)) :
    ∃ (ρ' : ℝ) (_ : 0 < ρ')
      (hmap : ∀ u ∈ puncturedDisc (0 : ℂ) ρ', σ + u ^ e ∈ puncturedDisc σ ρ)
      (w : ↥(puncturedDisc (0 : ℂ) ρ')), kummerRegionMap σ e hmap w = b := by
  obtain ⟨ρ', hρ', hpow⟩ : ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ^ e = ρ := by
    refine ⟨ρ ^ ((e : ℝ)⁻¹), Real.rpow_pos_of_pos hρ _, ?_⟩
    rw [← Real.rpow_natCast (ρ ^ ((e : ℝ)⁻¹)) e, ← Real.rpow_mul hρ.le,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr he.ne'), Real.rpow_one]
  have hmap : ∀ u ∈ puncturedDisc (0 : ℂ) ρ', σ + u ^ e ∈ puncturedDisc σ ρ :=
    kummer_mem_puncturedDisc he.ne' hpow.le σ
  obtain ⟨hblt, hbne⟩ := mem_puncturedDisc.mp b.2
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq ((b : ℂ) - σ) he
  have hwne : w ≠ 0 := fun h => by
    rw [h, zero_pow he.ne'] at hw
    exact hbne (sub_eq_zero.mp hw.symm)
  have hwlt : ‖w‖ < ρ' := by
    refine lt_of_pow_lt_pow_left₀ e hρ'.le ?_
    rw [← norm_pow, hw, hpow]
    exact hblt
  refine ⟨ρ', hρ', hmap, ⟨w, mem_puncturedDisc.mpr ⟨by rwa [sub_zero], hwne⟩⟩, Subtype.ext ?_⟩
  rw [coe_kummerRegionMap, hw]
  ring

variable {Ω : Type} [Field Ω] [Algebra (RatFunc k) Ω] [Algebra (Polynomial k) Ω]
  [IsScalarTower (Polynomial k) (RatFunc k) Ω] [Algebra k ℂ]

/-! ### An arbitrary basepoint inside the disc -/

/-- **An exponent for the monodromy of a punctured disc around the point gives a Puiseux
parametrisation of that index.**  Unlike the version phrased in the Kummer coordinate, the
basepoint of the disc is arbitrary: it is recovered as a Kummer image. -/
theorem exists_puiseuxEmbedding_of_discMonodromy (s : k) {α : Ω}
    (hα : IsIntegral (Polynomial k) α) (hgen : IntermediateField.adjoin (RatFunc k) {α} = ⊤)
    {S : Finset ℂ} (hS : ∀ z ∉ (S : Set ℂ), (Analytic.spec (complexEquation α) z).Separable)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : puncturedDisc (algebraMap k ℂ s) ρ ⊆ ((S : Set ℂ))ᶜ) {e : ℕ} (he : 0 < e)
    {b : ↥(puncturedDisc (algebraMap k ℂ s) ρ)}
    {g : FundamentalGroup ↥(puncturedDisc (algebraMap k ℂ s) ρ) b}
    (hg : Subgroup.zpowers g = ⊤)
    (hord : ((isCoveringMap_puncturedProj (monic_complexEquation hα) hS).monodromyHom
        (subsetIncl hsub b) (FundamentalGroup.map (subsetIncl hsub) b g)) ^ e = 1) :
    Nonempty (PuiseuxEmbedding Ω ℂ s e) := by
  obtain ⟨ρ', hρ', hmap, w, hw⟩ := exists_kummerRegionMap_eq hρ he b
  subst hw
  exact exists_puiseuxEmbedding_of_orderOf_monodromy s hα hgen hS hρ hρ' hsub he hmap w hg hord

/-! ### The local monodromy at the global basepoint -/

/-- **An exponent for a local monodromy element at the point gives a Puiseux parametrisation of
that index.**  The local monodromy element is the monodromy, read at the basepoint of the
punctured plane, of a loop winding once around the point; transporting the representation back
into the punctured disc where that loop is born preserves its exponents. -/
theorem exists_puiseuxEmbedding_of_isLocalMonodromy (s : k) {α : Ω}
    (hα : IsIntegral (Polynomial k) α) (hgen : IntermediateField.adjoin (RatFunc k) {α} = ⊤)
    {S : Finset ℂ} (hS : ∀ z ∉ (S : Set ℂ), (Analytic.spec (complexEquation α) z).Separable)
    {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ)) {e : ℕ} (he : 0 < e)
    {x : Equiv.Perm (Analytic.puncturedProj (complexEquation α) S ⁻¹'
      {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))})}
    (hx : Analytic.IsLocalMonodromy (monic_complexEquation hα) hS hz₀ (algebraMap k ℂ s) x)
    (hxe : x ^ e = 1) :
    Nonempty (PuiseuxEmbedding Ω ℂ s e) := by
  obtain ⟨γ, ⟨ρ, hincl, b, g, δ, hρ, hgtop, hγ⟩, hxγ⟩ := hx
  subst hγ
  subst hxγ
  set cov := isCoveringMap_puncturedProj (monic_complexEquation hα) hS with hcov
  have key : (cov.monodromyHom (discIncl hincl b)
      (FundamentalGroup.map (discIncl hincl) b g)) ^ e = 1 := by
    refine (cov.monodromyHom_transport_pow_eq_one_iff (Path.Homotopic.Quotient.mk δ) _).mp ?_
    rw [FundamentalGroup.transport_mk]
    exact hxe
  exact exists_puiseuxEmbedding_of_discMonodromy s hα hgen hS hρ hincl he hgtop key

/-! ### The ramification bound -/

/-- **The analytic local monodromy at a point bounds the algebraic inertia there.**  The order of
the local monodromy of the complexified equation of the cover is an index for which a Puiseux
parametrisation exists, and such an index bounds the order of every inertia element. -/
theorem LineCover.orderOf_isInertiaAt_le_orderOf_localMonodromy (L : LineCover) {s : k} {α : L.M}
    (hα : IsIntegral (Polynomial k) α) (hgen : IntermediateField.adjoin (RatFunc k) {α} = ⊤)
    {S : Finset ℂ} (hS : ∀ z ∉ (S : Set ℂ), (Analytic.spec (complexEquation α) z).Separable)
    {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ))
    {x : Equiv.Perm (Analytic.puncturedProj (complexEquation α) S ⁻¹'
      {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))})}
    (hx : Analytic.IsLocalMonodromy (monic_complexEquation hα) hS hz₀ (algebraMap k ℂ s) x)
    {σ : L.deck} (hσ : L.IsInertiaAt s σ) : orderOf σ ≤ orderOf x := by
  haveI : Finite (Analytic.puncturedProj (complexEquation α) S ⁻¹'
      {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}) :=
    (Analytic.finite_puncturedFiber (monic_complexEquation hα) hz₀).to_subtype
  have hpos : 0 < orderOf x := orderOf_pos_iff.mpr (isOfFinOrder_of_finite x)
  exact L.orderOf_le_of_isInertiaAt
    (exists_puiseuxEmbedding_of_isLocalMonodromy (Ω := L.M) s hα hgen hS hz₀ hpos hx
      (pow_orderOf_eq_one x)).some hσ

/-- **An inertia element whose order reaches the order of the local monodromy generates its whole
inertia group.**  Together with the ramification bound this pins the inertia group at the point to
be cyclic of the order of the local monodromy. -/
theorem LineCover.isInertiaGenAt_of_localMonodromy (L : LineCover) {s : k} {α : L.M}
    (hα : IsIntegral (Polynomial k) α) (hgen : IntermediateField.adjoin (RatFunc k) {α} = ⊤)
    {S : Finset ℂ} (hS : ∀ z ∉ (S : Set ℂ), (Analytic.spec (complexEquation α) z).Separable)
    {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ))
    {x : Equiv.Perm (Analytic.puncturedProj (complexEquation α) S ⁻¹'
      {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))})}
    (hx : Analytic.IsLocalMonodromy (monic_complexEquation hα) hS hz₀ (algebraMap k ℂ s) x)
    {σ : L.deck} (hσ : L.IsInertiaAt s σ) (he : orderOf x ≤ orderOf σ) :
    L.IsInertiaGenAt s σ := by
  haveI : Finite (Analytic.puncturedProj (complexEquation α) S ⁻¹'
      {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}) :=
    (Analytic.finite_puncturedFiber (monic_complexEquation hα) hz₀).to_subtype
  have hpos : 0 < orderOf x := orderOf_pos_iff.mpr (isOfFinOrder_of_finite x)
  exact L.isInertiaGenAt_of_puiseux
    (exists_puiseuxEmbedding_of_isLocalMonodromy (Ω := L.M) s hα hgen hS hz₀ hpos hx
      (pow_orderOf_eq_one x)).some hσ he

end Rigidity.RET

end

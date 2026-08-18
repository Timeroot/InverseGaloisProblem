/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.EquationCover

/-!
# A polynomial presentation of a cover of the line

A finite Galois cover of the line with deck group `G`, branched inside a prescribed finite set of
points, can be written down entirely in terms of polynomials over the constant field.  This file
records such a presentation — a `CoverDatum` — and turns one into an actual cover.

The presentation consists of one monic equation `f` in two variables, irreducible over the function
field of the line, whose degree is the order of `G`; a common denominator `den` and numerators
`num g` writing the image of the root under the deck transformation `g` as a polynomial expression
in the root; witnesses that those images are pairwise distinct; a second equation `f₂` for a second
generator of the same cover; and Bézout certificates saying that the two equations are not both
degenerate away from the prescribed points.  Every condition is an identity between polynomials,
which is what makes the presentation travel between fields.

Two equations are used rather than one because a single generator of the cover may well fail to
have a good equation at some point away from the branch locus, while a second generator can be
chosen to be good exactly there; the last Bézout certificate is what expresses that the two
degeneracy loci meet only inside the prescribed set.

## Main definitions

* `Rigidity.RET.CoverDatum` — the polynomial presentation.

## Main results

* `Rigidity.RET.exists_lineCover_of_coverDatum` — a presentation over `ℚ̄` yields a cover of the
  line with deck group `G`, unramified outside the prescribed points.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

open GeomAKLB

/-- A **polynomial presentation** of a Galois cover of the line with deck group `G` whose branch
points lie among `t 0, …, t (r-1)`.

The equation `f` presents the cover, `num g / den` is the image of its root under the deck
transformation `g`, `sepNum` and `sepDen` witness that those images are pairwise distinct, `f₂` is
the equation of a second generator `num₂ / den₂` of the same cover, and the three Bézout
identities certify that at a point outside `t 0, …, t (r-1)` at least one of the two equations
stays separable. -/
structure CoverDatum (F : Type*) [Field F] (G : Type*) [Group G] {r : ℕ} (t : Fin r → F) where
  /-- the equation presenting the cover. -/
  f : Polynomial (Polynomial F)
  /-- the equation is monic. -/
  monic : f.Monic
  /-- its degree is the order of the deck group. -/
  natDegree_eq : f.natDegree = Nat.card G
  /-- the cover is connected. -/
  irreducible : Irreducible (f.map (algebraMap (Polynomial F) (RatFunc F)))
  /-- the common denominator of the deck transformations. -/
  den : Polynomial F
  /-- the common denominator is nonzero. -/
  den_ne : den ≠ 0
  /-- the numerator of the image of the root under the deck transformation `g`. -/
  num : G → Polynomial (Polynomial F)
  /-- each image of the root is again a root of the equation. -/
  num_root : ∀ g, ((f.scaleRoots den).comp (num g)) %ₘ f = 0
  /-- the images compose according to the group law. -/
  num_mul : ∀ g h, ((((num h).scaleRoots den).comp (num g))
    - C den ^ (num h).natDegree * num (g * h)) %ₘ f = 0
  /-- the numerator of the inverse of the difference of two images. -/
  sepNum : G → G → Polynomial (Polynomial F)
  /-- the denominator of the inverse of the difference of two images. -/
  sepDen : G → G → Polynomial F
  /-- that denominator is nonzero. -/
  sepDen_ne : ∀ g h, g ≠ h → sepDen g h ≠ 0
  /-- distinct group elements move the root to distinct places. -/
  sepNum_spec : ∀ g h, g ≠ h →
    ((num g - num h) * sepNum g h - C (sepDen g h)) %ₘ f = 0
  /-- a second equation, for a second generator of the same cover. -/
  f₂ : Polynomial (Polynomial F)
  /-- the second equation is monic. -/
  monic₂ : f₂.Monic
  /-- the denominator of the second generator. -/
  den₂ : Polynomial F
  /-- that denominator is nonzero. -/
  den₂_ne : den₂ ≠ 0
  /-- the numerator of the second generator, as a polynomial in the root of `f`. -/
  num₂ : Polynomial (Polynomial F)
  /-- the second generator satisfies the second equation. -/
  num₂_root : ((f₂.scaleRoots den₂).comp num₂) %ₘ f = 0
  /-- the numerator writing the root of `f` back in terms of the second generator. -/
  back : Polynomial (Polynomial F)
  /-- the corresponding denominator. -/
  backDen : Polynomial F
  /-- that denominator is nonzero. -/
  backDen_ne : backDen ≠ 0
  /-- the second generator generates the cover. -/
  back_spec : (((back.scaleRoots den₂).comp num₂)
    - C (den₂ ^ back.natDegree * backDen) * X) %ₘ f = 0
  /-- the first Bézout cofactor of the equation. -/
  cofA : Polynomial (Polynomial F)
  /-- the second Bézout cofactor of the equation. -/
  cofB : Polynomial (Polynomial F)
  /-- the resulting element of the constant ring, whose zeros carry the degeneracy of `f`. -/
  res : Polynomial F
  /-- the equation and its derivative are coprime up to `res`. -/
  bezout : f * cofA + f.derivative * cofB = C res
  /-- the first Bézout cofactor of the second equation. -/
  cofA₂ : Polynomial (Polynomial F)
  /-- the second Bézout cofactor of the second equation. -/
  cofB₂ : Polynomial (Polynomial F)
  /-- the resulting element of the constant ring, whose zeros carry the degeneracy of `f₂`. -/
  res₂ : Polynomial F
  /-- the second equation and its derivative are coprime up to `res₂`. -/
  bezout₂ : f₂ * cofA₂ + f₂.derivative * cofB₂ = C res₂
  /-- the first cofactor of the last Bézout identity. -/
  locA : Polynomial F
  /-- the second cofactor of the last Bézout identity. -/
  locB : Polynomial F
  /-- the exponent of the last Bézout identity. -/
  expo : ℕ
  /-- the two degeneracies have no common zero outside the prescribed points. -/
  locus : res * locA + res₂ * locB = (∏ i, (X - C (t i))) ^ expo

namespace CoverDatum

variable {F : Type*} [Field F]

/-- **A Bézout identity between an equation and its derivative certifies separability** at every
point where the right-hand side does not vanish. -/
theorem separable_map_of_bezout {p A B : Polynomial (Polynomial F)} {w : Polynomial F}
    (hb : p * A + p.derivative * B = C w) {t₀ : F} (hw : w.eval t₀ ≠ 0) :
    (p.map (evalRingHom t₀)).Separable := by
  have h := congrArg (Polynomial.map (evalRingHom t₀)) hb
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C,
    coe_evalRingHom] at h
  refine ⟨A.map (evalRingHom t₀) * C (w.eval t₀)⁻¹,
    B.map (evalRingHom t₀) * C (w.eval t₀)⁻¹, ?_⟩
  rw [Polynomial.derivative_map]
  calc A.map (evalRingHom t₀) * C (w.eval t₀)⁻¹ * p.map (evalRingHom t₀)
        + B.map (evalRingHom t₀) * C (w.eval t₀)⁻¹ * p.derivative.map (evalRingHom t₀)
      = C (w.eval t₀)⁻¹ * (p.map (evalRingHom t₀) * A.map (evalRingHom t₀)
          + p.derivative.map (evalRingHom t₀) * B.map (evalRingHom t₀)) := by ring
    _ = C (w.eval t₀)⁻¹ * C (w.eval t₀) := by rw [h]
    _ = 1 := by rw [← C_mul, inv_mul_cancel₀ hw, C_1]

/-- Scaling the roots commutes with an injective change of coefficients. -/
theorem map_scaleRoots_of_injective {R S : Type*} [CommRing R] [CommRing S]
    (p : Polynomial R) (s : R) (φ : R →+* S) (hφ : Function.Injective φ) :
    (p.scaleRoots s).map φ = (p.map φ).scaleRoots (φ s) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · refine Polynomial.map_scaleRoots p s φ ?_
    simpa [map_eq_zero_iff φ hφ, Polynomial.leadingCoeff_eq_zero] using hp

/-- **Substituting a fraction into a polynomial with its roots scaled**: if the value of `u` at a
point is the denominator times `y`, then the value of the composite of `u` with the polynomial
whose roots are scaled by that denominator is a power of the denominator times the value of the
polynomial at `y`.  This is how a polynomial identity between numerators expresses an identity
between the fractions they present. -/
theorem aeval_scaleRoots_comp {L : Type*} [CommRing L] [Algebra (RatFunc F) L]
    (p u : Polynomial (Polynomial F)) (s : Polynomial F) (x y : L)
    (hy : aeval x (u.map (algebraMap (Polynomial F) (RatFunc F)))
      = algebraMap (RatFunc F) L (algebraMap (Polynomial F) (RatFunc F) s) * y) :
    aeval x (((p.scaleRoots s).comp u).map (algebraMap (Polynomial F) (RatFunc F)))
      = algebraMap (RatFunc F) L (algebraMap (Polynomial F) (RatFunc F) s) ^ p.natDegree
        * aeval y (p.map (algebraMap (Polynomial F) (RatFunc F))) := by
  have hψinj : Function.Injective (algebraMap (Polynomial F) (RatFunc F)) :=
    IsFractionRing.injective (Polynomial F) (RatFunc F)
  rw [Polynomial.map_comp, map_scaleRoots_of_injective p s _ hψinj, Polynomial.aeval_comp, hy,
    Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.scaleRoots_eval₂_mul,
    Polynomial.natDegree_map_eq_of_injective hψinj]

end CoverDatum

/-! ### From a presentation to a cover -/

section Build

variable {G : Type} [Group G] [Finite G] {r : ℕ} {t : Fin r → k}

open scoped Classical in
/-- **A polynomial presentation over `ℚ̄` is a cover of the line with the prescribed deck group and
branch points.**

The equation defines a field extension of the function field of the line, of the right degree and
connected because the equation is irreducible; the numerators define automorphisms of that
extension, one for each group element, distinct because of the separation witnesses and composing
according to the group law; there are then as many automorphisms as the degree, so the extension is
Galois with the prescribed deck group.  At a point outside the prescribed set one of the two
equations stays separable, and the generator it presents is then fixed by every inertia element
there. -/
theorem exists_lineCover_of_coverDatum (D : CoverDatum k G t) :
    ∃ L : LineCover, Nonempty (L.deck ≃* G) ∧ L.IsUnramifiedOutside (Set.range t) := by
  classical
  haveI := Fintype.ofFinite G
  have hψinj : Function.Injective (algebraMap (Polynomial k) (RatFunc k)) :=
    IsFractionRing.injective (Polynomial k) (RatFunc k)
  set ψ : Polynomial k →+* RatFunc k := algebraMap (Polynomial k) (RatFunc k) with hψdef
  set gf : Polynomial (RatFunc k) := D.f.map ψ with hgfdef
  have hgfm : gf.Monic := D.monic.map ψ
  have hgf0 : gf ≠ 0 := hgfm.ne_zero
  have hgfdeg : gf.natDegree = Nat.card G := by
    rw [hgfdef, D.monic.natDegree_map, D.natDegree_eq]
  haveI hfact : Fact (Irreducible gf) := ⟨D.irreducible⟩
  set x : AdjoinRoot gf := AdjoinRoot.root gf with hxdef
  have hxroot : (aeval x) gf = 0 := by
    rw [hxdef, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  haveI : FiniteDimensional (RatFunc k) (AdjoinRoot gf) := (AdjoinRoot.powerBasis hgf0).finite
  have hfinrank : Module.finrank (RatFunc k) (AdjoinRoot gf) = Nat.card G := by
    rw [(AdjoinRoot.powerBasis hgf0).finrank, AdjoinRoot.powerBasis_dim, hgfdeg]
  -- every identity modulo the equation holds at the root
  have key : ∀ P : Polynomial (Polynomial k), P %ₘ D.f = 0 → (aeval x) (P.map ψ) = 0 := by
    intro P hP
    have h1 : (P.map ψ) %ₘ (D.f.map ψ) = 0 := by
      rw [← Polynomial.map_modByMonic ψ D.monic, hP, Polynomial.map_zero]
    obtain ⟨c, hc⟩ := (Polynomial.modByMonic_eq_zero_iff_dvd (D.monic.map ψ)).mp h1
    rw [← hgfdef] at hc
    rw [hc, map_mul, hxroot, zero_mul]
  -- the homogenized substitutions
  have hscale : ∀ (p u : Polynomial (Polynomial k)) (s : Polynomial k)
      (dd y : AdjoinRoot gf), dd = algebraMap (RatFunc k) (AdjoinRoot gf) (ψ s) →
      (aeval x) (u.map ψ) = dd * y →
      (aeval x) (((p.scaleRoots s).comp u).map ψ) = dd ^ p.natDegree * (aeval y) (p.map ψ) := by
    rintro p u s dd y rfl hy
    exact CoverDatum.aeval_scaleRoots_comp p u s x y hy
  -- the images of the root under the deck transformations
  have hdL0 : algebraMap (RatFunc k) (AdjoinRoot gf) (ψ D.den) ≠ 0 := by
    simp only [Ne, map_eq_zero_iff _ (algebraMap (RatFunc k) (AdjoinRoot gf)).injective,
      map_eq_zero_iff _ hψinj]
    exact D.den_ne
  set dL : AdjoinRoot gf := algebraMap (RatFunc k) (AdjoinRoot gf) (ψ D.den) with hdLdef
  set rr : G → AdjoinRoot gf := fun g => (aeval x) ((D.num g).map ψ) / dL with hrrdef
  have hnum : ∀ g, (aeval x) ((D.num g).map ψ) = dL * rr g := by
    intro g
    rw [hrrdef]
    field_simp
  -- each image is again a root of the equation
  have hrrroot : ∀ g, (aeval (rr g)) gf = 0 := by
    intro g
    have h := key _ (D.num_root g)
    rw [hscale D.f (D.num g) D.den dL (rr g) hdLdef (hnum g), ← hgfdef] at h
    rcases mul_eq_zero.mp h with h0 | h0
    · exact absurd h0 (pow_ne_zero _ hdL0)
    · exact h0
  -- distinct group elements move the root to distinct places
  have hrrinj : Function.Injective rr := by
    intro g h hgh
    by_contra hne
    have hk := key _ (D.sepNum_spec g h hne)
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_C,
      map_sub, map_mul, map_sub, Polynomial.aeval_C, hnum g, hnum h, hgh, sub_self, zero_mul,
      zero_sub, neg_eq_zero] at hk
    exact (D.sepDen_ne g h hne) (hψinj (by
      simpa using (map_eq_zero_iff _ (algebraMap (RatFunc k) (AdjoinRoot gf)).injective).mp hk))
  -- the images compose according to the group law
  have hmul : ∀ g h : G, (aeval (rr g)) ((D.num h).map ψ) = dL * rr (g * h) := by
    intro g h
    have hk := key _ (D.num_mul g h)
    rw [Polynomial.map_sub, map_sub, sub_eq_zero,
      hscale (D.num h) (D.num g) D.den dL (rr g) hdLdef (hnum g), Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_C, map_mul, map_pow, Polynomial.aeval_C, hnum (g * h),
      ← hdLdef] at hk
    exact mul_left_cancel₀ (pow_ne_zero (D.num h).natDegree hdL0) hk
  -- the deck transformations themselves
  set E : G → (AdjoinRoot gf ≃ₐ[RatFunc k] AdjoinRoot gf) := fun g =>
    AlgEquiv.ofBijective
      (AdjoinRoot.liftAlgHom gf (Algebra.ofId (RatFunc k) (AdjoinRoot gf)) (rr g) (hrrroot g))
      (AlgHom.bijective _) with hEdef
  have hEx : ∀ g, E g x = rr g := by
    intro g
    rw [hEdef]
    exact AdjoinRoot.liftAlgHom_root gf (Algebra.ofId (RatFunc k) (AdjoinRoot gf)) (rr g)
      (hrrroot g)
  have hErr : ∀ g h : G, E g (rr h) = rr (g * h) := by
    intro g h
    rw [hrrdef]
    simp only
    rw [map_div₀, ← Polynomial.aeval_algHom_apply, hEx g, hmul g h, hdLdef,
      AlgEquiv.commutes, ← hdLdef, mul_div_cancel_left₀ _ hdL0]
  have hEmul : ∀ g h : G, E (g * h) = E g * E h := by
    intro g h
    have h1 : (E (g * h)).toAlgHom = ((E g * E h : AdjoinRoot gf ≃ₐ[RatFunc k] _)).toAlgHom := by
      refine AlgHom.ext_of_adjoin_eq_top (s := ({x} : Set (AdjoinRoot gf)))
        AdjoinRoot.adjoinRoot_eq_top ?_
      rintro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      show E (g * h) x = (E g * E h) x
      rw [AlgEquiv.mul_apply, hEx, hEx, hErr]
    exact AlgEquiv.ext fun y => AlgHom.congr_fun h1 y
  set Ψ : G →* (AdjoinRoot gf ≃ₐ[RatFunc k] AdjoinRoot gf) := MonoidHom.mk' E hEmul with hΨdef
  have hΨinj : Function.Injective Ψ := by
    intro g h hgh
    refine hrrinj ?_
    rw [← hEx, ← hEx]
    exact congrArg (fun e : AdjoinRoot gf ≃ₐ[RatFunc k] AdjoinRoot gf => e x) hgh
  -- the equation splits, so the extension is Galois
  have hPdeg : (gf.map (algebraMap (RatFunc k) (AdjoinRoot gf))).natDegree = Nat.card G := by
    rw [hgfm.natDegree_map, hgfdeg]
  have hPsub : (Finset.univ.image rr) ⊆
      (gf.map (algebraMap (RatFunc k) (AdjoinRoot gf))).roots.toFinset := by
    intro y hy
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (by
      simpa [Polynomial.map_eq_zero_iff (algebraMap (RatFunc k) (AdjoinRoot gf)).injective]
        using hgf0)]
    exact (Polynomial.eval_map _ _).trans (hrrroot g)
  have hcards : Nat.card G ≤
      Multiset.card (gf.map (algebraMap (RatFunc k) (AdjoinRoot gf))).roots := by
    calc Nat.card G = (Finset.univ.image rr).card := by
          rw [Finset.card_image_of_injective _ hrrinj, Finset.card_univ, Nat.card_eq_fintype_card]
      _ ≤ (gf.map (algebraMap (RatFunc k) (AdjoinRoot gf))).roots.toFinset.card :=
          Finset.card_le_card hPsub
      _ ≤ _ := Multiset.toFinset_card_le _
  have hrootscard :
      Multiset.card (gf.map (algebraMap (RatFunc k) (AdjoinRoot gf))).roots = Nat.card G := by
    have := Polynomial.card_roots' (gf.map (algebraMap (RatFunc k) (AdjoinRoot gf)))
    omega
  have hsplits : (gf.map (algebraMap (RatFunc k) (AdjoinRoot gf))).Splits :=
    Polynomial.splits_iff_card_roots.mpr (by rw [hrootscard, hPdeg])
  have hadjoin : Algebra.adjoin (RatFunc k) (gf.rootSet (AdjoinRoot gf)) = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← AdjoinRoot.adjoinRoot_eq_top (f := gf)]
    exact Algebra.adjoin_mono (by
      simp only [Set.singleton_subset_iff]
      exact Polynomial.mem_rootSet.mpr ⟨hgf0, hxroot⟩)
  haveI hsf : Polynomial.IsSplittingField (RatFunc k) (AdjoinRoot gf) gf := ⟨hsplits, hadjoin⟩
  have hnodup : (gf.map (algebraMap (RatFunc k) (AdjoinRoot gf))).roots.Nodup := by
    rw [← Multiset.toFinset_card_eq_card_iff_nodup]
    refine le_antisymm (Multiset.toFinset_card_le _) ?_
    rw [hrootscard]
    calc Nat.card G = (Finset.univ.image rr).card := by
          rw [Finset.card_image_of_injective _ hrrinj, Finset.card_univ, Nat.card_eq_fintype_card]
      _ ≤ _ := Finset.card_le_card hPsub
  have hsepgf : gf.Separable := by
    rw [← Polynomial.separable_map (algebraMap (RatFunc k) (AdjoinRoot gf))]
    exact (Polynomial.nodup_roots_iff_of_splits (by
      simpa [Polynomial.map_eq_zero_iff (algebraMap (RatFunc k) (AdjoinRoot gf)).injective]
        using hgf0) hsplits).mp hnodup
  haveI : IsGalois (RatFunc k) (AdjoinRoot gf) := IsGalois.of_separable_splitting_field hsepgf
  have hcardaut : Nat.card (AdjoinRoot gf ≃ₐ[RatFunc k] AdjoinRoot gf) = Nat.card G := by
    rw [IsGalois.card_aut_eq_finrank, hfinrank]
  have hΨbij : Function.Bijective Ψ :=
    (Nat.bijective_iff_injective_and_card Ψ).mpr ⟨hΨinj, hcardaut.symm⟩
  -- the generator, and the second generator
  have hgen : IntermediateField.adjoin (RatFunc k) ({x} : Set (AdjoinRoot gf)) = ⊤ := by
    have halg : IsAlgebraic (RatFunc k) x := Algebra.IsAlgebraic.isAlgebraic x
    refine IntermediateField.toSubalgebra_injective ?_
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg,
      IntermediateField.top_toSubalgebra]
    exact AdjoinRoot.adjoinRoot_eq_top
  have hd₂0 : algebraMap (RatFunc k) (AdjoinRoot gf) (ψ D.den₂) ≠ 0 := by
    simp only [Ne, map_eq_zero_iff _ (algebraMap (RatFunc k) (AdjoinRoot gf)).injective,
      map_eq_zero_iff _ hψinj]
    exact D.den₂_ne
  have hb0 : algebraMap (RatFunc k) (AdjoinRoot gf) (ψ D.backDen) ≠ 0 := by
    simp only [Ne, map_eq_zero_iff _ (algebraMap (RatFunc k) (AdjoinRoot gf)).injective,
      map_eq_zero_iff _ hψinj]
    exact D.backDen_ne
  set y : AdjoinRoot gf :=
    (aeval x) (D.num₂.map ψ) / algebraMap (RatFunc k) (AdjoinRoot gf) (ψ D.den₂) with hydef
  have hnum₂ : (aeval x) (D.num₂.map ψ)
      = algebraMap (RatFunc k) (AdjoinRoot gf) (ψ D.den₂) * y := by
    rw [hydef]
    field_simp
  have hyroot : (aeval y) (D.f₂.map ψ) = 0 := by
    have h := key _ D.num₂_root
    rw [hscale D.f₂ D.num₂ D.den₂ _ y rfl hnum₂] at h
    rcases mul_eq_zero.mp h with h0 | h0
    · exact absurd h0 (pow_ne_zero _ hd₂0)
    · exact h0
  have hback : (aeval y) (D.back.map ψ)
      = algebraMap (RatFunc k) (AdjoinRoot gf) (ψ D.backDen) * x := by
    have h := key _ D.back_spec
    rw [Polynomial.map_sub, map_sub, sub_eq_zero,
      hscale D.back D.num₂ D.den₂ _ y rfl hnum₂, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at h
    refine mul_left_cancel₀ (pow_ne_zero D.back.natDegree hd₂0) ?_
    rw [h]
    simp only [map_mul, map_pow]
    ring
  have hgen₂ : IntermediateField.adjoin (RatFunc k) ({y} : Set (AdjoinRoot gf)) = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← hgen]
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have hmem : (aeval y) (D.back.map ψ) ∈
        IntermediateField.adjoin (RatFunc k) ({y} : Set (AdjoinRoot gf)) :=
      IntermediateField.algebra_adjoin_le_adjoin _ _
        (Polynomial.aeval_mem_adjoin_singleton _ _)
    have hbmem : algebraMap (RatFunc k) (AdjoinRoot gf) (ψ D.backDen) ∈
        IntermediateField.adjoin (RatFunc k) ({y} : Set (AdjoinRoot gf)) :=
      IntermediateField.algebraMap_mem _ _
    have : x = (algebraMap (RatFunc k) (AdjoinRoot gf) (ψ D.backDen))⁻¹
        * (aeval y) (D.back.map ψ) := by
      rw [hback, inv_mul_cancel_left₀ hb0]
    rw [this]
    exact mul_mem (inv_mem hbmem) hmem
  -- assemble
  refine ⟨LineCover.of (AdjoinRoot gf), ⟨(MulEquiv.ofBijective Ψ hΨbij).symm⟩, ?_⟩
  intro t₀ ht₀ σ hσ
  have hloc : D.res.eval t₀ * D.locA.eval t₀ + D.res₂.eval t₀ * D.locB.eval t₀ ≠ 0 := by
    have h := congrArg (Polynomial.eval t₀) D.locus
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h
    rw [h]
    refine pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr ?_)
    exact fun hh => ht₀ ⟨i, hh.symm⟩
  rcases (by
    by_contra hcon
    push_neg at hcon
    rw [hcon.1, hcon.2] at hloc
    simp at hloc : D.res.eval t₀ ≠ 0 ∨ D.res₂.eval t₀ ≠ 0) with hres | hres
  · refine (LineCover.of (AdjoinRoot gf)).isUnramifiedAt_of_separable (x := x) hgen D.monic ?_
      (CoverDatum.separable_map_of_bezout D.bezout hres) hσ
    show Polynomial.eval₂ ((algebraMap (RatFunc k) (AdjoinRoot gf)).comp ψ) x D.f = 0
    rw [← Polynomial.eval₂_map, ← hgfdef]
    exact hxroot
  · refine (LineCover.of (AdjoinRoot gf)).isUnramifiedAt_of_separable (x := y) hgen₂ D.monic₂ ?_
      (CoverDatum.separable_map_of_bezout D.bezout₂ hres) hσ
    show Polynomial.eval₂ ((algebraMap (RatFunc k) (AdjoinRoot gf)).comp ψ) y D.f₂ = 0
    rw [← Polynomial.eval₂_map]
    exact hyroot

end Build

end Rigidity.RET

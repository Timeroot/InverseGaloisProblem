/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Transfer.Datum
import InverseGalois.Rigidity.RET.Degeneracy

/-!
# Writing a cover down as a polynomial presentation

A Galois extension of the function field of the line, given by two generators each satisfying a
monic equation with polynomial coefficients, is turned here into a `CoverDatum`: every piece of the
structure — the images of the generator under the group, the witnesses that those images are
pairwise distinct, the passage between the two generators, and the Bézout certificates locating the
degeneracy — is produced from the two equations and the two generators.

The mechanism is uniform.  A generator generates the extension as an algebra, so every element of
the extension is a polynomial expression in it with coefficients rational functions of the
parameter; clearing denominators writes the element as a polynomial expression with polynomial
coefficients divided by a single polynomial in the parameter.  A finite family of elements can be
put over a common denominator.  Conversely a polynomial expression that vanishes at the generator
is divisible by the equation, because the equation is monic and irreducible, hence the minimal
polynomial.  Every field of the presentation is one of these two moves.

The degeneracy of a monic equation is the resultant with its derivative, and the resultant comes
with a Bézout identity by construction; the two degeneracies have no common zero away from the
prescribed points, so their greatest common divisor has all its zeros there and therefore divides a
power of the product of the linear forms vanishing at those points.

## Main results

* `Rigidity.RET.exists_num_den` — an element of a simple extension of the function field of the line
  is a polynomial expression in the generator divided by a polynomial in the parameter.
* `Rigidity.RET.exists_num_den_family` — a finite family of such elements can be put over a common
  denominator.
* `Rigidity.RET.dvd_pow_natDegree_of_roots` — over an algebraically closed field a polynomial
  divides a power of any polynomial vanishing at all of its zeros.
* `Rigidity.RET.exists_coverDatum` — two equations and two generators of a Galois extension of the
  function field of the line, degenerate at no common point outside the prescribed ones, form a
  polynomial presentation of a cover.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

/-! ### Fractions with a common denominator -/

section NumDen

variable {F : Type*} [Field F]

/-- **An element of a simple extension of the function field of the line is a polynomial expression
in the generator, with polynomial coefficients, divided by a polynomial in the parameter.**

The generator generates the extension as an algebra, so the element is a polynomial expression in
it with coefficients rational functions; the finitely many coefficients have a common denominator,
and clearing it leaves polynomial coefficients. -/
theorem exists_num_den {L : Type*} [CommRing L] [Algebra (RatFunc F) L] {α : L}
    (hgen : Algebra.adjoin (RatFunc F) ({α} : Set L) = ⊤) (β : L) :
    ∃ (N : Polynomial (Polynomial F)) (D : Polynomial F), D ≠ 0 ∧
      aeval α (N.map (algebraMap (Polynomial F) (RatFunc F)))
        = algebraMap (RatFunc F) L (algebraMap (Polynomial F) (RatFunc F) D) * β := by
  have hmem : β ∈ (Polynomial.aeval α : Polynomial (RatFunc F) →ₐ[RatFunc F] L).range := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval, hgen]
    exact Algebra.mem_top
  rw [AlgHom.mem_range] at hmem
  obtain ⟨q, hq⟩ := hmem
  obtain ⟨b, hb⟩ :=
    IsLocalization.integerNormalization_map_to_map (nonZeroDivisors (Polynomial F)) q
  refine ⟨IsLocalization.integerNormalization (nonZeroDivisors (Polynomial F)) q,
    (b : Polynomial F),
    nonZeroDivisors.coe_ne_zero b, ?_⟩
  have hsmul : ((b : Polynomial F) • q)
      = C (algebraMap (Polynomial F) (RatFunc F) (b : Polynomial F)) * q := by
    ext i
    rw [coeff_smul, coeff_C_mul, Algebra.smul_def]
  rw [hb, hsmul, map_mul, Polynomial.aeval_C, hq]

/-- **A finite family of elements of a simple extension can be put over a common denominator**: the
product of the individual denominators works, each numerator being multiplied by the denominators
of the other members of the family. -/
theorem exists_num_den_family {L : Type*} [CommRing L] [Algebra (RatFunc F) L] {α : L}
    (hgen : Algebra.adjoin (RatFunc F) ({α} : Set L) = ⊤)
    {ι : Type*} [Fintype ι] (β : ι → L) :
    ∃ (N : ι → Polynomial (Polynomial F)) (D : Polynomial F), D ≠ 0 ∧
      ∀ i, aeval α ((N i).map (algebraMap (Polynomial F) (RatFunc F)))
        = algebraMap (RatFunc F) L (algebraMap (Polynomial F) (RatFunc F) D) * β i := by
  classical
  choose N₀ D₀ hD₀ hN₀ using fun i => exists_num_den hgen (β i)
  refine ⟨fun i => C (∏ j ∈ Finset.univ.erase i, D₀ j) * N₀ i, ∏ j, D₀ j,
    Finset.prod_ne_zero_iff.2 fun j _ => hD₀ j, fun i => ?_⟩
  have hprod : (∏ j ∈ Finset.univ.erase i, D₀ j) * D₀ i = ∏ j, D₀ j :=
    Finset.prod_erase_mul _ _ (Finset.mem_univ i)
  calc aeval α ((C (∏ j ∈ Finset.univ.erase i, D₀ j) * N₀ i).map
        (algebraMap (Polynomial F) (RatFunc F)))
      = algebraMap (RatFunc F) L
            (algebraMap (Polynomial F) (RatFunc F) (∏ j ∈ Finset.univ.erase i, D₀ j))
          * (algebraMap (RatFunc F) L (algebraMap (Polynomial F) (RatFunc F) (D₀ i)) * β i) := by
        rw [Polynomial.map_mul, Polynomial.map_C, map_mul, Polynomial.aeval_C, hN₀ i]
    _ = algebraMap (RatFunc F) L (algebraMap (Polynomial F) (RatFunc F)
          ((∏ j ∈ Finset.univ.erase i, D₀ j) * D₀ i)) * β i := by
        rw [map_mul, map_mul, mul_assoc]
    _ = algebraMap (RatFunc F) L
          (algebraMap (Polynomial F) (RatFunc F) (∏ j, D₀ j)) * β i := by rw [hprod]

/-- **A numerator can be taken monic of the degree of the equation.**

Reducing modulo the monic equation lowers the degree below that of the equation without changing
the value at the root, and adding the equation back makes the result monic of exactly the degree
of the equation, again without changing the value. -/
theorem monic_modByMonic_add {L : Type*} [CommRing L] [Algebra (RatFunc F) L]
    {P : Polynomial (Polynomial F)} (hP : P.Monic) {x : L}
    (hx : aeval x (P.map (algebraMap (Polynomial F) (RatFunc F))) = 0)
    (q : Polynomial (Polynomial F)) :
    (q %ₘ P + P).Monic ∧
      aeval x ((q %ₘ P + P).map (algebraMap (Polynomial F) (RatFunc F)))
        = aeval x (q.map (algebraMap (Polynomial F) (RatFunc F))) := by
  refine ⟨hP.add_of_right (Polynomial.degree_modByMonic_lt q hP), ?_⟩
  rw [Polynomial.modByMonic_eq_sub_mul_div q hP, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, map_add, map_sub, map_mul, hx]
  ring

/-- **Reducing modulo a monic polynomial and adding it back gives its degree.** -/
theorem natDegree_modByMonic_add {P : Polynomial (Polynomial F)} (hP : P.Monic)
    (q : Polynomial (Polynomial F)) : (q %ₘ P + P).natDegree = P.natDegree :=
  Polynomial.natDegree_eq_of_degree_eq
    (Polynomial.degree_add_eq_right_of_degree_lt (Polynomial.degree_modByMonic_lt q hP))

/-- **A constant power factors out of a polynomial expression in the generator.** -/
theorem aeval_C_pow_mul {L : Type*} [CommRing L] [Algebra (RatFunc F) L] (c : Polynomial F) (n : ℕ)
    (P : Polynomial (Polynomial F)) (x : L) :
    aeval x ((C c ^ n * P).map (algebraMap (Polynomial F) (RatFunc F)))
      = algebraMap (RatFunc F) L (algebraMap (Polynomial F) (RatFunc F) c) ^ n
        * aeval x (P.map (algebraMap (Polynomial F) (RatFunc F))) := by
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, map_mul, map_pow,
    Polynomial.aeval_C]

/-- **The difference of two multiples of a nonzero element cancels against its inverse.** -/
theorem sep_cancel {L : Type*} [Field L] (d s u v : L) (h : d * (u - v) ≠ 0) :
    (d * u - d * v) * (s * (d * (u - v))⁻¹) - s = 0 := by
  have hrw : d * u - d * v = d * (u - v) := by ring
  rw [hrw, ← mul_assoc, mul_comm (d * (u - v)) s, mul_assoc, mul_inv_cancel₀ h, mul_one, sub_self]

end NumDen

/-! ### Divisibility from a containment of zeros -/

/-- **Over an algebraically closed field a polynomial divides a power of any polynomial vanishing
at all of its zeros.**  The polynomial is a unit times the product of the linear forms attached to
its zeros; each of those forms divides the other polynomial, and there are at most as many of them
as the degree. -/
theorem dvd_pow_natDegree_of_roots {F : Type*} [Field F] [IsAlgClosed F] {p q : Polynomial F}
    (hp : p ≠ 0) (h : ∀ z, p.eval z = 0 → q.eval z = 0) : p ∣ q ^ p.natDegree := by
  have hsplit : p = C p.leadingCoeff * (p.roots.map (X - C ·)).prod :=
    (IsAlgClosed.splits p).eq_prod_roots
  have hdvd : (p.roots.map (X - C ·)).prod ∣ q ^ Multiset.card p.roots := by
    have hstep := Multiset.prod_dvd_prod_of_dvd (S := p.roots) (fun a => X - C a) (fun _ => q)
      (fun a ha => dvd_iff_isRoot.mpr (h a (isRoot_of_mem_roots ha)))
    rwa [Multiset.map_const', Multiset.prod_replicate] at hstep
  have hdvd' : (p.roots.map (X - C ·)).prod ∣ q ^ p.natDegree :=
    hdvd.trans (pow_dvd_pow q (Polynomial.card_roots' p))
  have hu : IsUnit (C p.leadingCoeff) :=
    isUnit_C.2 (isUnit_iff_ne_zero.2 (Polynomial.leadingCoeff_ne_zero.2 hp))
  nth_rewrite 1 [hsplit]
  exact (IsUnit.mul_left_dvd hu).mpr hdvd'

/-! ### The presentation -/

/-- **Two equations and two generators of a Galois extension of the function field of the line form
a polynomial presentation of a cover**, provided the two equations do not both degenerate at any
point outside the prescribed ones.

Everything is read off from the two generators: the images of the first one under the group, put
over a common denominator, give the deck transformations; the inverses of their differences, put
over a common denominator, witness that they are pairwise distinct; the second generator and the
expression of the first one in terms of it connect the two equations; and the resultant of each
equation with its derivative comes with its Bézout identity, the greatest common divisor of the two
resultants dividing a power of the product of the linear forms attached to the prescribed points. -/
theorem exists_coverDatum {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    {G : Type*} [Group G] [Finite G] {r : ℕ} {t : Fin r → F}
    {L : Type*} [Field L] [Algebra (RatFunc F) L]
    (σ : G →* (L ≃ₐ[RatFunc F] L)) (hσ : Function.Injective σ) (α₁ α₂ : L)
    (P₁ P₂ : Polynomial (Polynomial F)) (hm₁ : P₁.Monic) (hm₂ : P₂.Monic)
    (hn₁ : P₁.natDegree = Nat.card G) (hn₂ : P₂.natDegree = Nat.card G)
    (hirr : Irreducible (P₁.map (algebraMap (Polynomial F) (RatFunc F))))
    (hr₁ : aeval α₁ (P₁.map (algebraMap (Polynomial F) (RatFunc F))) = 0)
    (hr₂ : aeval α₂ (P₂.map (algebraMap (Polynomial F) (RatFunc F))) = 0)
    (hg₁ : IntermediateField.adjoin (RatFunc F) ({α₁} : Set L) = ⊤)
    (hg₂ : IntermediateField.adjoin (RatFunc F) ({α₂} : Set L) = ⊤)
    (hsep : ∀ z ∉ Set.range t, (P₁.map (evalRingHom z)).Separable ∨
      (P₂.map (evalRingHom z)).Separable) :
    Nonempty (CoverDatum F G t) := by
  classical
  haveI := Fintype.ofFinite G
  have hcardpos : 0 < Nat.card G := Nat.card_pos
  have hψinj : Function.Injective (algebraMap (Polynomial F) (RatFunc F)) :=
    IsFractionRing.injective (Polynomial F) (RatFunc F)
  have hΛinj : Function.Injective (algebraMap (RatFunc F) L) :=
    (algebraMap (RatFunc F) L).injective
  have hdeg₁ : 0 < P₁.natDegree := by rw [hn₁]; exact hcardpos
  have hdeg₂ : 0 < P₂.natDegree := by rw [hn₂]; exact hcardpos
  -- the two generators generate as algebras
  have halg₁ : IsAlgebraic (RatFunc F) α₁ :=
    ⟨P₁.map (algebraMap (Polynomial F) (RatFunc F)), (hm₁.map _).ne_zero, hr₁⟩
  have halg₂ : IsAlgebraic (RatFunc F) α₂ :=
    ⟨P₂.map (algebraMap (Polynomial F) (RatFunc F)), (hm₂.map _).ne_zero, hr₂⟩
  have hadj₁ : Algebra.adjoin (RatFunc F) ({α₁} : Set L) = ⊤ := by
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
      (F := RatFunc F) (S := ({α₁} : Set L))
      (fun z hz => by rw [Set.mem_singleton_iff] at hz; subst hz; exact halg₁),
      hg₁, IntermediateField.top_toSubalgebra]
  have hadj₂ : Algebra.adjoin (RatFunc F) ({α₂} : Set L) = ⊤ := by
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
      (F := RatFunc F) (S := ({α₂} : Set L))
      (fun z hz => by rw [Set.mem_singleton_iff] at hz; subst hz; exact halg₂),
      hg₂, IntermediateField.top_toSubalgebra]
  -- an expression vanishing at the generator is divisible by the equation
  have hminpoly : P₁.map (algebraMap (Polynomial F) (RatFunc F)) = minpoly (RatFunc F) α₁ :=
    minpoly.eq_of_irreducible_of_monic hirr hr₁ (hm₁.map _)
  have key : ∀ P : Polynomial (Polynomial F),
      aeval α₁ (P.map (algebraMap (Polynomial F) (RatFunc F))) = 0 → P %ₘ P₁ = 0 := by
    intro P hP
    have hdvd : minpoly (RatFunc F) α₁ ∣ P.map (algebraMap (Polynomial F) (RatFunc F)) :=
      minpoly.dvd _ _ hP
    rw [← hminpoly, ← Polynomial.modByMonic_eq_zero_iff_dvd (hm₁.map _),
      ← Polynomial.map_modByMonic _ hm₁] at hdvd
    refine Polynomial.map_injective _ hψinj ?_
    rw [Polynomial.map_zero]
    exact hdvd
  -- the images of the generator under the group
  have hrrroot : ∀ g : G, aeval (σ g α₁) (P₁.map (algebraMap (Polynomial F) (RatFunc F))) = 0 := by
    intro g
    rw [Polynomial.aeval_algHom_apply, hr₁, map_zero]
  have hrrinj : Function.Injective (fun g : G => σ g α₁) := by
    intro g h hgh
    refine hσ ?_
    have hh : (σ g).toAlgHom = (σ h).toAlgHom := by
      refine AlgHom.ext_of_adjoin_eq_top (s := ({α₁} : Set L)) hadj₁ ?_
      rintro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      simpa using hgh
    exact AlgEquiv.ext fun z => AlgHom.congr_fun hh z
  obtain ⟨nm0, dn, hdn, hnm0⟩ := exists_num_den_family hadj₁ (fun g : G => σ g α₁)
  obtain ⟨nm, hnmmonic, hnmdeg, hnm⟩ : ∃ nm : G → Polynomial (Polynomial F), (∀ g, (nm g).Monic) ∧
      (∀ g, (nm g).natDegree = Nat.card G) ∧
      ∀ g : G, aeval α₁ ((nm g).map (algebraMap (Polynomial F) (RatFunc F)))
        = algebraMap (RatFunc F) L (algebraMap (Polynomial F) (RatFunc F) dn) * σ g α₁ :=
    ⟨fun g => nm0 g %ₘ P₁ + P₁, fun g => (monic_modByMonic_add hm₁ hr₁ (nm0 g)).1,
      fun g => (natDegree_modByMonic_add hm₁ (nm0 g)).trans hn₁,
      fun g => ((monic_modByMonic_add hm₁ hr₁ (nm0 g)).2).trans (hnm0 g)⟩
  have hdn0 : algebraMap (RatFunc F) L (algebraMap (Polynomial F) (RatFunc F) dn) ≠ 0 := by
    simp only [ne_eq, map_eq_zero_iff _ hΛinj, map_eq_zero_iff _ hψinj]
    exact hdn
  -- each image is again a root of the equation
  have hnm_root : ∀ g : G, ((P₁.scaleRoots dn).comp (nm g)) %ₘ P₁ = 0 := by
    intro g
    refine key _ ?_
    rw [CoverDatum.aeval_scaleRoots_comp P₁ (nm g) dn α₁ (σ g α₁) (hnm g), hrrroot g, mul_zero]
  -- the images compose according to the group law
  have hnm_mul : ∀ g h : G, ((((nm h).scaleRoots dn).comp (nm g))
      - C dn ^ (nm h).natDegree * nm (g * h)) %ₘ P₁ = 0 := by
    intro g h
    refine key _ ?_
    have hstep : aeval (σ g α₁) ((nm h).map (algebraMap (Polynomial F) (RatFunc F)))
        = algebraMap (RatFunc F) L (algebraMap (Polynomial F) (RatFunc F) dn) * σ (g * h) α₁ := by
      rw [Polynomial.aeval_algHom_apply, hnm h, map_mul, AlgEquiv.commutes, map_mul,
        AlgEquiv.mul_apply]
    rw [Polynomial.map_sub, map_sub, sub_eq_zero,
      CoverDatum.aeval_scaleRoots_comp (nm h) (nm g) dn α₁ (σ g α₁) (hnm g), hstep,
      aeval_C_pow_mul, hnm (g * h)]
  -- the images are pairwise distinct
  obtain ⟨snm, sdn, hsdn, hsnm⟩ := exists_num_den_family hadj₁
    (fun p : G × G => (algebraMap (RatFunc F) L (algebraMap (Polynomial F) (RatFunc F) dn)
      * (σ p.1 α₁ - σ p.2 α₁))⁻¹)
  have hsnm' : ∀ a b : G, aeval α₁ ((snm (a, b)).map (algebraMap (Polynomial F) (RatFunc F)))
      = algebraMap (RatFunc F) L (algebraMap (Polynomial F) (RatFunc F) sdn)
        * (algebraMap (RatFunc F) L (algebraMap (Polynomial F) (RatFunc F) dn)
          * (σ a α₁ - σ b α₁))⁻¹ := fun a b => hsnm (a, b)
  have hsnm_spec : ∀ g h : G, g ≠ h →
      ((nm g - nm h) * snm (g, h) - C sdn) %ₘ P₁ = 0 := by
    intro g h hgh
    refine key _ ?_
    have hsub : σ g α₁ - σ h α₁ ≠ 0 := sub_ne_zero.2 fun hc => hgh (hrrinj hc)
    have hw : algebraMap (RatFunc F) L (algebraMap (Polynomial F) (RatFunc F) dn)
        * (σ g α₁ - σ h α₁) ≠ 0 := mul_ne_zero hdn0 hsub
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_C,
      map_sub, map_mul, map_sub, Polynomial.aeval_C, hnm g, hnm h, hsnm' g h]
    exact sep_cancel _ _ _ _ hw
  -- the second generator, and the first one written back in terms of it
  obtain ⟨nm2, dn2, hdn2, hnm2⟩ := exists_num_den hadj₁ α₂
  obtain ⟨bk0, bkd, hbkd, hbk0⟩ := exists_num_den hadj₂ α₁
  obtain ⟨bk, hbkmonic, hbkdeg, hbk⟩ : ∃ bk : Polynomial (Polynomial F), bk.Monic ∧
      bk.natDegree = Nat.card G ∧
      aeval α₂ (bk.map (algebraMap (Polynomial F) (RatFunc F)))
        = algebraMap (RatFunc F) L (algebraMap (Polynomial F) (RatFunc F) bkd) * α₁ :=
    ⟨bk0 %ₘ P₂ + P₂, (monic_modByMonic_add hm₂ hr₂ bk0).1,
      (natDegree_modByMonic_add hm₂ bk0).trans hn₂,
      ((monic_modByMonic_add hm₂ hr₂ bk0).2).trans hbk0⟩
  have hnm2_root : ((P₂.scaleRoots dn2).comp nm2) %ₘ P₁ = 0 := by
    refine key _ ?_
    rw [CoverDatum.aeval_scaleRoots_comp P₂ nm2 dn2 α₁ α₂ hnm2, hr₂, mul_zero]
  have hbk_spec : (((bk.scaleRoots dn2).comp nm2)
      - C (dn2 ^ bk.natDegree * bkd) * X) %ₘ P₁ = 0 := by
    refine key _ ?_
    have hrhs : aeval α₁ ((C (dn2 ^ bk.natDegree * bkd) * X).map
          (algebraMap (Polynomial F) (RatFunc F)))
        = algebraMap (RatFunc F) L (algebraMap (Polynomial F) (RatFunc F) dn2) ^ bk.natDegree
          * (algebraMap (RatFunc F) L (algebraMap (Polynomial F) (RatFunc F) bkd) * α₁) := by
      rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, map_mul, Polynomial.aeval_C,
        Polynomial.aeval_X, map_mul, map_pow, map_mul, map_pow, mul_assoc]
    rw [Polynomial.map_sub, map_sub, sub_eq_zero,
      CoverDatum.aeval_scaleRoots_comp bk nm2 dn2 α₁ α₂ hnm2, hbk, hrhs]
  -- the Bézout certificates of the two equations
  obtain ⟨cofA, cofB, -, -, hbez⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant
    P₁ (derivative P₁) (le_refl P₁.natDegree) (Polynomial.natDegree_derivative_le P₁)
    (Or.inl hdeg₁.ne')
  obtain ⟨cofA₂, cofB₂, -, -, hbez₂⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant
    P₂ (derivative P₂) (le_refl P₂.natDegree) (Polynomial.natDegree_derivative_le P₂)
    (Or.inl hdeg₂.ne')
  have hbez' : P₁ * cofA + derivative P₁ * cofB = C (degeneracy P₁) := hbez
  have hbez₂' : P₂ * cofA₂ + derivative P₂ * cofB₂ = C (degeneracy P₂) := hbez₂
  -- the two degeneracies have no common zero away from the prescribed points
  have hcommon : ∀ z : F, (degeneracy P₁).eval z = 0 → (degeneracy P₂).eval z = 0 →
      z ∈ Set.range t := by
    intro z h1 h2
    by_contra hz
    rcases hsep z hz with hs | hs
    · exact ((separable_specialize_iff P₁ hm₁ hdeg₁ z).mp hs) h1
    · exact ((separable_specialize_iff P₂ hm₂ hdeg₂ z).mp hs) h2
  -- some point is outside the prescribed set, so not both degeneracies vanish
  obtain ⟨z₀, hz₀⟩ := ((Set.finite_range t).infinite_compl (α := F)).nonempty
  have hnotboth : ¬ (degeneracy P₁ = 0 ∧ degeneracy P₂ = 0) := by
    rintro ⟨e1, e2⟩
    exact hz₀ (hcommon z₀ (by rw [e1, Polynomial.eval_zero]) (by rw [e2, Polynomial.eval_zero]))
  have hgcd0 : EuclideanDomain.gcd (degeneracy P₁) (degeneracy P₂) ≠ 0 := by
    intro h0
    exact hnotboth (EuclideanDomain.gcd_eq_zero_iff.mp h0)
  have hgcdroots : ∀ z : F, (EuclideanDomain.gcd (degeneracy P₁) (degeneracy P₂)).eval z = 0 →
      (∏ i, (X - C (t i))).eval z = 0 := by
    intro z hz
    obtain ⟨i, hi⟩ := hcommon z
      (by
        obtain ⟨c, hc⟩ := EuclideanDomain.gcd_dvd_left (degeneracy P₁) (degeneracy P₂)
        rw [hc, Polynomial.eval_mul, hz, zero_mul])
      (by
        obtain ⟨c, hc⟩ := EuclideanDomain.gcd_dvd_right (degeneracy P₁) (degeneracy P₂)
        rw [hc, Polynomial.eval_mul, hz, zero_mul])
    rw [Polynomial.eval_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, hi, sub_self]
  obtain ⟨e, he⟩ := dvd_pow_natDegree_of_roots hgcd0 hgcdroots
  have hloc : degeneracy P₁ *
        (EuclideanDomain.gcdA (degeneracy P₁) (degeneracy P₂) * e)
      + degeneracy P₂ * (EuclideanDomain.gcdB (degeneracy P₁) (degeneracy P₂) * e)
      = (∏ i, (X - C (t i))) ^
          (EuclideanDomain.gcd (degeneracy P₁) (degeneracy P₂)).natDegree := by
    rw [he, ← mul_assoc, ← mul_assoc, ← add_mul,
      ← EuclideanDomain.gcd_eq_gcd_ab (degeneracy P₁) (degeneracy P₂)]
  exact ⟨{ f := P₁
           monic := hm₁
           natDegree_eq := hn₁
           irreducible := hirr
           den := dn
           den_ne := hdn
           num := nm
           num_monic := hnmmonic
           num_natDegree := hnmdeg
           num_root := hnm_root
           num_mul := hnm_mul
           sepNum := fun g h => snm (g, h)
           sepDen := fun _ _ => sdn
           sepDen_ne := fun _ _ _ => hsdn
           sepNum_spec := hsnm_spec
           f₂ := P₂
           monic₂ := hm₂
           natDegree₂_eq := hn₂
           den₂ := dn2
           den₂_ne := hdn2
           num₂ := nm2
           num₂_root := hnm2_root
           back := bk
           back_monic := hbkmonic
           back_natDegree := hbkdeg
           backDen := bkd
           backDen_ne := hbkd
           back_spec := hbk_spec
           cofA := cofA
           cofB := cofB
           res := degeneracy P₁
           bezout := hbez'
           cofA₂ := cofA₂
           cofB₂ := cofB₂
           res₂ := degeneracy P₂
           bezout₂ := hbez₂'
           locA := EuclideanDomain.gcdA (degeneracy P₁) (degeneracy P₂) * e
           locB := EuclideanDomain.gcdB (degeneracy P₁) (degeneracy P₂) * e
           expo := (EuclideanDomain.gcd (degeneracy P₁) (degeneracy P₂)).natDegree
           locus := hloc }⟩

end Rigidity.RET

end

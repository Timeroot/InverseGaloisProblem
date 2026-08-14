/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.ClearDenom
import InverseGalois.Rigidity.RET.Analytic.DeckPolyMul
import InverseGalois.Rigidity.RET.Analytic.IntegralDeck
import InverseGalois.Rigidity.RET.Analytic.DeckCycles
import InverseGalois.Rigidity.RET.Analytic.Shrink

/-!
# From a Galois group to a group of root formulas

The automorphisms of a simple extension of a field of fractions are polynomials modulo the
minimal polynomial.  Clearing all their denominators at once turns them into polynomials over the
base ring divided by one common element of that ring, and the three identities they satisfy —
carrying roots to roots, the identity element, the composition law — become divisibilities in the
base ring.  Two different automorphisms are separated by a Bézout identity, and the minimal
polynomial is separated from its derivative by another; clearing those too, all the exceptional
behaviour is concentrated in the vanishing of a single element of the base ring.

Over the ring of complex polynomials the exceptional element vanishes at finitely many points, so
outside a finite set of parameters the automorphism group has become a group of continuous
formulas permuting the roots of the family: a `Rigidity.RET.Analytic.IntegralDeck`.

## Main results

* `Rigidity.RET.exists_deck_formulas` — the automorphism group as formulas over the base ring.
* `Rigidity.RET.Analytic.exists_integralDeck` — over complex polynomials, the resulting group of
  root formulas, together with a finite set of parameters outside of which the family is
  separable.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

/-! ### The automorphism group as formulas over the base ring -/

section General

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- **The automorphisms of a simple extension of a field of fractions, written as formulas over
the base ring.**  The numerators `num g`, the common denominator `den`, and the single exceptional
element `bad` carry the whole group structure: the formulas permute the roots of `P`, the identity
element acts trivially, composing formulas multiplies group elements, different group elements are
separated, and `P` is separated from its derivative — all by identities in the base ring, so all
of them survive every evaluation at which `bad` does not vanish. -/
theorem exists_deck_formulas {P : Polynomial R} (hP : P.Monic)
    {L : Type*} [Field L] [Algebra K L] [Finite (L ≃ₐ[K] L)] {α : L}
    (hirr : Irreducible (P.map (algebraMap R K)))
    (hsep : (P.map (algebraMap R K)).Separable)
    (hα : aeval α (P.map (algebraMap R K)) = 0)
    (hgen : ∀ β : L, ∃ q : Polynomial K, aeval α q = β) :
    ∃ (num : (L ≃ₐ[K] L) → Polynomial R) (den bad : R),
      bad ≠ 0 ∧ den ∣ bad ∧
      (∀ g, P ∣ scaledComp P (num g) den) ∧
      P ∣ num 1 - C den * X ∧
      (∀ g h, P ∣ scaledComp (num g) (num h) den
        - C (den ^ (num g).natDegree) * num (g * h)) ∧
      (∀ g h, g ≠ h → ∃ A B : Polynomial R, A * P + B * (num g - num h) = C bad) ∧
      (∃ A B : Polynomial R, A * P + B * derivative P = C bad) := by
  classical
  letI : Fintype (L ≃ₐ[K] L) := Fintype.ofFinite _
  have hφinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hPk : (P.map (algebraMap R K)).Monic := hP.map _
  obtain ⟨d, N, hd, hN⟩ := exists_common_denom (R := R) (K := K)
    (fun g : L ≃ₐ[K] L => autPoly (P.map (algebraMap R K)) hgen g⁻¹)
  have hdK : (algebraMap R K) d ≠ 0 := fun hz => hd ((map_eq_zero_iff _ hφinj).mp hz)
  have hNq : ∀ g : L ≃ₐ[K] L,
      C ((algebraMap R K) d)⁻¹ * (N g).map (algebraMap R K)
        = autPoly (P.map (algebraMap R K)) hgen g⁻¹ := by
    intro g
    rw [hN g, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hdK, C_1, one_mul]
  -- the formulas carry roots to roots
  have hroot : ∀ g : L ≃ₐ[K] L, P ∣ scaledComp P (N g) d := by
    intro g
    refine dvd_scaledComp (algebraMap R K) hφinj hP hdK ?_
    rw [hNq g]
    exact dvd_comp_autPoly hgen hPk hirr hα _
  -- the identity element acts trivially
  have hone : P ∣ N 1 - C d * X := by
    rw [← Polynomial.map_dvd_map (algebraMap R K) hφinj hP, Polynomial.map_sub,
      Polynomial.map_mul, map_C, Polynomial.map_X, hN 1, inv_one]
    have hfac : ∀ A : Polynomial K,
        C ((algebraMap R K) d) * A - C ((algebraMap R K) d) * X
          = C ((algebraMap R K) d) * (A - X) := fun A => by ring
    rw [hfac]
    exact (dvd_autPoly_one hgen hPk hirr hα).mul_left _
  -- composing formulas multiplies group elements
  have hmul : ∀ g h : L ≃ₐ[K] L,
      P ∣ scaledComp (N g) (N h) d - C (d ^ (N g).natDegree) * N (g * h) := by
    intro g h
    rw [← Polynomial.map_dvd_map (algebraMap R K) hφinj hP, Polynomial.map_sub,
      map_scaledComp (algebraMap R K) (N g) (N h) hdK, Polynomial.map_mul, map_C, map_pow,
      C_pow, hNq h, hN g, hN (g * h), mul_inv_rev, mul_comp, C_comp]
    have hfac : ∀ A B : Polynomial K,
        C ((algebraMap R K) d) ^ (N g).natDegree * (C ((algebraMap R K) d) * A)
          - C ((algebraMap R K) d) ^ (N g).natDegree * (C ((algebraMap R K) d) * B)
          = C ((algebraMap R K) d) ^ (N g).natDegree * C ((algebraMap R K) d) * (A - B) :=
      fun A B => by ring
    rw [hfac]
    exact (dvd_autPoly_mul hgen hPk hirr hα g⁻¹ h⁻¹).mul_left _
  -- `P` is separated from its derivative
  obtain ⟨A₀s, B₀s, hABs⟩ := hsep
  obtain ⟨As, Bs, cs, hcs, hids⟩ :=
    exists_bezout_clear (R := R) (K := K) (f₁ := P) (f₂ := derivative P) one_ne_zero A₀s B₀s (by
      rw [← Polynomial.derivative_map, map_one, C_1]
      exact hABs)
  -- different group elements are separated
  have hpair : ∀ g h : L ≃ₐ[K] L, ∃ (A B : Polynomial R) (c : R), c ≠ 0 ∧
      (g ≠ h → A * P + B * (N g - N h) = C c) := by
    intro g h
    by_cases hgh : g = h
    · exact ⟨0, 0, 1, one_ne_zero, fun hne => absurd hgh hne⟩
    · obtain ⟨A₀, B₀, hAB⟩ := isCoprime_autPoly_sub hgen hPk hirr hα
        (show g⁻¹ ≠ h⁻¹ from fun he => hgh (inv_injective he))
      obtain ⟨A, B, c, hc, hid⟩ :=
        exists_bezout_clear (R := R) (K := K) (f₁ := P) (f₂ := N g - N h) hd
          (C ((algebraMap R K) d) * A₀) B₀ (by
            rw [Polynomial.map_sub, hN g, hN h]
            have hfac : C ((algebraMap R K) d) * A₀ * P.map (algebraMap R K)
                + B₀ * (C ((algebraMap R K) d) * autPoly (P.map (algebraMap R K)) hgen g⁻¹
                  - C ((algebraMap R K) d) * autPoly (P.map (algebraMap R K)) hgen h⁻¹)
                = C ((algebraMap R K) d) * (A₀ * P.map (algebraMap R K)
                  + B₀ * (autPoly (P.map (algebraMap R K)) hgen g⁻¹
                    - autPoly (P.map (algebraMap R K)) hgen h⁻¹)) := by ring
            rw [hfac, hAB, mul_one])
      exact ⟨A, B, c, hc, fun _ => hid⟩
  choose A B c hc hid using hpair
  refine ⟨N, d, d * cs * ∏ p : (L ≃ₐ[K] L) × (L ≃ₐ[K] L), c p.1 p.2,
    mul_ne_zero (mul_ne_zero hd hcs) (Finset.prod_ne_zero_iff.mpr fun p _ => hc p.1 p.2),
    dvd_mul_of_dvd_left (dvd_mul_right d cs) _, hroot, hone, hmul, ?_, ?_⟩
  · intro g h hgh
    obtain ⟨m, hm⟩ : c g h ∣ d * cs * ∏ p : (L ≃ₐ[K] L) × (L ≃ₐ[K] L), c p.1 p.2 :=
      Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun p => c p.1 p.2) (Finset.mem_univ (g, h))) _
    refine ⟨C m * A g h, C m * B g h, ?_⟩
    have hfac : C m * A g h * P + C m * B g h * (N g - N h)
        = C m * (A g h * P + B g h * (N g - N h)) := by ring
    rw [hfac, hid g h hgh, ← C_mul, mul_comm m (c g h), ← hm]
  · obtain ⟨m, hm⟩ : cs ∣ d * cs * ∏ p : (L ≃ₐ[K] L) × (L ≃ₐ[K] L), c p.1 p.2 :=
      Dvd.dvd.mul_right (dvd_mul_left cs d) _
    refine ⟨C m * As, C m * Bs, ?_⟩
    have hfac : C m * As * P + C m * Bs * derivative P
        = C m * (As * P + Bs * derivative P) := by ring
    rw [hfac, hids, ← C_mul, mul_comm m cs, ← hm]

end General

/-! ### Over complex polynomials -/

namespace Analytic

/-- The zeros of a polynomial, as a finite set. -/
def badSet (b : Polynomial ℂ) : Finset ℂ := b.roots.toFinset

theorem eval_ne_zero_of_notMem_badSet {b c : Polynomial ℂ} (hb : b ≠ 0) (hdvd : c ∣ b) {z : ℂ}
    (hz : z ∉ (badSet b : Set ℂ)) : c.eval z ≠ 0 := by
  intro hc
  obtain ⟨m, hm⟩ := hdvd
  refine hz ?_
  have hbz : b.IsRoot z := by rw [Polynomial.IsRoot, hm, eval_mul, hc, zero_mul]
  simpa [badSet, Polynomial.mem_roots', hb] using hbz

/-- **A Bézout identity with a nonzero constant right-hand side witnesses separability.** -/
theorem separable_of_bezout {f a b : Polynomial ℂ} {u : ℂ} (hu : u ≠ 0)
    (h : a * f + b * derivative f = C u) : f.Separable := by
  refine ⟨C u⁻¹ * a, C u⁻¹ * b, ?_⟩
  rw [mul_assoc, mul_assoc, ← mul_add, h, ← C_mul, inv_mul_cancel₀ hu, C_1]

/-- **Away from the zeros of the constant, every specialization of the family is separable.** -/
theorem separable_spec_of_bezout {P A B : Polynomial (Polynomial ℂ)} {cs : Polynomial ℂ}
    (h : A * P + B * derivative P = C cs) {z : ℂ} (hz : cs.eval z ≠ 0) :
    (spec P z).Separable := by
  have hmap := congrArg (Polynomial.map (Polynomial.evalRingHom z)) h
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, map_C,
    ← Polynomial.derivative_map] at hmap
  exact separable_of_bezout hz hmap

/-- **A Galois extension of the complex rational function field, read as a group of root
formulas.**  Outside a finite set of parameters the family is separable and the automorphism
group acts on its roots by continuous formulas. -/
theorem exists_integralDeck {P : Polynomial (Polynomial ℂ)} (hP : P.Monic)
    {L : Type} [Field L] [Algebra (RatFunc ℂ) L] [Finite (L ≃ₐ[RatFunc ℂ] L)] {α : L}
    (hirr : Irreducible (P.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))))
    (hα : aeval α (P.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))) = 0)
    (hgen : ∀ β : L, ∃ q : Polynomial (RatFunc ℂ), aeval α q = β) :
    ∃ S : Finset ℂ, (∀ z ∉ (S : Set ℂ), (spec P z).Separable) ∧
      Nonempty (IntegralDeck P S (L ≃ₐ[RatFunc ℂ] L)) := by
  obtain ⟨num, den, bad, hbad, hdvdden, hroot, hone, hmul, hsepp, As, Bs, hids⟩ :=
    exists_deck_formulas hP hirr hirr.separable hα hgen
  refine ⟨badSet bad, fun z hz => separable_spec_of_bezout hids
    (eval_ne_zero_of_notMem_badSet hbad dvd_rfl hz), ⟨?_⟩⟩
  exact
    { num := num
      den := den
      den_ne := fun z hz => eval_ne_zero_of_notMem_badSet hbad hdvdden hz
      dvd_root := hroot
      dvd_one := hone
      dvd_mul := hmul
      sep := fun g h hgh => by
        obtain ⟨A, B, hAB⟩ := hsepp g h hgh
        exact ⟨A, B, bad, fun z hz => eval_ne_zero_of_notMem_badSet hbad dvd_rfl hz, hAB⟩ }

/-- **A Galois extension of the complex rational function field has a branch-cycle system.**

The parameters at which the presenting family degenerates carry one group element each, and one
more stands for infinity; the elements multiply to one and generate the whole group.  The set of
parameters is not an artefact of the presentation of the extension: it is exactly the set at which
the equation acquires a repeated root. -/
theorem exists_branchCycles_of_galois {P : Polynomial (Polynomial ℂ)} (hP : P.Monic)
    (hdeg : 0 < P.natDegree)
    {L : Type} [Field L] [Algebra (RatFunc ℂ) L] [Finite (L ≃ₐ[RatFunc ℂ] L)] {α : L}
    (hirr : Irreducible (P.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))))
    (hα : aeval α (P.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))) = 0)
    (hgen : ∀ β : L, ∃ q : Polynomial (RatFunc ℂ), aeval α q = β)
    (hcard : Nat.card (L ≃ₐ[RatFunc ℂ] L) = P.natDegree) :
    ∃ S : Finset ℂ, (S : Set ℂ) = degenLocus P ∧
      ∃ g : Fin (S.card + 1) → (L ≃ₐ[RatFunc ℂ] L),
        (List.ofFn g).prod = 1 ∧ Subgroup.closure (Set.range g) = ⊤ := by
  have hirrP : Irreducible P :=
    (hP.isPrimitive.irreducible_iff_irreducible_map_fraction_map (K := RatFunc ℂ)).mpr hirr
  obtain ⟨S, hS, ⟨D⟩⟩ := exists_integralDeck hP hirr hα hgen
  exact D.toRationalDeck.exists_branchCycles_eq_degen hP hdeg hirrP hS hcard

end Analytic

end Rigidity.RET

end

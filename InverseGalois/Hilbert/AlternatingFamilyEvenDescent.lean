/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Hilbert.Analytic.SerreBaseCover
import InverseGalois.Hilbert.AlternatingFamilyDisc
import InverseGalois.Resolvent.ResolventFamily
import InverseGalois.Hilbert.Analytic.Luroth

/-!
# Base-change machinery for the even-`n` `Aₙ` descent

This file provides the "base-change machinery" that transports the shared Serre base cover
`serreBaseGeomPoly n` (over `GeomBase = ℚ̄(T)`) to Serre's even-`n` alternating family
`serreAnFamily n` through the **quadratic substitution** `S ↦ -1/(n-1) - (-1)^{n/2}·T²`.

Writing `ℚ̄ := AlgebraicClosure ℚ`, `R := ℚ̄[X]`, and `t := algebraMap R GeomBase X`
(the transcendental generator of `GeomBase`), the three deliverables are:

* `substFieldHomEven n : BaseT →+* GeomBase` — the field hom induced by the quadratic substitution
  `X ↦ C(-1/(n-1)) + C(-(-1)^{n/2})·X²` on `R`, together with the algebra structure
  `algBaseT n : Algebra BaseT GeomBase` it carries.
* `serreBaseGeomPoly_map_substFieldHomEven` — the base-change identity
  `(serreBaseGeomPoly n).map (substFieldHomEven n) = (serreAnFamily n).map toClosureFrac`.
* `finrank_baseT_geomBase` — the degree of the resulting field extension is `2`.
-/

open Polynomial
open SerreBaseCover
open AlternatingFamily
open ResolventFamily

noncomputable section

namespace AlternatingFamily

namespace EvenDescent

/-- Type synonym for the "T-copy" of the geometric base field `ℚ̄(T)`.

We transport the field/algebra/fraction-ring instances from `GeomBase` via `inferInstanceAs`,
keeping a single instance path (avoiding a diamond between a freshly-derived `Field BaseT` and the
defeq `Field GeomBase`). -/
def BaseT : Type := FractionRing (Polynomial (AlgebraicClosure ℚ))

noncomputable instance : Field BaseT := inferInstanceAs (Field GeomBase)

instance : CharZero BaseT := inferInstanceAs (CharZero GeomBase)

noncomputable instance : Algebra (Polynomial (AlgebraicClosure ℚ)) BaseT :=
  inferInstanceAs (Algebra (Polynomial (AlgebraicClosure ℚ)) GeomBase)

instance : IsFractionRing (Polynomial (AlgebraicClosure ℚ)) BaseT :=
  inferInstanceAs (IsFractionRing (Polynomial (AlgebraicClosure ℚ)) GeomBase)

/-- The even quadratic substitution `X ↦ C(-1/(n-1)) + C(-(-1)^{n/2})·X²` on `ℚ̄[X]`, as a
ring endomorphism.  The coefficients are chosen so the base-change identity
`serreBaseGeomPoly_map_substFieldHomEven` holds:
the constant term is `-1/(n-1)` and the `X²`-coefficient is `-(-1)^{n/2}`. -/
def substPolyEven (n : ℕ) :
    Polynomial (AlgebraicClosure ℚ) →+* Polynomial (AlgebraicClosure ℚ) :=
  (Polynomial.aeval
    (C (-1 / ((n : AlgebraicClosure ℚ) - 1))
      + C (-((-1 : AlgebraicClosure ℚ) ^ (n / 2))) * X ^ 2
      : Polynomial (AlgebraicClosure ℚ))).toRingHom

/-- `substPolyEven n` fixes the constants `C c`. -/
@[simp] theorem substPolyEven_C (n : ℕ) (c : AlgebraicClosure ℚ) :
    substPolyEven n (C c) = C c := by
  simp [substPolyEven]

/-- `substPolyEven n` sends the generator `X` to the substitution polynomial. -/
@[simp] theorem substPolyEven_X (n : ℕ) :
    substPolyEven n X
      = C (-1 / ((n : AlgebraicClosure ℚ) - 1))
        + C (-((-1 : AlgebraicClosure ℚ) ^ (n / 2))) * X ^ 2 := by
  simp [substPolyEven]

/-- The `X²`-coefficient `-(-1)^{n/2}` of the substitution is nonzero. -/
theorem substPolyEven_c2_ne_zero (n : ℕ) :
    -((-1 : AlgebraicClosure ℚ) ^ (n / 2)) ≠ 0 :=
  neg_ne_zero.mpr (pow_ne_zero _ (by norm_num))

/-- Substitution by the degree-`2` polynomial is injective (`Polynomial.comp_eq_zero_iff`). -/
theorem substPolyEven_injective (n : ℕ) : Function.Injective (substPolyEven n) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  set v : Polynomial (AlgebraicClosure ℚ) :=
    C (-1 / ((n : AlgebraicClosure ℚ) - 1))
      + C (-((-1 : AlgebraicClosure ℚ) ^ (n / 2))) * X ^ 2 with hv
  have hconv : substPolyEven n p = p.comp v := by
    rw [substPolyEven, comp_eq_aeval]
    rfl
  rw [hconv] at hp
  rcases comp_eq_zero_iff.mp hp with h | ⟨_, hq2⟩
  · exact h
  · have hnd : v.natDegree = 2 := by
      rw [hv]
      compute_degree!
    rw [hq2, natDegree_C] at hnd
    exact absurd hnd (by norm_num)

/-- The field hom `BaseT →+* GeomBase` induced by the even quadratic substitution, via
functoriality of the fraction-ring construction (`IsFractionRing.map`). -/
noncomputable def substFieldHomEven (n : ℕ) : BaseT →+* GeomBase :=
  IsFractionRing.map (A := Polynomial (AlgebraicClosure ℚ))
    (B := Polynomial (AlgebraicClosure ℚ)) (substPolyEven_injective n)

/-- `substFieldHomEven` is injective (a ring hom out of a field). -/
theorem substFieldHomEven_injective (n : ℕ) : Function.Injective (substFieldHomEven n) :=
  (substFieldHomEven n).injective

/-- `substFieldHomEven` intertwines `algebraMap R GeomBase` with `substPolyEven`
(`IsLocalization.map_eq`). -/
theorem substFieldHomEven_algebraMap (n : ℕ)
    (x : Polynomial (AlgebraicClosure ℚ)) :
    substFieldHomEven n
        (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase x)
      = algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase (substPolyEven n x) := by
  simp only [substFieldHomEven, IsFractionRing.map]
  exact IsLocalization.map_eq _ _

/-- The algebra structure on `GeomBase` over `BaseT` carried by the even substitution.

Because it depends on `n`, we expose it as a `def` (not a global `instance`); downstream callers
should introduce it with `letI := algBaseT n`.  With this structure
`algebraMap BaseT GeomBase = substFieldHomEven n` holds definitionally. -/
noncomputable def algBaseT (n : ℕ) : Algebra BaseT GeomBase := (substFieldHomEven n).toAlgebra

/-- With `algBaseT n`, `algebraMap BaseT GeomBase = substFieldHomEven n`. -/
theorem algebraMap_baseT_eq (n : ℕ) :
    letI := algBaseT n
    algebraMap BaseT GeomBase = substFieldHomEven n := rfl

/-- `substFieldHomEven` fixes the `ℚ̄`-constants `algebraMap R GeomBase (C c)`. -/
theorem substFieldHomEven_C (n : ℕ) (c : AlgebraicClosure ℚ) :
    substFieldHomEven n (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase (C c))
      = algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase (C c) := by
  rw [substFieldHomEven_algebraMap, substPolyEven_C]

/-- `substFieldHomEven` sends the transcendental generator `t = algebraMap R GeomBase X` to
`algebraMap R GeomBase (C c₀ + C c₂·X²)`, i.e. `c₀ + c₂·t²`. -/
theorem substFieldHomEven_X (n : ℕ) :
    substFieldHomEven n (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X)
      = algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase
          (C (-1 / ((n : AlgebraicClosure ℚ) - 1))
            + C (-((-1 : AlgebraicClosure ℚ) ^ (n / 2))) * X ^ 2) := by
  rw [substFieldHomEven_algebraMap, substPolyEven_X]

/-! ## Deliverable 2 — the base-change identity -/

/-- **Base-change identity.**  The shared Serre base cover, base-changed along the even quadratic
substitution, is Serre's even alternating family base-changed to `ℚ̄(T)`. -/
theorem serreBaseGeomPoly_map_substFieldHomEven (n : ℕ) (_hn : 3 ≤ n) :
    (serreBaseGeomPoly n).map (substFieldHomEven n)
      = (serreAnFamily n).map toClosureFrac := by
  -- Reduce to a polynomial identity over `R = ℚ̄[X]`.
  have key : (linearCoverC (serreBaseP n)).map (substPolyEven n)
      = (serreAnFamily n).map
          (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ))) := by
    rw [linearCoverC, serreBaseP, serreAnFamily]
    simp only [Polynomial.coe_mapRingHom, Polynomial.map_sub, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      substPolyEven_C, substPolyEven_X]
    simp only [map_div₀, map_natCast, map_sub, map_one, map_pow, map_neg]
    simp only [Polynomial.C_add, Polynomial.C_neg, Polynomial.C_mul,
      Polynomial.C_pow, Polynomial.C_1]
    rw [neg_div, C_neg, C_neg]
    ring
  -- Assemble: both sides are `(·).map (algebraMap R GeomBase)`.
  have hcomp : (substFieldHomEven n).comp
        (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase)
      = (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase).comp (substPolyEven n) :=
    RingHom.ext (substFieldHomEven_algebraMap n)
  rw [serreBaseGeomPoly, linearCoverGeom, map_map, hcomp, ← map_map, key, map_map]
  rfl

/-! ## Deliverable 3 — the degree-`2` field extension -/

set_option synthInstance.maxHeartbeats 200000 in
/-- The square of the transcendental generator `t = algebraMap R GeomBase X` lies in the image of
`BaseT` (equivalently, `t² ∈ ℚ̄(t²)`): explicitly `t² = algebraMap BaseT GeomBase β` for
`β = (X - C c₀) / C c₂` (with `c₀ = -1/(n-1)`, `c₂ = -(-1)^{n/2} ≠ 0`), because
`substFieldHomEven` sends `t` to `c₀ + c₂·t²`. -/
theorem gen_sq_mem_range (n : ℕ) :
    letI := algBaseT n
    ∃ β : BaseT, algebraMap BaseT GeomBase β
      = (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X) ^ 2 := by
  letI := algBaseT n
  refine ⟨(algebraMap (Polynomial (AlgebraicClosure ℚ)) BaseT X
        - algebraMap (Polynomial (AlgebraicClosure ℚ)) BaseT
            (C (-1 / ((n : AlgebraicClosure ℚ) - 1))))
      * (algebraMap (Polynomial (AlgebraicClosure ℚ)) BaseT
          (C (-((-1 : AlgebraicClosure ℚ) ^ (n / 2)))))⁻¹, ?_⟩
  show substFieldHomEven n _ = _
  rw [map_mul, map_sub, map_inv₀,
    show substFieldHomEven n
        (algebraMap (Polynomial (AlgebraicClosure ℚ)) BaseT X)
      = algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase
          (C (-1 / ((n : AlgebraicClosure ℚ) - 1))
            + C (-((-1 : AlgebraicClosure ℚ) ^ (n / 2))) * X ^ 2)
      from substFieldHomEven_X n,
    show substFieldHomEven n
        (algebraMap (Polynomial (AlgebraicClosure ℚ)) BaseT
          (C (-1 / ((n : AlgebraicClosure ℚ) - 1))))
      = algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase
          (C (-1 / ((n : AlgebraicClosure ℚ) - 1)))
      from substFieldHomEven_C n _,
    show substFieldHomEven n
        (algebraMap (Polynomial (AlgebraicClosure ℚ)) BaseT
          (C (-((-1 : AlgebraicClosure ℚ) ^ (n / 2)))))
      = algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase
          (C (-((-1 : AlgebraicClosure ℚ) ^ (n / 2))))
      from substFieldHomEven_C n _]
  rw [map_add, map_mul, map_pow]
  field_simp
  ring

/-! ### Helper lemmas for the degree-`2` computation

The proof is the self-contained "sign automorphism + adjoin" route: `t = algebraMap R GeomBase X`
is integral of degree `≤ 2` over `BaseT` (root of the monic `X² - C β`), generates `GeomBase`
(`adjoin BaseT {t} = ⊤`), and is *not* in the base (the `X ↦ -X` automorphism `σ` fixes the image of
`substFieldHomEven` but sends `t ↦ -t ≠ t`), so the minimal polynomial has degree exactly `2`. -/

/-- The `X ↦ -X` ring endomorphism of `ℚ̄[X]`. -/
private noncomputable def signPolyHom :
    Polynomial (AlgebraicClosure ℚ) →+* Polynomial (AlgebraicClosure ℚ) :=
  (Polynomial.aeval (-X : Polynomial (AlgebraicClosure ℚ))).toRingHom

private theorem signPolyHom_apply (p : Polynomial (AlgebraicClosure ℚ)) :
    signPolyHom p = p.comp (-X) := by
  rw [signPolyHom, comp_eq_aeval]
  rfl

private theorem signPolyHom_involutive : Function.Involutive signPolyHom := by
  intro p
  rw [signPolyHom_apply, signPolyHom_apply, comp_assoc]
  simp only [neg_comp, X_comp, neg_neg, comp_X]

/-- `signPolyHom` fixes the substitution polynomial `substPolyEven n x`, because the latter is a
polynomial in `X²` (the substitution `C c₀ + C c₂·X²` is even). -/
private theorem signPolyHom_substPolyEven (n : ℕ) (x : Polynomial (AlgebraicClosure ℚ)) :
    signPolyHom (substPolyEven n x) = substPolyEven n x := by
  set v : Polynomial (AlgebraicClosure ℚ) :=
    C (-1 / ((n : AlgebraicClosure ℚ) - 1))
      + C (-((-1 : AlgebraicClosure ℚ) ^ (n / 2))) * X ^ 2 with hv
  have hconv : substPolyEven n x = x.comp v := by
    rw [substPolyEven, comp_eq_aeval]
    rfl
  rw [hconv, signPolyHom_apply, comp_assoc]
  congr 1
  rw [hv]
  simp only [add_comp, mul_comp, C_comp, pow_comp, X_comp, neg_sq]

/-- The `X ↦ -X` field automorphism of `GeomBase = ℚ̄(X)`. -/
private noncomputable def signFieldHom : GeomBase →+* GeomBase :=
  IsFractionRing.map (A := Polynomial (AlgebraicClosure ℚ))
    (B := Polynomial (AlgebraicClosure ℚ)) signPolyHom_involutive.injective

private theorem signFieldHom_algebraMap (x : Polynomial (AlgebraicClosure ℚ)) :
    signFieldHom (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase x)
      = algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase (signPolyHom x) := by
  simp only [signFieldHom, IsFractionRing.map]
  exact IsLocalization.map_eq _ _

/-- `signFieldHom` fixes the image of `substFieldHomEven n` (i.e. the subfield `ℚ̄(t²)`). -/
private theorem signFieldHom_comp_substFieldHomEven (n : ℕ) :
    signFieldHom.comp (substFieldHomEven n) = substFieldHomEven n := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial (AlgebraicClosure ℚ)))
  refine RingHom.ext fun x ↦ ?_
  simp only [RingHom.comp_apply]
  rw [show substFieldHomEven n (algebraMap (Polynomial (AlgebraicClosure ℚ)) BaseT x)
        = algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase (substPolyEven n x)
      from substFieldHomEven_algebraMap n x,
    signFieldHom_algebraMap, signPolyHom_substPolyEven]

/-- `t = algebraMap R GeomBase X` is integral over `BaseT`: it is a root of the monic `X² - C β`. -/
private theorem isIntegral_t (n : ℕ) :
    letI := algBaseT n
    IsIntegral BaseT (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X) := by
  letI := algBaseT n
  obtain ⟨β, hβ⟩ := gen_sq_mem_range n
  refine ⟨X ^ 2 - C β, monic_X_pow_sub_C β (by norm_num), ?_⟩
  rw [← aeval_def]
  simp only [map_sub, map_pow, aeval_X, aeval_C, hβ, sub_self]

/-- The minimal polynomial of `t` over `BaseT` has degree `≤ 2` (divides the monic `X² - C β`). -/
private theorem minpoly_natDegree_le_two (n : ℕ) :
    letI := algBaseT n
    (minpoly BaseT (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X)).natDegree ≤ 2 := by
  letI := algBaseT n
  obtain ⟨β, hβ⟩ := gen_sq_mem_range n
  have hmonic : (X ^ 2 - C β : BaseT[X]).Monic := monic_X_pow_sub_C β (by norm_num)
  have haeval : (aeval
      (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X)) (X ^ 2 - C β : BaseT[X]) = 0 := by
    simp only [map_sub, map_pow, aeval_X, aeval_C, hβ, sub_self]
  have hdvd := minpoly.dvd BaseT _ haeval
  calc (minpoly BaseT (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X)).natDegree
        ≤ (X ^ 2 - C β : BaseT[X]).natDegree :=
          natDegree_le_of_dvd hdvd hmonic.ne_zero
    _ = 2 := natDegree_X_pow_sub_C

/-- `t` generates `GeomBase` over `BaseT`. -/
private theorem adjoin_t_eq_top (n : ℕ) :
    letI := algBaseT n
    IntermediateField.adjoin BaseT
      {algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X} = ⊤ := by
  letI := algBaseT n
  set t := algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X with ht
  set M := IntermediateField.adjoin BaseT {t} with hM
  have htM : t ∈ M := IntermediateField.mem_adjoin_simple_self BaseT t
  have hconst : ∀ c : AlgebraicClosure ℚ,
      algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase (C c) ∈ M := by
    intro c
    rw [← substFieldHomEven_C n c, ← algebraMap_baseT_eq n]
    exact M.algebraMap_mem _
  have hrange : ∀ q : Polynomial (AlgebraicClosure ℚ),
      algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase q ∈ M := by
    intro q
    refine Polynomial.induction_on' q ?_ ?_
    · intro p q hp hq
      rw [map_add]
      exact add_mem hp hq
    · intro k c
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
      exact mul_mem (hconst c) (pow_mem htM k)
  rw [eq_top_iff]
  intro y _
  obtain ⟨a, d, -, rfl⟩ :=
    IsFractionRing.div_surjective (A := Polynomial (AlgebraicClosure ℚ)) (K := GeomBase) y
  exact div_mem (hrange a) (hrange d)

/-- `t` is not in the base field `BaseT` (its image), via the sign automorphism: `σ t = -t ≠ t`. -/
private theorem t_not_mem_range (n : ℕ) :
    letI := algBaseT n
    algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X
      ∉ Set.range (algebraMap BaseT GeomBase) := by
  letI := algBaseT n
  rintro ⟨b, hb⟩
  rw [algebraMap_baseT_eq] at hb
  have h1 : signFieldHom (substFieldHomEven n b) = substFieldHomEven n b :=
    RingHom.congr_fun (signFieldHom_comp_substFieldHomEven n) b
  have h2 : signFieldHom (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X)
      = - algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X := by
    rw [signFieldHom_algebraMap, signPolyHom_apply, X_comp, map_neg]
  rw [hb, h2] at h1
  have htne : algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
    exact X_ne_zero
  have h6 : (2 : GeomBase) * algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X = 0 := by
    linear_combination -h1
  rcases mul_eq_zero.mp h6 with h | h
  · exact two_ne_zero h
  · exact htne h

set_option synthInstance.maxHeartbeats 200000 in
set_option linter.unusedVariables false in
/-- **Finite-dimensionality of the even quadratic base change.**  `GeomBase = ℚ̄(t)` is a *finite*
extension of `BaseT ≅ ℚ̄(t²)` under the even substitution `t ↦ c₀ + c₂·t²` (`c₂ ≠ 0`).

This is required as an *instance* at the descent call site: `finrank_baseT_geomBase = 2` alone does
**not** synthesize `FiniteDimensional BaseT GeomBase` (a `finrank` of a possibly-infinite extension
is `0`, so the numeric value carries no finiteness information).  Same underlying content as
`finrank_baseT_geomBase`: by `gen_sq_mem_range`, `t = algebraMap R GeomBase X` is a root of the monic
`X² - C β` over `BaseT`, hence integral; and `t` generates `GeomBase` over `BaseT`
(`IntermediateField.adjoin BaseT {t} = ⊤`), so `GeomBase` is a finite (in fact degree-`2`)
extension. -/
theorem finiteDimensional_baseT_geomBase (n : ℕ) (hn : 3 ≤ n) :
    letI := algBaseT n
    FiniteDimensional BaseT GeomBase := by
  letI := algBaseT n
  have hfd : FiniteDimensional BaseT
      (IntermediateField.adjoin BaseT
        {algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X}) :=
    IntermediateField.adjoin.finiteDimensional (isIntegral_t n)
  rw [adjoin_t_eq_top n] at hfd
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

set_option synthInstance.maxHeartbeats 200000 in
set_option linter.unusedVariables false in
/-- **Degree of the even quadratic base change.**  `GeomBase = ℚ̄(t)` is a degree-`2` extension of
`BaseT ≅ ℚ̄(t²)` under the even substitution `t ↦ c₀ + c₂·t²` (`c₂ ≠ 0`).

Proof strategy (crux of the even descent).  By `gen_sq_mem_range`, `t² = algebraMap BaseT GeomBase β`
for an explicit `β`, and `substFieldHomEven` identifies `BaseT` with the subfield `ℚ̄(t²) ⊆ ℚ̄(t)`.
The degree of `ℚ̄(t) / ℚ̄(t²)` is `2`: transport across the algebra isomorphism
`GeomBase ≅ RatFunc ℚ̄` (`FractionRing.algEquiv`) and apply
`RatFunc.finrank_adjoin_eq_height` (`InverseGalois.Hilbert.Analytic.Luroth`) with `θ = X²`, whose
`height` is `max (natDegree X²) (natDegree 1) = 2`; the missing glue is a finrank-preservation lemma
across the scalar-ring iso `BaseT ≃ ℚ̄⟮θ⟯` (no direct Mathlib lemma). Alternatively, the minpoly
route (the one used here): `t` is a root of the monic `X² - C β` over `BaseT` (so
`finrank ≤ 2` via `minpoly`), and `finrank ≥ 2` because `t ∉ ℚ̄(t²)`, shown by the `X ↦ -X` sign
automorphism `σ` (which fixes the image of `substFieldHomEven` but sends `t ↦ -t ≠ t`). -/
theorem finrank_baseT_geomBase (n : ℕ) (hn : 3 ≤ n) :
    letI := algBaseT n
    Module.finrank BaseT GeomBase = 2 := by
  letI := algBaseT n
  have hInt := isIntegral_t n
  have hfr : Module.finrank BaseT
      (IntermediateField.adjoin BaseT
        {algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X})
      = (minpoly BaseT (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X)).natDegree :=
    IntermediateField.adjoin.finrank hInt
  rw [adjoin_t_eq_top n, IntermediateField.finrank_top'] at hfr
  rw [hfr]
  have hle := minpoly_natDegree_le_two n
  have hpos := minpoly.natDegree_pos hInt
  have hne1 : (minpoly BaseT
      (algebraMap (Polynomial (AlgebraicClosure ℚ)) GeomBase X)).natDegree ≠ 1 := by
    intro h1
    apply t_not_mem_range n
    rw [← IntermediateField.mem_bot, ← IntermediateField.adjoin_simple_eq_bot_iff,
      ← IntermediateField.finrank_eq_one_iff, IntermediateField.adjoin.finrank hInt]
    exact h1
  omega

end EvenDescent

end AlternatingFamily

end

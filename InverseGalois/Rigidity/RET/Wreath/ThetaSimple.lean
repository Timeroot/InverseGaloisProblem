/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Genus.Fundamental
import InverseGalois.Rigidity.RET.Genus.OrdUltra
import InverseGalois.Rigidity.RET.Wreath.LineMap

/-!
# Almost every value of a coordinate is taken simply

A non-constant function on a covering surface takes every value: the coordinate `T` of a finite map
to the line takes the value `α` at any place of the source lying over the point `X = α` of the
target, and such a place exists because the integral model is integral over `ℚ̄[X]`, so primes go
up.  The interesting statement is the refinement: at all but finitely many `α` the value is taken
*simply*, that is with multiplicity exactly one at some place.

Multiplicity is ramification.  The order of `T - α` at a place `Q` over `X = α` is the ramification
index of `Q`, and a prime of a separable extension of Dedekind domains is ramified exactly when it
divides the different ideal.  The different is a nonzero ideal, so it is divisible by only finitely
many primes — a nonzero element of it has nonzero order at only finitely many places — and distinct
points of the line have disjoint fibres, so the values `α` whose entire fibre is ramified inject
into the finitely many divisors of the different.  Nothing here needs the map to be Galois, which is
the whole reason for working with `LineMap` rather than `LineCover`.

The last refinement is to keep the simple place away from a prescribed finite set of places.  This
costs nothing: a constant is a unit at every place, so if two different values `α ≠ α'` were both
attained at one and the same place `Q`, their difference — a nonzero constant — would have positive
order at `Q`, which it does not.  Each forbidden place therefore rules out at most one further
value.

## Main results

* `Rigidity.RET.Wreath.LineMap.different_ne_bot` — the different ideal of the integral model is
  nonzero.
* `Rigidity.RET.Wreath.LineMap.finite_ramified` — only finitely many places divide the different.
* `Rigidity.RET.Wreath.LineMap.ord_eq_one_of_unramified` — at an unramified place over `X = α` the
  coordinate takes the value `α` to order one.
* `Rigidity.RET.Wreath.LineMap.exists_ord_pos` — the coordinate takes every value somewhere.
* `Rigidity.RET.Wreath.LineMap.ord_algebraMap_const` — a nonzero constant is a unit at every place.
* `Rigidity.RET.Wreath.LineMap.finite_not_exists_ord_eq_one` — all but finitely many values are
  taken simply.
* `Rigidity.RET.Wreath.LineMap.finite_not_exists_ord_eq_one_notMem` — all but finitely many values
  are taken simply away from any prescribed finite set of places.
-/

open Polynomial IsDedekindDomain

noncomputable section

namespace Rigidity.RET.Wreath

open GeomAKLB (k placeP)

namespace LineMap

set_option synthInstance.maxHeartbeats 400000

/-- **The different ideal of the integral model is nonzero.**  The constant field has
characteristic zero, so the extension of function fields is separable and the different of a
separable extension of Dedekind domains does not vanish. -/
theorem different_ne_bot (L : LineMap) : differentIdeal (Polynomial k) L.R ≠ ⊥ :=
  differentIdeal_ne_bot

/-- **Only finitely many places of the source are ramified.**  A nonzero element of the different
has nonzero order at only finitely many places, and every place dividing the different contains
it. -/
theorem finite_ramified (L : LineMap) :
    {Q : HeightOneSpectrum L.R | Q.asIdeal ∣ differentIdeal (Polynomial k) L.R}.Finite := by
  obtain ⟨d, hdmem, hd0⟩ : ∃ d ∈ differentIdeal (Polynomial k) L.R, d ≠ 0 :=
    Submodule.exists_mem_ne_zero_of_ne_bot (different_ne_bot L)
  have hfin : {Q : HeightOneSpectrum L.R | ord L.M Q (algebraMap L.R L.M d) ≠ 0}.Finite :=
    Filter.eventually_cofinite.mp (ord_finite _)
  refine hfin.subset ?_
  intro Q hQ
  simp only [Set.mem_setOf_eq] at hQ ⊢
  have hle : differentIdeal (Polynomial k) L.R ≤ Q.asIdeal := Ideal.le_of_dvd hQ
  have hpos : (0 : ℤ) < ord L.M Q (algebraMap L.R L.M d) :=
    (mem_iff_ord_pos (K := L.M) (v := Q) hd0).mp (hle hdmem)
  omega

/-- **At an unramified place over a point of the line the coordinate takes that point's value to
order one.**  The order of `T - α` at a place lying over `X = α` is the ramification index there,
and a place not dividing the different is unramified. -/
theorem ord_eq_one_of_unramified (L : LineMap) (α : k) (Q : HeightOneSpectrum L.R)
    [hover : Q.asIdeal.LiesOver (placeP α)]
    (hQ : ¬ Q.asIdeal ∣ differentIdeal (Polynomial k) L.R) :
    ord L.M Q (L.T - algebraMap k L.M α) = 1 := by
  haveI : Algebra.IsUnramifiedAt (Polynomial k) Q.asIdeal := not_dvd_differentIdeal_iff.mp hQ
  haveI : Algebra.EssFiniteType (Polynomial k) L.R := inferInstance
  have hover' : placeP α = Q.asIdeal.under (Polynomial k) := hover.over
  have he : Ideal.ramificationIdx (algebraMap (Polynomial k) L.R) (placeP α) Q.asIdeal = 1 := by
    rw [hover']
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt Q.ne_bot
  have hx : L.T - algebraMap k L.M α = algebraMap (Polynomial k) L.M (X - C α) := by
    rw [map_sub]
    simp only [T, Polynomial.C_eq_algebraMap,
      ← IsScalarTower.algebraMap_apply k (Polynomial k) L.M]
  have hmap0 : Ideal.map (algebraMap (Polynomial k) L.R) (placeP α) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective
      (FaithfulSMul.algebraMap_injective (Polynomial k) L.R)).not.mpr (GeomAKLB.placeP_ne_bot α)
  rw [hx, ord_algebraMap_eq_ramificationIdx (F := L.M) (placeP α) Q rfl hmap0, he]
  rfl

/-- **The coordinate takes every value.**  A prime of the line goes up to a prime of the integral
model, and there the generator `X - α` of the prime below has positive order. -/
theorem exists_ord_pos (L : LineMap) (α : k) :
    ∃ Q : HeightOneSpectrum L.R, 0 < ord L.M Q (L.T - algebraMap k L.M α) := by
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (R := Polynomial k) (S := L.R) (placeP α)
  have hQprime : Q.IsPrime := hQmax.isPrime
  have hQbot : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot (GeomAKLB.placeP_ne_bot α) Q
  have hgen : (X - C α : Polynomial k) ∈ placeP α := Ideal.mem_span_singleton_self _
  set b : L.R := algebraMap (Polynomial k) L.R (X - C α) with hb
  have hbmem : b ∈ Q := by
    have h : (X - C α : Polynomial k) ∈ Ideal.under (Polynomial k) Q := by
      rw [← Ideal.LiesOver.over (p := placeP α) (P := Q)]
      exact hgen
    exact h
  have hb0 : b ≠ 0 := by
    rw [hb, Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (Polynomial k) L.R)]
    exact X_sub_C_ne_zero α
  refine ⟨⟨Q, hQprime, hQbot⟩, ?_⟩
  have hpos := (mem_iff_ord_pos (K := L.M) (v := ⟨Q, hQprime, hQbot⟩) hb0).mp hbmem
  convert hpos using 2
  rw [hb, ← IsScalarTower.algebraMap_apply, map_sub]
  simp only [T, Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply k (Polynomial k) L.M]

/-- **All but finitely many values of the coordinate are taken simply.**  A value whose whole fibre
is ramified determines a place dividing the different, distinct values determine distinct places,
and only finitely many places divide the different. -/
theorem finite_not_exists_ord_eq_one (L : LineMap) :
    {α : k | ¬ ∃ Q : HeightOneSpectrum L.R, ord L.M Q (L.T - algebraMap k L.M α) = 1}.Finite := by
  classical
  set bad := {α : k | ¬ ∃ Q : HeightOneSpectrum L.R, ord L.M Q (L.T - algebraMap k L.M α) = 1}
  have hQ : ∀ α : k, ∃ Q : Ideal L.R, Q.IsMaximal ∧ Q.LiesOver (placeP α) := fun α =>
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (R := Polynomial k) (S := L.R) (placeP α)
  choose Q0 hQ0max hQ0over using hQ
  set f : k → HeightOneSpectrum L.R := fun α =>
    ⟨Q0 α, (hQ0max α).isPrime,
      Ideal.ne_bot_of_liesOver_of_ne_bot (GeomAKLB.placeP_ne_bot α) _⟩
  have hmaps : ∀ α ∈ bad, (f α).asIdeal ∣ differentIdeal (Polynomial k) L.R := by
    intro α hα
    by_contra hdvd
    haveI := hQ0over α
    exact hα ⟨f α, ord_eq_one_of_unramified L α (f α) hdvd⟩
  have hinj : Set.InjOn f bad := by
    intro a _ b _ hab
    have ha : placeP a = Ideal.under (Polynomial k) (f a).asIdeal := (hQ0over a).over
    have hb : placeP b = Ideal.under (Polynomial k) (f b).asIdeal := (hQ0over b).over
    have hab' : placeP a = placeP b := by rw [ha, hb, hab]
    have hmem : (X - C a : Polynomial k) ∈ Ideal.span {(X - C b : Polynomial k)} := by
      rw [show (Ideal.span {(X - C b : Polynomial k)}) = placeP b from rfl, ← hab']
      exact Ideal.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hmem
    have hev := congrArg (Polynomial.eval b) hc
    simpa [sub_eq_zero, eq_comm] using hev
  refine Set.Finite.of_finite_image ?_ hinj
  exact (finite_ramified L).subset (by rintro _ ⟨α, hα, rfl⟩; exact hmaps α hα)

/-- **A nonzero constant is a unit at every place.**  Both the constant and its inverse are
integral over `ℚ̄[X]`, so both have non-negative order, and their orders sum to zero. -/
theorem ord_algebraMap_const (L : LineMap) (Q : HeightOneSpectrum L.R) {c : k} (hc : c ≠ 0) :
    ord L.M Q (algebraMap k L.M c) = 0 := by
  have hconst : ∀ d : k,
      algebraMap k L.M d = algebraMap L.R L.M (algebraMap (Polynomial k) L.R (C d)) := by
    intro d
    rw [← IsScalarTower.algebraMap_apply (Polynomial k) L.R L.M]
    simp only [Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply k (Polynomial k) L.M]
  have hnonneg : ∀ d : k, 0 ≤ ord L.M Q (algebraMap k L.M d) := by
    intro d
    rw [hconst d]
    exact ord_nonneg (K := L.M) Q _
  have hc0 : algebraMap k L.M c ≠ 0 := by
    simpa using (algebraMap k L.M).injective.ne hc
  have hci0 : algebraMap k L.M c⁻¹ ≠ 0 := by
    simpa using (algebraMap k L.M).injective.ne (inv_ne_zero hc)
  have hsum : ord L.M Q (algebraMap k L.M c) + ord L.M Q (algebraMap k L.M c⁻¹) = 0 := by
    rw [← ord_mul (K := L.M) Q hc0 hci0, ← map_mul, mul_inv_cancel₀ hc, map_one, ord_one]
  have h1 := hnonneg c
  have h2 := hnonneg c⁻¹
  omega

/-- **A place sees at most one value of the coordinate.**  If the coordinate came close to two
values at one place, their difference — a nonzero constant — would have positive order there. -/
theorem subsingleton_ord_pos (L : LineMap) (Q : HeightOneSpectrum L.R) :
    {α : k | 0 < ord L.M Q (L.T - algebraMap k L.M α)}.Subsingleton := by
  intro a ha b hb
  simp only [Set.mem_setOf_eq] at ha hb
  by_contra hne
  have hsub : (L.T - algebraMap k L.M a) - (L.T - algebraMap k L.M b)
      = algebraMap k L.M (b - a) := by
    rw [map_sub]
    ring
  have hne0 : algebraMap k L.M (b - a) ≠ 0 := by
    simpa using (algebraMap k L.M).injective.ne (sub_ne_zero.mpr (Ne.symm hne))
  have h := min_ord_le_ord_sub (K := L.M) (v := Q) (x := L.T - algebraMap k L.M a)
    (y := L.T - algebraMap k L.M b) (by rw [hsub]; exact hne0)
  rw [hsub, ord_algebraMap_const L Q (sub_ne_zero.mpr (Ne.symm hne))] at h
  exact absurd h (not_le.mpr (lt_min ha hb))

/-- **A coordinate takes all but finitely many values simply, and away from any prescribed finite
set of places.**  A value that is only ever taken simply inside the forbidden set uses up one of
its places, and no place is used twice. -/
theorem finite_not_exists_ord_eq_one_notMem (L : LineMap) (Z : Finset (HeightOneSpectrum L.R)) :
    {α : k | ¬ ∃ Q : HeightOneSpectrum L.R,
        Q ∉ Z ∧ ord L.M Q (L.T - algebraMap k L.M α) = 1}.Finite := by
  classical
  have hZ : (⋃ Q ∈ (↑Z : Set (HeightOneSpectrum L.R)),
      {α : k | 0 < ord L.M Q (L.T - algebraMap k L.M α)}).Finite :=
    Set.Finite.biUnion Z.finite_toSet fun Q _ => (subsingleton_ord_pos L Q).finite
  refine ((finite_not_exists_ord_eq_one L).union hZ).subset ?_
  intro α hα
  simp only [Set.mem_setOf_eq, not_exists, not_and] at hα
  by_cases h : ∃ Q : HeightOneSpectrum L.R, ord L.M Q (L.T - algebraMap k L.M α) = 1
  · obtain ⟨Q, hQ⟩ := h
    have hQZ : Q ∈ (↑Z : Set (HeightOneSpectrum L.R)) := by
      by_contra hcon
      exact hα Q (fun hmem => hcon hmem) hQ
    refine Or.inr (Set.mem_iUnion₂.mpr ⟨Q, hQZ, ?_⟩)
    show (0 : ℤ) < ord L.M Q (L.T - algebraMap k L.M α)
    rw [hQ]
    exact one_pos
  · exact Or.inl h

end LineMap

end Rigidity.RET.Wreath

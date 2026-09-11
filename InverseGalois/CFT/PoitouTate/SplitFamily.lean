/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.TwoPlacesKill

/-!
# A family of two-place data, one pair of places for each coordinate

A prescription with values in a module of several coordinates is realised one coordinate at a time,
and each coordinate spends its own pair of exceptional places.  For the resulting global element to
have the right local behaviour the coordinates must not interfere: the unit built for one
coordinate has to be a local power at the exceptional places of every other coordinate, and at all
of their conjugates, since the conjugates are the places a Galois-stable prescription sees.

Both directions of that non-interference come out of the two-place construction that kills a stable
family of radicands, run over a growing set of places.  An earlier unit is killed at a later place
because the later pair is produced together with the demand that it kill the conjugates of all the
earlier units.  A later unit is killed at an earlier place because the earlier places, and their
conjugates, have by then been put into the set carrying the prescription, and the prescription is
trivial there.

The bookkeeping is packaged as a predicate on a finite set of places together with the two
sequences of places and the sequence of units, saying that all the coordinates built so far behave
in that way; the construction is then an induction on the number of coordinates.

## Main results

* `InverseGalois.CFT.IsTwoPlaceFamily`: the bookkeeping of the coordinates built so far.
* `InverseGalois.CFT.exists_isTwoPlaceFamily`: **for every number of coordinates there is a family
  of pairs of places, and of units ramified exactly at them, realising a prescribed local behaviour
  coordinate by coordinate and not interfering with one another.**
* `InverseGalois.CFT.exists_isTwoPlaceFamily_zpowers`: **the same for a prescription which is
  allowed to be ramified on a distinguished stable part of the prescribed set,** once a
  Galois-equivariant family of lines carrying it is supplied along with it.

## Tags

number field, place, completely split, local class, prescription, coordinate
-/

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 1600000

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped Pointwise

/-! ### The bookkeeping of a family of coordinates -/

section Family

variable {k A K : Type} [Field k] [NumberField k] [Field A] [Algebra k A] [Normal k A]
  [IsAlgClosed A] [Field K] [NumberField K] [Algebra k K] [Algebra K A] [IsGalois k K]
  [IsScalarTower k K A] {Ω : IntermediateField k A} [NumberField ↥Ω] [Normal k ↥Ω] [Algebra K ↥Ω]
  [IsScalarTower k K ↥Ω] [IsScalarTower K ↥Ω A] [IsGalois K ↥Ω]
  {p : ℕ} [NeZero p] {Pc Ec : HeightOneSpectrum (𝓞 K) → ℕ}

variable (Ω p) in
/-- **The data of the coordinates built so far.**  A finite set of places containing the places
carrying the prescription, stable under the Galois group and completely split in the auxiliary
field outside the prescribed part; for each coordinate a pair of places, outside the prescribed
part but inside the finite set together with all their conjugates, with trivial decomposition
group; and for each coordinate a unit realising the prescription of that coordinate, ramified
exactly at that coordinate's pair of places and on a distinguished part of the prescribed set, a
local power at every conjugate of them and at every conjugate of the pairs of the other
coordinates. -/
structure IsTwoPlaceFamily (Tr Tn : Finset (HeightOneSpectrum (𝓞 K)))
    (c : ℕ → (v : HeightOneSpectrum (𝓞 K)) → localClasses v p) (d : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (Q R : ℕ → HeightOneSpectrum (𝓞 K))
    (z : ℕ → Kˣ) : Prop where
  /-- The finite set contains the places carrying the prescription. -/
  subset : Tn ⊆ S
  /-- The finite set is stable under the Galois group. -/
  stable : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ S → σ • v ∈ S
  /-- Outside the prescribed part the places of the finite set are completely split. -/
  split : ∀ v ∈ S, v ∉ Tn → ∃ W : HeightOneSpectrum (𝓞 ↥Ω),
    primeUnder (𝓞 K) W = v ∧ stabilizer Gal(↥Ω/k) W = ⊥
  /-- Every conjugate of the first place of a coordinate lies in the finite set. -/
  memQ : ∀ i < d, ∀ σ : Gal(K/k), σ • Q i ∈ S
  /-- Every conjugate of the second place of a coordinate lies in the finite set. -/
  memR : ∀ i < d, ∀ σ : Gal(K/k), σ • R i ∈ S
  /-- The first place of a coordinate is outside the prescribed part. -/
  notMemQ : ∀ i < d, Q i ∉ Tn
  /-- The second place of a coordinate is outside the prescribed part. -/
  notMemR : ∀ i < d, R i ∉ Tn
  /-- The unit of a coordinate realises the prescription of that coordinate. -/
  prescribed : ∀ i < d, ∀ v ∈ Tn, localClassHom v p (z i) = c i v
  /-- The unit of a coordinate is unramified away from that coordinate's pair of places and the
  distinguished part. -/
  unram : ∀ i < d, ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Tr → v ≠ Q i → v ≠ R i →
    (p : ℤ) ∣ placeValue v (z i)
  /-- The unit of a coordinate is ramified at the first place of that coordinate. -/
  ramQ : ∀ i < d, ¬ (p : ℤ) ∣ placeValue (Q i) (z i)
  /-- The unit of a coordinate is ramified at the second place of that coordinate. -/
  ramR : ∀ i < d, ¬ (p : ℤ) ∣ placeValue (R i) (z i)
  /-- The unit of a coordinate is a local power at every proper conjugate of its first place. -/
  conjQ : ∀ i < d, ∀ σ : Gal(K/k), σ ≠ 1 → localClassHom (σ • Q i) p (z i) = 1
  /-- The unit of a coordinate is a local power at every proper conjugate of its second place. -/
  conjR : ∀ i < d, ∀ σ : Gal(K/k), σ ≠ 1 → localClassHom (σ • R i) p (z i) = 1
  /-- The unit of a coordinate is a local power at every conjugate of the first place of another
  coordinate. -/
  crossQ : ∀ i < d, ∀ j < d, i ≠ j → ∀ σ : Gal(K/k), localClassHom (σ • Q j) p (z i) = 1
  /-- The unit of a coordinate is a local power at every conjugate of the second place of another
  coordinate. -/
  crossR : ∀ i < d, ∀ j < d, i ≠ j → ∀ σ : Gal(K/k), localClassHom (σ • R j) p (z i) = 1
  /-- The two places of a coordinate are not conjugate. -/
  ne : ∀ i < d, ∀ σ : Gal(K/k), Q i ≠ σ • R i
  /-- The first place of a coordinate has trivial decomposition group. -/
  stabQ : ∀ i < d, stabilizer Gal(K/k) (Q i) = ⊥
  /-- The second place of a coordinate has trivial decomposition group. -/
  stabR : ∀ i < d, stabilizer Gal(K/k) (R i) = ⊥

end Family

/-! ### One more coordinate -/

section Step

variable {k A K : Type} [Field k] [NumberField k] [Field A] [Algebra k A] [Normal k A]
  [IsAlgClosed A] [Field K] [NumberField K] [Algebra k K] [Algebra K A] [IsGalois k K]
  [IsScalarTower k K A] {Ω : IntermediateField k A} [NumberField ↥Ω] [Normal k ↥Ω] [Algebra K ↥Ω]
  [IsScalarTower k K ↥Ω] [IsScalarTower K ↥Ω A] [IsGalois K ↥Ω]
  {p : ℕ} [NeZero p] {Pc Ec : HeightOneSpectrum (𝓞 K) → ℕ}

omit [Normal k A] [IsAlgClosed A] [Algebra K A] [IsGalois k K] [IsScalarTower k K A] [Normal k ↥Ω]
  [IsScalarTower k K ↥Ω] [IsScalarTower K ↥Ω A] [IsGalois K ↥Ω] [NeZero p] in
/-- **The bookkeeping of one more coordinate.**  Given the coordinates built so far and a pair of
places outside the set of places reached so far, together with a unit ramified exactly at them
which meets the prescription of the new coordinate and is a local power at every conjugate of the
pairs of the earlier coordinates, enlarging the set by the conjugates of the two places carries the
bookkeeping to one coordinate more. -/
theorem exists_isTwoPlaceFamily_succ_of_two_places
    {T Tr Tn : Finset (HeightOneSpectrum (𝓞 K))} (hT : T ⊆ Tn)
    (hTnst : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ Tn → σ • v ∈ Tn)
    {c : ℕ → (v : HeightOneSpectrum (𝓞 K)) → localClasses v p}
    (hcT : ∀ (i : ℕ), ∀ v ∈ Tn, v ∉ T → c i v = 1)
    {d : ℕ} {S : Finset (HeightOneSpectrum (𝓞 K))} {Q R : ℕ → HeightOneSpectrum (𝓞 K)}
    {z : ℕ → Kˣ} (h : IsTwoPlaceFamily Ω p Tr Tn c d S Q R z)
    {Qn Rn : HeightOneSpectrum (𝓞 K)} {zn : Kˣ} (hQS : Qn ∉ S) (hRS : Rn ∉ S)
    (hQspl : ∀ σ : Gal(K/k), ∃ W : HeightOneSpectrum (𝓞 ↥Ω),
      primeUnder (𝓞 K) W = σ • Qn ∧ stabilizer Gal(↥Ω/k) W = ⊥)
    (hRspl : ∀ σ : Gal(K/k), ∃ W : HeightOneSpectrum (𝓞 ↥Ω),
      primeUnder (𝓞 K) W = σ • Rn ∧ stabilizer Gal(↥Ω/k) W = ⊥)
    (hQz : ∀ i < d, ∀ σ : Gal(K/k), localClassHom (σ • Qn) p (z i) = 1)
    (hRz : ∀ i < d, ∀ σ : Gal(K/k), localClassHom (σ • Rn) p (z i) = 1)
    (hQR : ∀ σ : Gal(K/k), Qn ≠ σ • Rn) (hQstab : stabilizer Gal(K/k) Qn = ⊥)
    (hRstab : stabilizer Gal(K/k) Rn = ⊥)
    (hznT : ∀ v ∈ T, localClassHom v p zn = c d v)
    (hznS : ∀ v ∈ S, v ∉ T → localClassHom v p zn = 1)
    (hznunr : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Tr → v ≠ Qn → v ≠ Rn →
      (p : ℤ) ∣ placeValue v zn)
    (hznQ : ¬ (p : ℤ) ∣ placeValue Qn zn) (hznR : ¬ (p : ℤ) ∣ placeValue Rn zn)
    (hznQc : ∀ σ : Gal(K/k), σ ≠ 1 → localClassHom (σ • Qn) p zn = 1)
    (hznRc : ∀ σ : Gal(K/k), σ ≠ 1 → localClassHom (σ • Rn) p zn = 1) :
    ∃ (S' : Finset (HeightOneSpectrum (𝓞 K))) (Q' R' : ℕ → HeightOneSpectrum (𝓞 K))
      (z' : ℕ → Kˣ), IsTwoPlaceFamily Ω p Tr Tn c (d + 1) S' Q' R' z' := by
  classical
  have hidx : ∀ i, i < d + 1 → i < d ∨ i = d := fun i hi => by omega
  -- the conjugates of the places of the earlier coordinates avoid the prescribed places
  have hQnotT : ∀ i, i < d → ∀ σ : Gal(K/k), σ • Q i ∉ T := by
    intro i hi σ hcon
    refine h.notMemQ i hi ?_
    have h2 := hTnst σ⁻¹ _ (hT hcon)
    rwa [inv_smul_smul] at h2
  have hRnotT : ∀ i, i < d → ∀ σ : Gal(K/k), σ • R i ∉ T := by
    intro i hi σ hcon
    refine h.notMemR i hi ?_
    have h2 := hTnst σ⁻¹ _ (hT hcon)
    rwa [inv_smul_smul] at h2
  -- the enlarged set of places
  have hQfin : (Set.range fun σ : Gal(K/k) => σ • Qn).Finite := Set.finite_range _
  have hRfin : (Set.range fun σ : Gal(K/k) => σ • Rn).Finite := Set.finite_range _
  obtain ⟨S', hS'⟩ : ∃ S' : Finset (HeightOneSpectrum (𝓞 K)),
      ∀ v : HeightOneSpectrum (𝓞 K), v ∈ S' ↔
        (v ∈ S ∨ (∃ σ : Gal(K/k), σ • Qn = v) ∨ ∃ σ : Gal(K/k), σ • Rn = v) :=
    ⟨S ∪ hQfin.toFinset ∪ hRfin.toFinset, fun v => by
      rw [Finset.mem_union, Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
      simp only [Set.mem_range]
      tauto⟩
  have hQu : ∀ i, i ≠ d → Function.update Q d Qn i = Q i := fun i hi =>
    Function.update_of_ne hi _ _
  have hRu : ∀ i, i ≠ d → Function.update R d Rn i = R i := fun i hi =>
    Function.update_of_ne hi _ _
  have hzu : ∀ i, i ≠ d → Function.update z d zn i = z i := fun i hi =>
    Function.update_of_ne hi _ _
  have hQd : Function.update Q d Qn d = Qn := Function.update_self _ _ _
  have hRd : Function.update R d Rn d = Rn := Function.update_self _ _ _
  have hzd : Function.update z d zn d = zn := Function.update_self _ _ _
  refine ⟨S', Function.update Q d Qn, Function.update R d Rn, Function.update z d zn,
    { subset := fun v hv => (hS' v).2 (Or.inl (h.subset hv))
      stable := ?_
      split := ?_
      memQ := ?_
      memR := ?_
      notMemQ := ?_
      notMemR := ?_
      prescribed := ?_
      unram := ?_
      ramQ := ?_
      ramR := ?_
      conjQ := ?_
      conjR := ?_
      crossQ := ?_
      crossR := ?_
      ne := ?_
      stabQ := ?_
      stabR := ?_ }⟩
  · intro σ v hv
    rcases (hS' v).1 hv with hv' | ⟨τ, rfl⟩ | ⟨τ, rfl⟩
    · exact (hS' _).2 (Or.inl (h.stable σ v hv'))
    · exact (hS' _).2 (Or.inr (Or.inl ⟨σ * τ, mul_smul σ τ Qn⟩))
    · exact (hS' _).2 (Or.inr (Or.inr ⟨σ * τ, mul_smul σ τ Rn⟩))
  · intro v hv hvn
    rcases (hS' v).1 hv with hv' | ⟨τ, rfl⟩ | ⟨τ, rfl⟩
    · exact h.split v hv' hvn
    · exact hQspl τ
    · exact hRspl τ
  · intro i hi σ
    rcases hidx i hi with hi' | rfl
    · rw [hQu i hi'.ne]
      exact (hS' _).2 (Or.inl (h.memQ i hi' σ))
    · rw [hQd]
      exact (hS' _).2 (Or.inr (Or.inl ⟨σ, rfl⟩))
  · intro i hi σ
    rcases hidx i hi with hi' | rfl
    · rw [hRu i hi'.ne]
      exact (hS' _).2 (Or.inl (h.memR i hi' σ))
    · rw [hRd]
      exact (hS' _).2 (Or.inr (Or.inr ⟨σ, rfl⟩))
  · intro i hi
    rcases hidx i hi with hi' | rfl
    · rw [hQu i hi'.ne]; exact h.notMemQ i hi'
    · rw [hQd]; exact fun hcon => hQS (h.subset hcon)
  · intro i hi
    rcases hidx i hi with hi' | rfl
    · rw [hRu i hi'.ne]; exact h.notMemR i hi'
    · rw [hRd]; exact fun hcon => hRS (h.subset hcon)
  · intro i hi v hv
    rcases hidx i hi with hi' | rfl
    · rw [hzu i hi'.ne]; exact h.prescribed i hi' v hv
    · rw [hzd]
      by_cases hvT : v ∈ T
      · exact hznT v hvT
      · rw [hznS v (h.subset hv) hvT]; exact (hcT _ v hv hvT).symm
  · intro i hi v hvTr hvQ hvR
    rcases hidx i hi with hi' | rfl
    · rw [hQu i hi'.ne] at hvQ
      rw [hRu i hi'.ne] at hvR
      rw [hzu i hi'.ne]
      exact h.unram i hi' v hvTr hvQ hvR
    · rw [hQd] at hvQ
      rw [hRd] at hvR
      rw [hzd]
      exact hznunr v hvTr hvQ hvR
  · intro i hi
    rcases hidx i hi with hi' | rfl
    · rw [hQu i hi'.ne, hzu i hi'.ne]; exact h.ramQ i hi'
    · rw [hQd, hzd]; exact hznQ
  · intro i hi
    rcases hidx i hi with hi' | rfl
    · rw [hRu i hi'.ne, hzu i hi'.ne]; exact h.ramR i hi'
    · rw [hRd, hzd]; exact hznR
  · intro i hi σ hσ
    rcases hidx i hi with hi' | rfl
    · rw [hQu i hi'.ne, hzu i hi'.ne]; exact h.conjQ i hi' σ hσ
    · rw [hQd, hzd]; exact hznQc σ hσ
  · intro i hi σ hσ
    rcases hidx i hi with hi' | rfl
    · rw [hRu i hi'.ne, hzu i hi'.ne]; exact h.conjR i hi' σ hσ
    · rw [hRd, hzd]; exact hznRc σ hσ
  · intro i hi j hj hij σ
    rcases hidx i hi with hi' | rfl
    · rcases hidx j hj with hj' | rfl
      · rw [hQu j hj'.ne, hzu i hi'.ne]; exact h.crossQ i hi' j hj' hij σ
      · rw [hQd, hzu i hi'.ne]; exact hQz i hi' σ
    · rcases hidx j hj with hj' | rfl
      · rw [hQu j hj'.ne, hzd]
        exact hznS _ (h.memQ j hj' σ) (hQnotT j hj' σ)
      · exact absurd rfl hij
  · intro i hi j hj hij σ
    rcases hidx i hi with hi' | rfl
    · rcases hidx j hj with hj' | rfl
      · rw [hRu j hj'.ne, hzu i hi'.ne]; exact h.crossR i hi' j hj' hij σ
      · rw [hRd, hzu i hi'.ne]; exact hRz i hi' σ
    · rcases hidx j hj with hj' | rfl
      · rw [hRu j hj'.ne, hzd]
        exact hznS _ (h.memR j hj' σ) (hRnotT j hj' σ)
      · exact absurd rfl hij
  · intro i hi σ
    rcases hidx i hi with hi' | rfl
    · rw [hQu i hi'.ne, hRu i hi'.ne]; exact h.ne i hi' σ
    · rw [hQd, hRd]; exact hQR σ
  · intro i hi
    rcases hidx i hi with hi' | rfl
    · rw [hQu i hi'.ne]; exact h.stabQ i hi'
    · rw [hQd]; exact hQstab
  · intro i hi
    rcases hidx i hi with hi' | rfl
    · rw [hRu i hi'.ne]; exact h.stabR i hi'
    · rw [hRd]; exact hRstab

/-- **One more coordinate.**  The conjugates of the units already built form a family of radicands
carried into itself by the Galois group, and the places at which they fail to be local powers all
lie in the finite set of places reached so far; running the two-place construction that kills such
a family over that finite set therefore returns a pair of places killing every earlier unit, and a
unit for the new coordinate which is a local power at every place of the finite set outside the
prescribed part, hence at every conjugate of the pairs of the earlier coordinates. -/
theorem exists_isTwoPlaceFamily_succ (hp : p.Prime) (hodd : 2 < p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (Pc v) (Ec v))
    {T Tn : Finset (HeightOneSpectrum (𝓞 K))} (hT : T ⊆ Tn)
    (hTnst : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ Tn → σ • v ∈ Tn)
    (hpTn : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((p : ℕ) : K) ≠ 1 → v ∈ Tn)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ (Tn : Set (HeightOneSpectrum (𝓞 K))),
        Rigidity.RET.ord K v (a : K) = m v)
    {c : ℕ → (v : HeightOneSpectrum (𝓞 K)) → localClasses v p}
    (hcunr : ∀ (i : ℕ), ∀ v ∈ Tn, c i v ∈ localUnramified v p)
    {g : ℕ → Kˣ} (hg : ∀ i : ℕ, g i ∈ sUnits K (Tn : Set (HeightOneSpectrum (𝓞 K))))
    (hc : ∀ (i : ℕ), ∀ v ∈ T, c i v = localClassHom v p (g i))
    (hcT : ∀ (i : ℕ), ∀ v ∈ Tn, v ∉ T → c i v = 1)
    (hcn : ∀ (i : ℕ), ∀ v ∈ T, FinitePlace.mk v ((p : ℕ) : K) ≠ 1 → c i v = 1)
    (hsplit : ∀ v ∈ Tn, v ∉ T → ∃ W : HeightOneSpectrum (𝓞 ↥Ω),
      primeUnder (𝓞 K) W = v ∧ stabilizer Gal(↥Ω/K) W = ⊥)
    (hram : ∀ v ∉ Tn, ∃ W : HeightOneSpectrum (𝓞 ↥Ω),
      primeUnder (𝓞 K) W = v ∧ ramIdx (𝓞 K) W = 1)
    {d : ℕ} {S : Finset (HeightOneSpectrum (𝓞 K))} {Q R : ℕ → HeightOneSpectrum (𝓞 K)}
    {z : ℕ → Kˣ} (h : IsTwoPlaceFamily Ω p ∅ Tn c d S Q R z) :
    ∃ (S' : Finset (HeightOneSpectrum (𝓞 K))) (Q' R' : ℕ → HeightOneSpectrum (𝓞 K))
      (z' : ℕ → Kˣ), IsTwoPlaceFamily Ω p ∅ Tn c (d + 1) S' Q' R' z' := by
  classical
  -- the radicands: the conjugates of the units already built
  let b : Fin d × Gal(K/k) → Kˣ := fun q => galUnits q.2 (z (q.1 : ℕ))
  have hbval : ∀ q : Fin d × Gal(K/k), ((b q : Kˣ) : K) = q.2 ((z (q.1 : ℕ) : K)) :=
    fun _ => rfl
  have hbone : ∀ (i : ℕ) (hi : i < d), b (⟨i, hi⟩, 1) = z i := fun _ _ => Units.ext rfl
  have hwex : ∀ q : Fin d × Gal(K/k), ∃ y : A, y ^ p = algebraMap K A ((b q : K)) :=
    fun q => IsAlgClosed.exists_pow_nat_eq _ hp.pos
  choose w hw using hwex
  have hstab : ∀ (σ : Gal(K/k)) (q : Fin d × Gal(K/k)), ∃ q', σ ((b q : K)) = ((b q' : K)) := by
    intro σ q
    refine ⟨(q.1, σ * q.2), ?_⟩
    rw [hbval, hbval, AlgEquiv.mul_apply]
  -- the earlier units have order a multiple of the exponent at the prescribed places
  have hord : ∀ v ∈ T, FinitePlace.mk v ((p : ℕ) : K) = 1 →
      ∀ q, (p : ℤ) ∣ Rigidity.RET.ord K v ((b q : K)) := by
    intro v hv _ q
    have hkey : Rigidity.RET.ord K v ((b q : K))
        = Rigidity.RET.ord K (q.2⁻¹ • v) ((z (q.1 : ℕ) : K)) := by
      rw [hbval q, ← ord_galSmul q.2 (q.2⁻¹ • v) ((z (q.1 : ℕ) : K)), smul_inv_smul]
    have hvn : q.2⁻¹ • v ∈ Tn := hTnst _ _ (hT hv)
    have hne1 : q.2⁻¹ • v ≠ Q (q.1 : ℕ) := fun hcon => h.notMemQ _ q.1.2 (hcon ▸ hvn)
    have hne2 : q.2⁻¹ • v ≠ R (q.1 : ℕ) := fun hcon => h.notMemR _ q.1.2 (hcon ▸ hvn)
    have hu := h.unram _ q.1.2 _ (Finset.notMem_empty _) hne1 hne2
    rw [placeValue_eq_neg_ord, dvd_neg] at hu
    rw [hkey]
    exact hu
  -- the hypotheses of the two-place construction, transported to the finite set reached so far
  have hsplitS : ∀ v ∈ S, v ∉ T → ∃ W : HeightOneSpectrum (𝓞 ↥Ω),
      primeUnder (𝓞 K) W = v ∧ stabilizer Gal(↥Ω/K) W = ⊥ := by
    intro v hv hvT
    by_cases hvn : v ∈ Tn
    · exact hsplit v hvn hvT
    · obtain ⟨W, hW1, hW2⟩ := h.split v hv hvn
      exact ⟨W, hW1, stabilizer_eq_bot_of_stabilizer_base_eq_bot (k := k) hW2⟩
  have hramS : ∀ v ∉ S, ∃ W : HeightOneSpectrum (𝓞 ↥Ω),
      primeUnder (𝓞 K) W = v ∧ ramIdx (𝓞 K) W = 1 :=
    fun v hv => hram v fun hcon => hv (h.subset hcon)
  have hpS : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((p : ℕ) : K) ≠ 1 → v ∈ S :=
    fun v hv => h.subset (hpTn v hv)
  have hreprS : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ (S : Set (HeightOneSpectrum (𝓞 K))),
        Rigidity.RET.ord K v (a : K) = m v := by
    intro m hm
    obtain ⟨a, ha⟩ := hrepr m hm
    exact ⟨a, fun v hv => ha v fun hcon => hv (h.subset hcon)⟩
  -- the prescription of the new coordinate, read over the larger set
  let c' : (v : HeightOneSpectrum (𝓞 K)) → localClasses v p := fun v => if v ∈ T then c d v else 1
  have hc'T : ∀ v ∈ T, c' v = c d v := fun v hv => if_pos hv
  have hc'nT : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → c' v = 1 := fun v hv => if_neg hv
  have hcunr' : ∀ v ∈ S, c' v ∈ localUnramified v p := by
    intro v hv
    by_cases hvT : v ∈ T
    · rw [hc'T v hvT]
      exact hcunr d v (hT hvT)
    · rw [hc'nT v hvT]
      exact one_mem _
  have hgS : g d ∈ sUnits K (S : Set (HeightOneSpectrum (𝓞 K))) :=
    mem_sUnits.2 fun v hv => mem_sUnits.1 (hg d) v fun hcon => hv (h.subset hcon)
  have hcS : ∀ v ∈ T, c' v = localClassHom v p (g d) := fun v hv => by
    rw [hc'T v hv]; exact hc d v hv
  have hcTS : ∀ v ∈ S, v ∉ T → c' v = 1 := fun v _ hvT => hc'nT v hvT
  have hcnS : ∀ v ∈ T, FinitePlace.mk v ((p : ℕ) : K) ≠ 1 → c' v = 1 := fun v hv hvp => by
    rw [hc'T v hv]; exact hcn d v hv hvp
  -- the new pair of places, and the unit of the new coordinate
  obtain ⟨Qn, Rn, hQTn, hRTn, hQspl, hRspl, hQb, hRb, hQR, hQstab, hRstab, zn, hzT, hzunr, hzQ,
    hzR, hzQc, hzRc⟩ :=
    exists_two_places_sUnit_kill (Ω := Ω) (T := T) (Tn := S) hp hodd hζ hres (hT.trans h.subset)
      h.stable hpS hreprS hcunr' hgS hcS hcTS hcnS hw hstab hord hsplitS hramS
  refine exists_isTwoPlaceFamily_succ_of_two_places (Ω := Ω) hT hTnst hcT h hQTn hRTn hQspl hRspl
    ?_ ?_ hQR hQstab hRstab ?_ ?_ ?_ hzQ hzR hzQc hzRc
  · intro i hi σ
    have hbq := hQb σ (⟨i, hi⟩, 1)
    rwa [hbone i hi] at hbq
  · intro i hi σ
    have hbq := hRb σ (⟨i, hi⟩, 1)
    rwa [hbone i hi] at hbq
  · intro v hv
    rw [hzT v (h.subset (hT hv))]
    exact hc'T v hv
  · intro v hv hvT
    rw [hzT v hv]
    exact hc'nT v hvT
  · intro v _ hvQ hvR
    exact hzunr v hvQ hvR

/-- **One more coordinate, for a prescription which is allowed to be ramified on a distinguished
stable part of the prescribed set.**  The classes of the earlier units at the prescribed places are
the values of the prescription there, so a Galois-equivariant family of lines carrying the
prescription carries the classes of the conjugates of the earlier units as well, which is what the
two-place construction needs of the radicands in place of their being local powers. -/
theorem exists_isTwoPlaceFamily_succ_zpowers (hp : p.Prime) (hodd : 2 < p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (Pc v) (Ec v))
    {Tr T Tn : Finset (HeightOneSpectrum (𝓞 K))} (hTr : Tr ⊆ T) (hT : T ⊆ Tn)
    (hTrst : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ Tr → σ • v ∈ Tr)
    (hTnst : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ Tn → σ • v ∈ Tn)
    (hpTn : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((p : ℕ) : K) ≠ 1 → v ∈ Tn)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ (Tn : Set (HeightOneSpectrum (𝓞 K))),
        Rigidity.RET.ord K v (a : K) = m v)
    {c : ℕ → (v : HeightOneSpectrum (𝓞 K)) → localClasses v p}
    (hcunr : ∀ (i : ℕ), ∀ v ∈ Tn, v ∉ Tr → c i v ∈ localUnramified v p)
    (hcfree : ∀ (i : ℕ), ∀ σ : Gal(K/k), σ ≠ 1 → ∀ v ∈ Tr, c i (σ • v) = 1 ∨ c i v = 1)
    {g : ℕ → Kˣ} (hg : ∀ i : ℕ, g i ∈ sUnits K (Tn : Set (HeightOneSpectrum (𝓞 K))))
    (hc : ∀ (i : ℕ), ∀ v ∈ T, c i v = localClassHom v p (g i))
    (hcT : ∀ (i : ℕ), ∀ v ∈ Tn, v ∉ T → c i v = 1)
    (hcn : ∀ (i : ℕ), ∀ v ∈ T, FinitePlace.mk v ((p : ℕ) : K) ≠ 1 → c i v = 1)
    {D : (v : HeightOneSpectrum (𝓞 K)) → localClasses v p}
    (hDgal : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)),
      Subgroup.zpowers (D (σ • v)) = Subgroup.zpowers (localClassesGalEquiv σ v p (D v)))
    (hDc : ∀ (i : ℕ), ∀ v ∈ Tn, c i v ∈ Subgroup.zpowers (D v))
    (hsplit : ∀ v ∈ Tn, v ∉ T → ∃ W : HeightOneSpectrum (𝓞 ↥Ω),
      primeUnder (𝓞 K) W = v ∧ stabilizer Gal(↥Ω/K) W = ⊥)
    (hram : ∀ v ∉ Tn, ∃ W : HeightOneSpectrum (𝓞 ↥Ω),
      primeUnder (𝓞 K) W = v ∧ ramIdx (𝓞 K) W = 1)
    {d : ℕ} {S : Finset (HeightOneSpectrum (𝓞 K))} {Q R : ℕ → HeightOneSpectrum (𝓞 K)}
    {z : ℕ → Kˣ} (h : IsTwoPlaceFamily Ω p Tr Tn c d S Q R z) :
    ∃ (S' : Finset (HeightOneSpectrum (𝓞 K))) (Q' R' : ℕ → HeightOneSpectrum (𝓞 K))
      (z' : ℕ → Kˣ), IsTwoPlaceFamily Ω p Tr Tn c (d + 1) S' Q' R' z' := by
  classical
  -- a line is carried to a line by the transport of local classes along the Galois group
  have hmap : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)) (x : localClasses v p),
      x ∈ Subgroup.zpowers (D v) →
      localClassesGalEquiv σ v p x ∈ Subgroup.zpowers (D (σ • v)) := by
    intro σ v x hx
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [hDgal σ v, Subgroup.mem_zpowers_iff]
    exact ⟨m, by rw [← hm, _root_.map_zpow]⟩
  -- the radicands: the conjugates of the units already built
  let b : Fin d × Gal(K/k) → Kˣ := fun q => galUnits q.2 (z (q.1 : ℕ))
  have hbval : ∀ q : Fin d × Gal(K/k), ((b q : Kˣ) : K) = q.2 ((z (q.1 : ℕ) : K)) :=
    fun _ => rfl
  have hwex : ∀ q : Fin d × Gal(K/k), ∃ y : A, y ^ p = algebraMap K A ((b q : K)) :=
    fun q => IsAlgClosed.exists_pow_nat_eq _ hp.pos
  choose w hw using hwex
  have hstab : ∀ (σ : Gal(K/k)) (q : Fin d × Gal(K/k)), ∃ q', σ ((b q : K)) = ((b q' : K)) := by
    intro σ q
    refine ⟨(q.1, σ * q.2), ?_⟩
    rw [hbval, hbval, AlgEquiv.mul_apply]
  -- the classes of the radicands lie on the line carrying the prescription
  have hDb0 : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ Tn → ∀ i, i < d →
      localClassHom (σ • v) p (galUnits σ (z i)) ∈ Subgroup.zpowers (D (σ • v)) := by
    intro σ v hv i hi
    rw [← localClassesGalEquiv_localClassHom, h.prescribed i hi v hv]
    exact hmap σ v _ (hDc i v hv)
  have hDbTn : ∀ q : Fin d × Gal(K/k), ∀ v ∈ Tn,
      localClassHom v p (b q) ∈ Subgroup.zpowers (D v) := fun q =>
    forall_mem_of_forall_mem_smul (T := Tn)
      (Q := fun u => localClassHom u p (b q) ∈ Subgroup.zpowers (D u)) hTnst q.2
      fun v hv => hDb0 q.2 v hv (q.1 : ℕ) q.1.2
  -- the hypotheses of the two-place construction, transported to the finite set reached so far
  have hsplitS : ∀ v ∈ S, v ∉ T → ∃ W : HeightOneSpectrum (𝓞 ↥Ω),
      primeUnder (𝓞 K) W = v ∧ stabilizer Gal(↥Ω/K) W = ⊥ := by
    intro v hv hvT
    by_cases hvn : v ∈ Tn
    · exact hsplit v hvn hvT
    · obtain ⟨W, hW1, hW2⟩ := h.split v hv hvn
      exact ⟨W, hW1, stabilizer_eq_bot_of_stabilizer_base_eq_bot (k := k) hW2⟩
  have hramS : ∀ v ∉ S, ∃ W : HeightOneSpectrum (𝓞 ↥Ω),
      primeUnder (𝓞 K) W = v ∧ ramIdx (𝓞 K) W = 1 :=
    fun v hv => hram v fun hcon => hv (h.subset hcon)
  have hpS : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((p : ℕ) : K) ≠ 1 → v ∈ S :=
    fun v hv => h.subset (hpTn v hv)
  have hreprS : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ (S : Set (HeightOneSpectrum (𝓞 K))),
        Rigidity.RET.ord K v (a : K) = m v := by
    intro m hm
    obtain ⟨a, ha⟩ := hrepr m hm
    exact ⟨a, fun v hv => ha v fun hcon => hv (h.subset hcon)⟩
  -- the prescription of the new coordinate, read over the larger set
  let c' : (v : HeightOneSpectrum (𝓞 K)) → localClasses v p := fun v => if v ∈ T then c d v else 1
  have hc'T : ∀ v ∈ T, c' v = c d v := fun v hv => if_pos hv
  have hc'nT : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → c' v = 1 := fun v hv => if_neg hv
  have hcunr' : ∀ v ∈ S, v ∉ Tr → c' v ∈ localUnramified v p := by
    intro v hv hvTr
    by_cases hvT : v ∈ T
    · rw [hc'T v hvT]
      exact hcunr d v (hT hvT) hvTr
    · rw [hc'nT v hvT]
      exact one_mem _
  have hcfree' : ∀ σ : Gal(K/k), σ ≠ 1 → ∀ v ∈ Tr, c' (σ • v) = 1 ∨ c' v = 1 := by
    intro σ hσ v hv
    rw [hc'T v (hTr hv), hc'T (σ • v) (hTr (hTrst σ v hv))]
    exact hcfree d σ hσ v hv
  have hgS : g d ∈ sUnits K (S : Set (HeightOneSpectrum (𝓞 K))) :=
    mem_sUnits.2 fun v hv => mem_sUnits.1 (hg d) v fun hcon => hv (h.subset hcon)
  have hcS : ∀ v ∈ T, c' v = localClassHom v p (g d) := fun v hv => by
    rw [hc'T v hv]; exact hc d v hv
  have hcTS : ∀ v ∈ S, v ∉ T → c' v = 1 := fun v _ hvT => hc'nT v hvT
  have hcnS : ∀ v ∈ T, FinitePlace.mk v ((p : ℕ) : K) ≠ 1 → c' v = 1 := fun v hv hvp => by
    rw [hc'T v hv]; exact hcn d v hv hvp
  have hDcS : ∀ v ∈ T, c' v ∈ Subgroup.zpowers (D v) := fun v hv => by
    rw [hc'T v hv]; exact hDc d v (hT hv)
  have hDbS : ∀ v ∈ T, ∀ q : Fin d × Gal(K/k),
      localClassHom v p (b q) ∈ Subgroup.zpowers (D v) := fun v hv q => hDbTn q v (hT hv)
  -- the new pair of places, and the unit of the new coordinate
  obtain ⟨Qn, Rn, hQTn, hRTn, hQspl, hRspl, hQb, hRb, hQR, hQstab, hRstab, zn, hzT, hzunr, hzQ,
    hzR, hzQc, hzRc⟩ :=
    exists_two_places_sUnit_kill_zpowers (Ω := Ω) (Tr := Tr) (T := T) (Tn := S) hp hodd hζ hres hTr
      (hT.trans h.subset) hTrst h.stable hpS hreprS hcunr' hcfree' hgS hcS hcTS hcnS hw hstab hDcS
      hDbS hsplitS hramS
  refine exists_isTwoPlaceFamily_succ_of_two_places (Ω := Ω) hT hTnst hcT h hQTn hRTn hQspl hRspl
    ?_ ?_ hQR hQstab hRstab ?_ ?_ hzunr hzQ hzR hzQc hzRc
  · intro i hi σ
    have hbq := hQb σ (⟨i, hi⟩, 1)
    rwa [show b (⟨i, hi⟩, 1) = z i from Units.ext rfl] at hbq
  · intro i hi σ
    have hbq := hRb σ (⟨i, hi⟩, 1)
    rwa [show b (⟨i, hi⟩, 1) = z i from Units.ext rfl] at hbq
  · intro v hv
    rw [hzT v (h.subset (hT hv))]
    exact hc'T v hv
  · intro v hv hvT
    rw [hzT v hv]
    exact hc'nT v hvT

/-- **A family of pairs of places, one pair for each coordinate, and units realising a prescribed
local behaviour coordinate by coordinate without interfering with one another.**  Each coordinate
is built by the two-place construction over the set of places already spent, and the pair it
returns kills every unit built before it, while its own unit is trivial at every place already
spent outside the prescribed part. -/
theorem exists_isTwoPlaceFamily (hp : p.Prime) (hodd : 2 < p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (Pc v) (Ec v))
    {T Tn : Finset (HeightOneSpectrum (𝓞 K))} (hT : T ⊆ Tn)
    (hTnst : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ Tn → σ • v ∈ Tn)
    (hpTn : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((p : ℕ) : K) ≠ 1 → v ∈ Tn)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ (Tn : Set (HeightOneSpectrum (𝓞 K))),
        Rigidity.RET.ord K v (a : K) = m v)
    {c : ℕ → (v : HeightOneSpectrum (𝓞 K)) → localClasses v p}
    (hcunr : ∀ (i : ℕ), ∀ v ∈ Tn, c i v ∈ localUnramified v p)
    {g : ℕ → Kˣ} (hg : ∀ i : ℕ, g i ∈ sUnits K (Tn : Set (HeightOneSpectrum (𝓞 K))))
    (hc : ∀ (i : ℕ), ∀ v ∈ T, c i v = localClassHom v p (g i))
    (hcT : ∀ (i : ℕ), ∀ v ∈ Tn, v ∉ T → c i v = 1)
    (hcn : ∀ (i : ℕ), ∀ v ∈ T, FinitePlace.mk v ((p : ℕ) : K) ≠ 1 → c i v = 1)
    (hsplit : ∀ v ∈ Tn, v ∉ T → ∃ W : HeightOneSpectrum (𝓞 ↥Ω),
      primeUnder (𝓞 K) W = v ∧ stabilizer Gal(↥Ω/K) W = ⊥)
    (hram : ∀ v ∉ Tn, ∃ W : HeightOneSpectrum (𝓞 ↥Ω),
      primeUnder (𝓞 K) W = v ∧ ramIdx (𝓞 K) W = 1) (d : ℕ) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (Q R : ℕ → HeightOneSpectrum (𝓞 K)) (z : ℕ → Kˣ),
      IsTwoPlaceFamily Ω p ∅ Tn c d S Q R z := by
  classical
  haveI : Nonempty (HeightOneSpectrum (𝓞 K)) := by
    obtain ⟨P, hP0, hP⟩ := Ring.not_isField_iff_exists_prime.1 (RingOfIntegers.not_isField K)
    exact ⟨⟨P, hP, hP0⟩⟩
  induction d with
  | zero =>
    refine ⟨Tn, fun _ => Classical.arbitrary _, fun _ => Classical.arbitrary _, fun _ => 1,
      { subset := Finset.Subset.refl Tn
        stable := hTnst
        split := fun v hv hvn => absurd hv hvn
        memQ := fun i hi => absurd hi (Nat.not_lt_zero i)
        memR := fun i hi => absurd hi (Nat.not_lt_zero i)
        notMemQ := fun i hi => absurd hi (Nat.not_lt_zero i)
        notMemR := fun i hi => absurd hi (Nat.not_lt_zero i)
        prescribed := fun i hi => absurd hi (Nat.not_lt_zero i)
        unram := fun i hi => absurd hi (Nat.not_lt_zero i)
        ramQ := fun i hi => absurd hi (Nat.not_lt_zero i)
        ramR := fun i hi => absurd hi (Nat.not_lt_zero i)
        conjQ := fun i hi => absurd hi (Nat.not_lt_zero i)
        conjR := fun i hi => absurd hi (Nat.not_lt_zero i)
        crossQ := fun i hi => absurd hi (Nat.not_lt_zero i)
        crossR := fun i hi => absurd hi (Nat.not_lt_zero i)
        ne := fun i hi => absurd hi (Nat.not_lt_zero i)
        stabQ := fun i hi => absurd hi (Nat.not_lt_zero i)
        stabR := fun i hi => absurd hi (Nat.not_lt_zero i) }⟩
  | succ n ih =>
    obtain ⟨S, Q, R, z, hst⟩ := ih
    exact exists_isTwoPlaceFamily_succ hp hodd hζ hres hT hTnst hpTn hrepr hcunr hg hc hcT hcn
      hsplit hram hst

/-- **A family of pairs of places and of units realising a prescription which is allowed to be
ramified on a distinguished stable part of the prescribed set.**  The coordinates are built one at
a time exactly as for an unramified prescription; what replaces the demand that the earlier units
be local powers at the prescribed places is a Galois-equivariant family of lines carrying the
prescription. -/
theorem exists_isTwoPlaceFamily_zpowers (hp : p.Prime) (hodd : 2 < p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (Pc v) (Ec v))
    {Tr T Tn : Finset (HeightOneSpectrum (𝓞 K))} (hTr : Tr ⊆ T) (hT : T ⊆ Tn)
    (hTrst : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ Tr → σ • v ∈ Tr)
    (hTnst : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ Tn → σ • v ∈ Tn)
    (hpTn : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((p : ℕ) : K) ≠ 1 → v ∈ Tn)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ (Tn : Set (HeightOneSpectrum (𝓞 K))),
        Rigidity.RET.ord K v (a : K) = m v)
    {c : ℕ → (v : HeightOneSpectrum (𝓞 K)) → localClasses v p}
    (hcunr : ∀ (i : ℕ), ∀ v ∈ Tn, v ∉ Tr → c i v ∈ localUnramified v p)
    (hcfree : ∀ (i : ℕ), ∀ σ : Gal(K/k), σ ≠ 1 → ∀ v ∈ Tr, c i (σ • v) = 1 ∨ c i v = 1)
    {g : ℕ → Kˣ} (hg : ∀ i : ℕ, g i ∈ sUnits K (Tn : Set (HeightOneSpectrum (𝓞 K))))
    (hc : ∀ (i : ℕ), ∀ v ∈ T, c i v = localClassHom v p (g i))
    (hcT : ∀ (i : ℕ), ∀ v ∈ Tn, v ∉ T → c i v = 1)
    (hcn : ∀ (i : ℕ), ∀ v ∈ T, FinitePlace.mk v ((p : ℕ) : K) ≠ 1 → c i v = 1)
    {D : (v : HeightOneSpectrum (𝓞 K)) → localClasses v p}
    (hDgal : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)),
      Subgroup.zpowers (D (σ • v)) = Subgroup.zpowers (localClassesGalEquiv σ v p (D v)))
    (hDc : ∀ (i : ℕ), ∀ v ∈ Tn, c i v ∈ Subgroup.zpowers (D v))
    (hsplit : ∀ v ∈ Tn, v ∉ T → ∃ W : HeightOneSpectrum (𝓞 ↥Ω),
      primeUnder (𝓞 K) W = v ∧ stabilizer Gal(↥Ω/K) W = ⊥)
    (hram : ∀ v ∉ Tn, ∃ W : HeightOneSpectrum (𝓞 ↥Ω),
      primeUnder (𝓞 K) W = v ∧ ramIdx (𝓞 K) W = 1) (d : ℕ) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (Q R : ℕ → HeightOneSpectrum (𝓞 K)) (z : ℕ → Kˣ),
      IsTwoPlaceFamily Ω p Tr Tn c d S Q R z := by
  classical
  haveI : Nonempty (HeightOneSpectrum (𝓞 K)) := by
    obtain ⟨P, hP0, hP⟩ := Ring.not_isField_iff_exists_prime.1 (RingOfIntegers.not_isField K)
    exact ⟨⟨P, hP, hP0⟩⟩
  induction d with
  | zero =>
    refine ⟨Tn, fun _ => Classical.arbitrary _, fun _ => Classical.arbitrary _, fun _ => 1,
      { subset := Finset.Subset.refl Tn
        stable := hTnst
        split := fun v hv hvn => absurd hv hvn
        memQ := fun i hi => absurd hi (Nat.not_lt_zero i)
        memR := fun i hi => absurd hi (Nat.not_lt_zero i)
        notMemQ := fun i hi => absurd hi (Nat.not_lt_zero i)
        notMemR := fun i hi => absurd hi (Nat.not_lt_zero i)
        prescribed := fun i hi => absurd hi (Nat.not_lt_zero i)
        unram := fun i hi => absurd hi (Nat.not_lt_zero i)
        ramQ := fun i hi => absurd hi (Nat.not_lt_zero i)
        ramR := fun i hi => absurd hi (Nat.not_lt_zero i)
        conjQ := fun i hi => absurd hi (Nat.not_lt_zero i)
        conjR := fun i hi => absurd hi (Nat.not_lt_zero i)
        crossQ := fun i hi => absurd hi (Nat.not_lt_zero i)
        crossR := fun i hi => absurd hi (Nat.not_lt_zero i)
        ne := fun i hi => absurd hi (Nat.not_lt_zero i)
        stabQ := fun i hi => absurd hi (Nat.not_lt_zero i)
        stabR := fun i hi => absurd hi (Nat.not_lt_zero i) }⟩
  | succ n ih =>
    obtain ⟨S, Q, R, z, hst⟩ := ih
    exact exists_isTwoPlaceFamily_succ_zpowers hp hodd hζ hres hTr hT hTrst hTnst hpTn hrepr hcunr
      hcfree hg hc hcT hcn hDgal hDc hsplit hram hst

end Step

end InverseGalois.CFT

import Mathlib
import InverseGalois.CFT.Global.Existence
import InverseGalois.CFT.Global.HilbertBimul
import InverseGalois.CFT.Global.SquareClassApprox

/-!
# Serre's existence theorem

A family of signs indexed by the places of the rational field, one for each member of a finite
family of nonzero integers, is realized by the Hilbert symbols of a single rational number as soon
as it is realized place by place and its product over all places is one.  The second condition is
forced by reciprocity and the first is obviously necessary, so the theorem says that these are the
only obstructions.

The reduction to the case already treated, where the signs are trivial on the bad set, is by weak
approximation: a rational number lying in the same square class as the prescribed local witness at
each place of the bad set, and of the prescribed sign, twists the signs into ones that are trivial
there.  The twisted family still has product one over all places, again by reciprocity, and its
local realizability is inherited by multiplying the local witnesses by the approximating number.

## Main results

* `InverseGalois.CFT.hilbertSymbolAt_congr_of_isSquare_div`: the symbol at a finite place depends
  on its second argument only through its local square class.
* `InverseGalois.CFT.hilbertSymbol_real_congr_sign`: the symbol at the real place depends on its
  second argument only through its sign.
* `InverseGalois.CFT.exists_rat_hilbert_prescribed`: **Serre's existence theorem**.
-/

namespace InverseGalois.CFT

open Local

/-- **The symbol at a finite place depends on its second argument only through its local square
class.** -/
theorem hilbertSymbolAt_congr_of_isSquare_div {p : Nat.Primes} {a u v : ℚ} (hu : u ≠ 0)
    (hv : v ≠ 0) (h : IsSquare (((u : ℚ_[(p : ℕ)])) / ((v : ℚ_[(p : ℕ)])))) :
    hilbertSymbolAt p a u = hilbertSymbolAt p a v := by
  obtain ⟨c, hc⟩ := h
  have hup : ((u : ℚ_[(p : ℕ)])) ≠ 0 := by simpa using hu
  have hvp : ((v : ℚ_[(p : ℕ)])) ≠ 0 := by simpa using hv
  rw [div_eq_iff hvp] at hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_mul, zero_mul] at hc
    exact hup hc
  unfold hilbertSymbolAt
  rw [show ((u : ℚ_[(p : ℕ)])) = ((v : ℚ_[(p : ℕ)])) * c ^ 2 by linear_combination hc,
    hilbertSymbol_mul_sq_right _ _ _ hc0]

/-- **The symbol at the real place depends on its second argument only through its sign.** -/
theorem hilbertSymbol_real_congr_sign {a u v : ℚ} (ha : a ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (h : 0 < u ↔ 0 < v) :
    hilbertSymbol ((a : ℝ)) ((u : ℝ)) = hilbertSymbol ((a : ℝ)) ((v : ℝ)) := by
  have haR : ((a : ℝ)) ≠ 0 := by simpa using ha
  have huR : ((u : ℝ)) ≠ 0 := by simpa using hu
  have hvR : ((v : ℝ)) ≠ 0 := by simpa using hv
  have hq : u < 0 ↔ v < 0 := by
    constructor
    · intro hlt
      rcases lt_trichotomy v 0 with h1 | h1 | h1
      · exact h1
      · exact absurd h1 hv
      · exact absurd (h.2 h1) (not_lt.2 hlt.le)
    · intro hlt
      rcases lt_trichotomy u 0 with h1 | h1 | h1
      · exact h1
      · exact absurd h1 hu
      · exact absurd (h.1 h1) (not_lt.2 hlt.le)
  have hneg : ((u : ℝ) < 0 ↔ ((v : ℝ) < 0)) := by
    constructor
    · intro hlt
      have hu' : u < 0 := by exact_mod_cast hlt
      exact_mod_cast hq.1 hu'
    · intro hlt
      have hv' : v < 0 := by exact_mod_cast hlt
      exact_mod_cast hq.2 hv'
  rw [hilbertSymbol_real _ _ haR huR, hilbertSymbol_real _ _ haR hvR]
  exact if_congr (and_congr_right fun _ => hneg) rfl rfl

/-- **Serre's existence theorem.**  Signs prescribed at every place for a finite family of nonzero
integers, trivial outside a finite set of primes, are the Hilbert symbols of one and the same
rational number as soon as they are realized separately at each place and their product over all
places is one. -/
theorem exists_rat_hilbert_prescribed {I : Type*} [Fintype I] (a : I → ℤ) (ha : ∀ i, a i ≠ 0)
    (ε : I → Nat.Primes → ℤ) (e : I → ℤ) (T : Finset Nat.Primes)
    (hTout : ∀ p ∉ T, ∀ i, ε i p = 1) (hprod : ∀ i, e i * ∏ p ∈ T, ε i p = 1)
    (hlocp : ∀ p : Nat.Primes, ∃ w : ℚ, w ≠ 0 ∧ ∀ i, hilbertSymbolAt p ((a i : ℚ)) w = ε i p)
    (hlocr : ∃ w : ℚ, w ≠ 0 ∧ ∀ i, hilbertSymbol ((((a i : ℚ)) : ℝ)) ((w : ℝ)) = e i) :
    ∃ x : ℚ, x ≠ 0 ∧ (∀ (i : I) (p : Nat.Primes), hilbertSymbolAt p ((a i : ℚ)) x = ε i p) ∧
      (∀ i, hilbertSymbol ((((a i : ℚ)) : ℝ)) ((x : ℝ)) = e i) := by
  classical
  have hai : ∀ i, ((a i : ℚ)) ≠ 0 := fun i => Int.cast_ne_zero.2 (ha i)
  choose w hw0 hwsym using hlocp
  obtain ⟨v, hv0, hvsym⟩ := hlocr
  -- the bad set: the dyadic place, the support of the signs, and the divisors of the `a i`
  set S : Finset Nat.Primes :=
    insert primeTwo (T ∪ Finset.univ.biUnion fun i => (finite_setOf_prime_dvd (ha i)).toFinset)
    with hSdef
  have hS2 : primeTwo ∈ S := Finset.mem_insert_self _ _
  have hTS : ∀ p ∈ T, p ∈ S := fun p hp => Finset.mem_insert_of_mem (Finset.mem_union_left _ hp)
  have hSa : ∀ (i : I) (p : Nat.Primes), ((p : ℕ) : ℤ) ∣ a i → p ∈ S := fun i p hd =>
    Finset.mem_insert_of_mem (Finset.mem_union_right _
      (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, by simpa using hd⟩))
  -- a global number in the prescribed local square class at every place of the bad set
  obtain ⟨u, hu0, husign, husq⟩ :=
    exists_rat_isSquare_div_sign S (fun p => ((w p : ℚ_[(p : ℕ)]))) (fun p _ => by
      simpa using hw0 p) hv0
  have huS : ∀ (i : I) (p : Nat.Primes), p ∈ S → hilbertSymbolAt p ((a i : ℚ)) u = ε i p := by
    intro i p hp
    rw [hilbertSymbolAt_congr_of_isSquare_div hu0 (hw0 p) (husq p hp)]
    exact hwsym p i
  have hur : ∀ i, hilbertSymbol ((((a i : ℚ)) : ℝ)) ((u : ℝ)) = e i := by
    intro i
    rw [hilbertSymbol_real_congr_sign (hai i) hu0 hv0 husign]
    exact hvsym i
  -- the twisted signs, trivial on the bad set
  set δ : I → Nat.Primes → ℤ := fun i p => ε i p * hilbertSymbolAt p ((a i : ℚ)) u with hδdef
  have hεsgn : ∀ (i : I) (p : Nat.Primes), ε i p = 1 ∨ ε i p = -1 := by
    intro i p
    rw [← hwsym p i]
    exact hilbertSymbolAt_eq_one_or _ _ _
  have hδsgn : ∀ (i : I) (p : Nat.Primes), δ i p = 1 ∨ δ i p = -1 := by
    intro i p
    rcases hεsgn i p with h1 | h1
    · rcases hilbertSymbolAt_eq_one_or p ((a i : ℚ)) u with h2 | h2
      · left; rw [hδdef]; simp only []; rw [h1, h2]; ring
      · right; rw [hδdef]; simp only []; rw [h1, h2]; ring
    · rcases hilbertSymbolAt_eq_one_or p ((a i : ℚ)) u with h2 | h2
      · right; rw [hδdef]; simp only []; rw [h1, h2]; ring
      · left; rw [hδdef]; simp only []; rw [h1, h2]; ring
  have hδS : ∀ (i : I) (p : Nat.Primes), p ∈ S → δ i p = 1 := by
    intro i p hp
    rw [hδdef]
    simp only []
    rw [huS i p hp]
    rcases hεsgn i p with h1 | h1
    · rw [h1]; ring
    · rw [h1]; ring
  -- a finite set carrying everything
  set U : Finset Nat.Primes := S ∪ Finset.univ.biUnion fun i =>
    (finite_mulSupport_hilbertSymbolAt (hai i) hu0).toFinset with hUdef
  have hSU : ∀ p ∈ S, p ∈ U := fun p hp => Finset.mem_union_left _ hp
  have hUout : ∀ p ∉ U, ∀ i, hilbertSymbolAt p ((a i : ℚ)) u = 1 := by
    intro p hp i
    by_contra hcon
    exact hp (Finset.mem_union_right _
      (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, by simpa using hcon⟩))
  set T' : Finset Nat.Primes := U.filter fun p => ∃ i, δ i p = -1 with hT'def
  have hT'U : T' ⊆ U := Finset.filter_subset _ _
  have hdisj : ∀ p ∈ S, p ∉ T' := by
    intro p hp hmem
    obtain ⟨i, hi⟩ := (Finset.mem_filter.1 hmem).2
    rw [hδS i p hp] at hi
    norm_num at hi
  have hT'out : ∀ p ∉ T', ∀ i, δ i p = 1 := by
    intro p hp i
    by_cases hU : p ∈ U
    · rcases hδsgn i p with h1 | h1
      · exact h1
      · exact absurd (Finset.mem_filter.2 ⟨hU, ⟨i, h1⟩⟩) hp
    · have hεp : ε i p = 1 := hTout p (fun hc => hU (hSU p (hTS p hc))) i
      rw [hδdef]
      simp only []
      rw [hεp, hUout p hU i]
      ring
  have hT'in : ∀ p ∈ T', ∃ i, δ i p = -1 := fun p hp => (Finset.mem_filter.1 hp).2
  -- the product of the twisted signs over the finite places is one
  have hprodU : ∀ i, ∏ p ∈ U, hilbertSymbolAt p ((a i : ℚ)) u = e i := by
    intro i
    have hrec := hilbertProduct_eq_one (hai i) hu0
    have hsub := hilbertProduct_eq_prod_of_subset ((a i : ℚ)) u U
      (fun p hp => hUout p hp i)
    rw [hrec, hur i] at hsub
    have hesgn : e i = 1 ∨ e i = -1 := by
      rw [← hvsym i]
      exact hilbertSymbol_eq_one_or _ _
    rcases hesgn with h1 | h1
    · rw [h1] at hsub ⊢
      linarith [hsub]
    · rw [h1] at hsub ⊢
      linarith [hsub]
  have hprod' : ∀ i, ∏ p ∈ T', δ i p = 1 := by
    intro i
    rw [Finset.prod_subset hT'U fun p hpU hpT => hT'out p hpT i]
    have hsplit : ∏ p ∈ U, δ i p =
        (∏ p ∈ U, ε i p) * ∏ p ∈ U, hilbertSymbolAt p ((a i : ℚ)) u := by
      rw [← Finset.prod_mul_distrib]
    rw [hsplit, hprodU i, ← Finset.prod_subset (fun p hp => hSU p (hTS p hp))
      (fun p _ hpT => hTout p hpT i), mul_comm]
    exact hprod i
  have hloc' : ∀ p ∈ T', ∃ z : ℚ, z ≠ 0 ∧ ∀ i, hilbertSymbolAt p ((a i : ℚ)) z = δ i p := by
    intro p _
    refine ⟨w p * u, mul_ne_zero (hw0 p) hu0, fun i => ?_⟩
    rw [hilbertSymbolAt_mul_right' (hai i) (hw0 p) hu0, hwsym p i]
  obtain ⟨z, hzpos, hzsym⟩ :=
    exists_int_hilbert_prescribed a ha δ S T' hS2 hSa hdisj hT'out hT'in hprod' hloc'
  have hz0 : ((z : ℚ)) ≠ 0 := Int.cast_ne_zero.2 hzpos.ne'
  refine ⟨((z : ℚ)) * u, mul_ne_zero hz0 hu0, fun i p => ?_, fun i => ?_⟩
  · rw [hilbertSymbolAt_mul_right' (hai i) hz0 hu0, hzsym i p, hδdef]
    simp only []
    rcases hilbertSymbolAt_eq_one_or p ((a i : ℚ)) u with h2 | h2
    · rw [h2]; ring
    · rw [h2]; ring
  · have hcast : ((((z : ℚ)) * u : ℚ) : ℝ) = ((((z : ℚ)) : ℝ)) * ((u : ℝ)) := by push_cast; ring
    rw [hcast, hilbertSymbol_real_mul_right _ _ _ (by simpa using hai i)
      (by simpa using hz0) (by simpa using hu0), hur i,
      hilbertSymbol_real_of_pos_right (by simpa using hai i) (by exact_mod_cast hzpos), one_mul]

/-- **Serre's existence theorem for a pair of integers**, in a form free of indexed families. -/
theorem exists_rat_hilbert_prescribed_two {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (α β : Nat.Primes → ℤ) (ea eb : ℤ) (T : Finset Nat.Primes)
    (hTa : ∀ p ∉ T, α p = 1) (hTb : ∀ p ∉ T, β p = 1)
    (hproda : ea * ∏ p ∈ T, α p = 1) (hprodb : eb * ∏ p ∈ T, β p = 1)
    (hlocp : ∀ p : Nat.Primes, ∃ w : ℚ, w ≠ 0 ∧
      hilbertSymbolAt p ((a : ℚ)) w = α p ∧ hilbertSymbolAt p ((b : ℚ)) w = β p)
    (hlocr : ∃ w : ℚ, w ≠ 0 ∧ hilbertSymbol ((((a : ℚ)) : ℝ)) ((w : ℝ)) = ea ∧
      hilbertSymbol ((((b : ℚ)) : ℝ)) ((w : ℝ)) = eb) :
    ∃ x : ℚ, x ≠ 0 ∧ (∀ p : Nat.Primes, hilbertSymbolAt p ((a : ℚ)) x = α p) ∧
      (∀ p : Nat.Primes, hilbertSymbolAt p ((b : ℚ)) x = β p) ∧
      hilbertSymbol ((((a : ℚ)) : ℝ)) ((x : ℝ)) = ea ∧
      hilbertSymbol ((((b : ℚ)) : ℝ)) ((x : ℝ)) = eb := by
  obtain ⟨x, hx0, hxp, hxr⟩ :=
    exists_rat_hilbert_prescribed (I := Fin 2) ![a, b] (Fin.forall_fin_two.2 ⟨ha, hb⟩)
      ![α, β] ![ea, eb] T
      (fun p hp => Fin.forall_fin_two.2 ⟨hTa p hp, hTb p hp⟩)
      (Fin.forall_fin_two.2 ⟨hproda, hprodb⟩)
      (fun p => by
        obtain ⟨w, hw0, hwa, hwb⟩ := hlocp p
        exact ⟨w, hw0, Fin.forall_fin_two.2 ⟨hwa, hwb⟩⟩)
      (by
        obtain ⟨w, hw0, hwa, hwb⟩ := hlocr
        exact ⟨w, hw0, Fin.forall_fin_two.2 ⟨hwa, hwb⟩⟩)
  exact ⟨x, hx0, fun p => hxp 0 p, fun p => hxp 1 p, hxr 0, hxr 1⟩

end InverseGalois.CFT

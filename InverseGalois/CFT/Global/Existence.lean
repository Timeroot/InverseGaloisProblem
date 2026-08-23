import Mathlib
import InverseGalois.CFT.Global.LocalSquare
import InverseGalois.CFT.Global.OddValuation
import InverseGalois.CFT.Global.Reciprocity

/-!
# Prescribing the Hilbert symbols of a rational number

Given finitely many nonzero rationals `a i` and a sign `ε i v` at each place `v`, when can one
find a single rational `x` whose Hilbert symbol against `a i` at `v` is `ε i v`?  Two conditions
are clearly necessary: each sign must be attainable locally, and by reciprocity the product of the
signs `ε i v` over all places must be one.  Serre's existence theorem says that they are also
sufficient.

The heart of the matter is the case where the signs are already trivial at every place in the
"bad" set `S`, which is to say at the dyadic place, at the real place and at every prime dividing
one of the `a i`.  The remaining places carrying a nontrivial sign form a set `T` disjoint from
`S`, and one takes `x = A q` where `A` is the product of the primes of `T` and `q` is a prime
congruent to `A` modulo `8 ∏_{ℓ ∈ S} ℓ`, supplied by Dirichlet's theorem.  Then `x ≡ A ^ 2` modulo
that number, so `x` is a square in each completion attached to `S`, giving the trivial sign there;
at a prime of `T` the number `x` has valuation exactly one, so the symbol is a Legendre symbol,
which is what the local hypothesis says the sign is; away from `S ∪ T` both arguments are units at
an odd place; and the value at the auxiliary prime `q` is forced by reciprocity.

## Main results

* `InverseGalois.CFT.isSquare_padic_of_odd_congr`: a rational integer congruent to a nonzero
  square modulo an odd prime is a square in the corresponding field of `p`-adic numbers.
* `InverseGalois.CFT.isSquare_padic_two_of_congr`: a rational integer congruent to one modulo
  eight is a dyadic square.
* `InverseGalois.CFT.exists_int_hilbert_prescribed`: the existence theorem in the case where the
  prescribed signs are trivial on the bad set.
-/

namespace InverseGalois.CFT

open Local

/-- **A rational integer congruent to a nonzero square modulo an odd prime is a square in the
field of `p`-adic numbers**: its residue is a nonzero square, and Hensel's lemma lifts it. -/
theorem isSquare_padic_of_odd_congr {p : Nat.Primes} (hp : (p : ℕ) ≠ 2) {x A : ℤ}
    (hA : ¬ ((p : ℕ) : ℤ) ∣ A) (h : ((p : ℕ) : ℤ) ∣ x - A ^ 2) :
    IsSquare (((x : ℚ) : ℚ_[(p : ℕ)])) := by
  have hxA : ((x : ZMod (p : ℕ))) = ((A : ZMod (p : ℕ))) ^ 2 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (x - A ^ 2) (p : ℕ)).2 h
    push_cast at this
    linear_combination this
  have hxd : ¬ ((p : ℕ) : ℤ) ∣ x := by
    intro hd
    refine hA ?_
    have hA0 : ((A : ZMod (p : ℕ))) ^ 2 = 0 := by
      rw [← hxA, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hd
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hA0
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact this
  have hu : IsUnit ((x : ℤ_[(p : ℕ)])) := isUnit_intCast_of_not_dvd hxd
  have hsq : IsSquare (PadicInt.toZMod ((x : ℤ_[(p : ℕ)]))) := by
    rw [toZMod_intCast, hxA]
    exact ⟨(A : ZMod (p : ℕ)), by ring⟩
  have := isSquare_of_isSquare_toZMod hp hu hsq
  have hcast : (((x : ℚ)) : ℚ_[(p : ℕ)]) = (((x : ℤ_[(p : ℕ)])) : ℚ_[(p : ℕ)]) := by
    rw [PadicInt.coe_intCast]
    push_cast
    ring
  rw [hcast]
  exact (isSquare_coe_iff hu).2 this

/-- **A rational integer congruent to one modulo eight is a dyadic square.** -/
theorem isSquare_padic_two_of_congr {x : ℤ} (h : (8 : ℤ) ∣ x - 1) :
    IsSquare (((x : ℚ) : ℚ_[2])) := by
  have hres : PadicInt.toZModPow 3 ((x : ℤ_[2])) = 1 := by
    have : ((x : ZMod 8)) = 1 := by
      obtain ⟨k, hk⟩ := h
      have : ((x - 1 : ℤ) : ZMod 8) = 0 := by
        rw [hk]
        push_cast
        rw [show (8 : ZMod 8) = 0 by decide]
        ring
      push_cast at this
      linear_combination this
    rw [show ((x : ℤ_[2])) = ((x : ℤ) : ℤ_[2]) from rfl]
    rw [map_intCast]
    exact this
  have hsq : IsSquare ((x : ℤ_[2])) := isSquare_of_toZModPow_three_eq_one hres
  have hcast : (((x : ℚ)) : ℚ_[2]) = (((x : ℤ_[2])) : ℚ_[2]) := by
    rw [PadicInt.coe_intCast]
    push_cast
    ring
  rw [hcast]
  obtain ⟨r, hr⟩ := hsq
  exact ⟨(r : ℚ_[2]), by rw [hr]; push_cast; ring⟩

/-- **The square of an odd integer is congruent to one modulo eight.** -/
theorem eight_dvd_sq_sub_one_of_odd {A : ℤ} (hA : ¬ (2 : ℤ) ∣ A) : (8 : ℤ) ∣ A ^ 2 - 1 := by
  rcases Int.even_or_odd A with hev | hodd
  · obtain ⟨k, hk⟩ := hev
    exact absurd ⟨k, by linarith⟩ hA
  · obtain ⟨k, hk⟩ := hodd
    obtain ⟨m, hm⟩ := Int.even_mul_succ_self k
    exact ⟨m, by rw [hk]; linear_combination 4 * hm⟩

/-- Two distinct primes are coprime as integers. -/
theorem isCoprime_intCast_primes {p q : Nat.Primes} (h : p ≠ q) :
    IsCoprime (((p : ℕ) : ℤ)) (((q : ℕ) : ℤ)) := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
  exact (Nat.coprime_primes p.2 q.2).2 fun hc => h (Subtype.ext hc)

/-- The product of the primes in a finite set is positive. -/
theorem prod_primes_pos (T : Finset Nat.Primes) : 0 < ∏ p ∈ T, ((p : ℕ) : ℤ) :=
  Finset.prod_pos fun p _ => by exact_mod_cast p.2.pos

/-- A prime outside a finite set of primes does not divide the product of that set. -/
theorem not_dvd_prod_primes {l : Nat.Primes} {T : Finset Nat.Primes} (h : l ∉ T) :
    ¬ (((l : ℕ) : ℤ)) ∣ ∏ p ∈ T, ((p : ℕ) : ℤ) := by
  intro hd
  have hp : Prime (((l : ℕ) : ℤ)) := Nat.prime_iff_prime_int.mp l.2
  obtain ⟨r, hr, hdr⟩ := (hp.dvd_finset_prod_iff _).1 hd
  exact h (by rwa [show l = r from
    Subtype.ext ((Nat.prime_dvd_prime_iff_eq l.2 r.2).1 (by exact_mod_cast hdr))])

/-- A prime of a finite set of primes divides the product of that set exactly once. -/
theorem exists_eq_mul_prod_primes {l : Nat.Primes} {T : Finset Nat.Primes} (h : l ∈ T) :
    ∃ w : ℤ, (∏ p ∈ T, ((p : ℕ) : ℤ)) = ((l : ℕ) : ℤ) * w ∧ ¬ (((l : ℕ) : ℤ)) ∣ w := by
  classical
  exact ⟨∏ p ∈ T.erase l, ((p : ℕ) : ℤ), (Finset.mul_prod_erase T _ h).symm,
    not_dvd_prod_primes (Finset.notMem_erase l T)⟩

/-- **Serre's existence theorem, in the case where the prescribed signs are trivial on the bad
set.**  Here `S` is a finite set of primes containing the dyadic one and every prime dividing one
of the `a i`, the set `T` of primes carrying a nontrivial sign is disjoint from `S`, the sign is
attainable at each prime of `T` by a single rational, and the product of the signs over `T` is
one.  Then a single positive integer realizes all the prescribed signs at once, and being positive
it also realizes the trivial sign at the real place. -/
theorem exists_int_hilbert_prescribed {I : Type*} (a : I → ℤ) (ha : ∀ i, a i ≠ 0)
    (ε : I → Nat.Primes → ℤ) (S T : Finset Nat.Primes) (hS2 : primeTwo ∈ S)
    (hSa : ∀ (i : I) (p : Nat.Primes), ((p : ℕ) : ℤ) ∣ a i → p ∈ S)
    (hdisj : ∀ p ∈ S, p ∉ T) (hTout : ∀ p ∉ T, ∀ i, ε i p = 1)
    (hTin : ∀ p ∈ T, ∃ i, ε i p = -1) (hprod : ∀ i, ∏ p ∈ T, ε i p = 1)
    (hloc : ∀ p ∈ T, ∃ y : ℚ, y ≠ 0 ∧ ∀ i, hilbertSymbolAt p ((a i : ℚ)) y = ε i p) :
    ∃ x : ℤ, 0 < x ∧ ∀ (i : I) (p : Nat.Primes),
      hilbertSymbolAt p ((a i : ℚ)) ((x : ℚ)) = ε i p := by
  classical
  set A : ℤ := ∏ p ∈ T, ((p : ℕ) : ℤ) with hAdef
  set N : ℕ := 8 * ∏ p ∈ S, (p : ℕ) with hNdef
  have hApos : 0 < A := prod_primes_pos T
  have hNpos : 0 < N := Nat.mul_pos (by norm_num) (Finset.prod_pos fun p _ => p.2.pos)
  have hNZ : ((N : ℕ) : ℤ) = 8 * ∏ p ∈ S, ((p : ℕ) : ℤ) := by
    rw [hNdef]; push_cast; ring
  have hAodd : ¬ (2 : ℤ) ∣ A := by
    have h := not_dvd_prod_primes (hdisj primeTwo hS2)
    rw [← hAdef] at h
    simpa [primeTwo] using h
  have hAnd : ∀ l ∈ S, ¬ (((l : ℕ) : ℤ)) ∣ A := fun l hl => by
    have h := not_dvd_prod_primes (hdisj l hl)
    rwa [← hAdef] at h
  have hSdvdN : ∀ l ∈ S, (((l : ℕ) : ℤ)) ∣ ((N : ℕ) : ℤ) := fun l hl => by
    rw [hNZ]
    exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun p : Nat.Primes => ((p : ℕ) : ℤ)) hl) 8
  -- an auxiliary prime congruent to `A` modulo `N`
  have hcop : IsCoprime A ((N : ℤ)) := by
    rw [hNZ, hAdef]
    refine IsCoprime.prod_left fun p hpT => IsCoprime.mul_right ?_ ?_
    · have hne : p ≠ primeTwo := fun hc => hdisj primeTwo hS2 (hc ▸ hpT)
      have h2 : IsCoprime (((p : ℕ) : ℤ)) ((2 : ℤ)) := by
        simpa [primeTwo] using isCoprime_intCast_primes hne
      have h8 := h2.pow_right (n := 3)
      norm_num at h8
      exact h8
    · exact IsCoprime.prod_right fun r hrS => isCoprime_intCast_primes fun hc =>
        hdisj r hrS (hc ▸ hpT)
  obtain ⟨q, hqgt, hqprime, hqmod⟩ :=
    Nat.forall_exists_prime_gt_and_zmodEq (∑ p ∈ S ∪ T, (p : ℕ)) hNpos.ne' hcop
  set qP : Nat.Primes := ⟨q, hqprime⟩ with hqPdef
  have hqnot : qP ∉ S ∪ T := by
    intro hmem
    have hle : ((qP : Nat.Primes) : ℕ) ≤ ∑ p ∈ S ∪ T, (p : ℕ) :=
      Finset.single_le_sum (f := fun p : Nat.Primes => (p : ℕ)) (fun _ _ => Nat.zero_le _) hmem
    exact absurd hqgt (not_lt.2 hle)
  have hqnotS : qP ∉ S := fun h => hqnot (Finset.mem_union_left _ h)
  have hqnotT : qP ∉ T := fun h => hqnot (Finset.mem_union_right _ h)
  have hxpos : 0 < A * (q : ℤ) := mul_pos hApos (by exact_mod_cast hqprime.pos)
  have hcong : ((N : ℕ) : ℤ) ∣ A * (q : ℤ) - A ^ 2 := by
    obtain ⟨k, hk⟩ := hqmod.dvd
    exact ⟨-(A * k), by linear_combination (-A) * hk⟩
  -- the symbols away from the auxiliary prime
  have hkey : ∀ (i : I) (l : Nat.Primes), l ≠ qP →
      hilbertSymbolAt l ((a i : ℚ)) (((A * (q : ℤ) : ℤ) : ℚ)) = ε i l := by
    intro i l hlq
    by_cases hlS : l ∈ S
    · rw [hTout l (hdisj l hlS) i]
      have hdvdl : (((l : ℕ) : ℤ)) ∣ A * (q : ℤ) - A ^ 2 := dvd_trans (hSdvdN l hlS) hcong
      have hsq : IsSquare ((((A * (q : ℤ) : ℤ) : ℚ)) : ℚ_[(l : ℕ)]) := by
        rcases eq_or_ne (l : ℕ) 2 with h2 | h2
        · have hl2 : l = primeTwo := Subtype.ext h2
          subst hl2
          have h8N : (8 : ℤ) ∣ ((N : ℕ) : ℤ) := by rw [hNZ]; exact Dvd.intro _ rfl
          obtain ⟨u, hu⟩ := dvd_trans h8N hcong
          obtain ⟨v, hv⟩ := eight_dvd_sq_sub_one_of_odd hAodd
          exact isSquare_padic_two_of_congr ⟨u + v, by linear_combination hu + hv⟩
        · exact isSquare_padic_of_odd_congr h2 (hAnd l hlS) hdvdl
      unfold hilbertSymbolAt
      exact hilbertSymbol_of_isSquare_right _ _ hsq
    · have hl2 : (l : ℕ) ≠ 2 := fun h => hlS (by rwa [show l = primeTwo from Subtype.ext h])
      have hai : ¬ (((l : ℕ) : ℤ)) ∣ a i := fun hd => hlS (hSa i l hd)
      have hlprime : Prime (((l : ℕ) : ℤ)) := Nat.prime_iff_prime_int.mp l.2
      have hlq' : ¬ (((l : ℕ) : ℤ)) ∣ (q : ℤ) := fun hd =>
        hlq (Subtype.ext ((Nat.prime_dvd_prime_iff_eq l.2 hqprime).1 (by exact_mod_cast hd)))
      by_cases hlT : l ∈ T
      · obtain ⟨w, hw, hwnd⟩ := exists_eq_mul_prod_primes hlT
        rw [← hAdef] at hw
        have hwq : ¬ (((l : ℕ) : ℤ)) ∣ w * (q : ℤ) := fun hd => by
          rcases hlprime.dvd_mul.1 hd with h | h
          · exact hwnd h
          · exact hlq' h
        have hsymx : hilbertSymbolAt l ((a i : ℚ)) (((A * (q : ℤ) : ℤ) : ℚ))
            = legendreSym (l : ℕ) (a i) := by
          rw [show A * (q : ℤ) = ((l : ℕ) : ℤ) * (w * (q : ℤ)) by rw [hw]; ring]
          exact hilbertSymbolAt_ramified_eq_legendreSym hl2 hai hwq
        obtain ⟨y, hy0, hysym⟩ := hloc l hlT
        have hodd : ¬ Even (((y : ℚ_[(l : ℕ)])).valuation) := by
          intro hev
          obtain ⟨i₀, hi₀⟩ := hTin l hlT
          have hai₀ : ¬ (((l : ℕ) : ℤ)) ∣ a i₀ := fun hd => hlS (hSa i₀ l hd)
          have hone := hilbertSymbolAt_odd_of_even_valuation hl2 hai₀ hy0 hev
          rw [hysym i₀, hi₀] at hone
          norm_num at hone
        have hyleg := hilbertSymbolAt_odd_of_odd_valuation hl2 hai hy0 hodd
        rw [hysym i] at hyleg
        rw [hsymx]
        exact hyleg.symm
      · rw [hTout l hlT i]
        have hxnd : ¬ (((l : ℕ) : ℤ)) ∣ A * (q : ℤ) := fun hd => by
          rcases hlprime.dvd_mul.1 hd with h | h
          · rw [hAdef] at h
            exact not_dvd_prod_primes hlT h
          · exact hlq' h
        exact hilbertSymbolAt_intCast_eq_one hl2 hai hxnd
  refine ⟨A * (q : ℤ), hxpos, fun i l => ?_⟩
  by_cases hlq : l = qP
  · subst hlq
    rw [hTout qP hqnotT i]
    have hax : ((a i : ℚ)) ≠ 0 := by exact_mod_cast ha i
    have hxq : (((A * (q : ℤ) : ℤ)) : ℚ) ≠ 0 := by exact_mod_cast hxpos.ne'
    have hrec := hilbertProduct_eq_one hax hxq
    have hsub := hilbertProduct_eq_prod_of_subset ((a i : ℚ)) (((A * (q : ℤ) : ℤ)) : ℚ)
      (insert qP T) (fun p hp => by
        rw [hkey i p (fun hc => hp (by rw [hc]; exact Finset.mem_insert_self _ _))]
        exact hTout p (fun hc => hp (Finset.mem_insert_of_mem hc)) i)
    have hreal : hilbertSymbol ((((a i : ℚ)) : ℝ)) (((((A * (q : ℤ) : ℤ)) : ℚ) : ℝ)) = 1 :=
      hilbertSymbol_real_of_pos_right (by exact_mod_cast ha i) (by exact_mod_cast hxpos)
    have hT1 : ∏ p ∈ T, hilbertSymbolAt p ((a i : ℚ)) (((A * (q : ℤ) : ℤ)) : ℚ) = 1 := by
      rw [Finset.prod_congr rfl fun p hp => hkey i p (fun hc => hqnotT (hc ▸ hp))]
      exact hprod i
    rw [hreal, one_mul, Finset.prod_insert hqnotT, hT1, mul_one] at hsub
    rw [← hsub, hrec]
  · exact hkey i l hlq

end InverseGalois.CFT

import Mathlib
import InverseGalois.CFT.Global.DescentTools
import InverseGalois.CFT.Global.LocalSquare
import InverseGalois.CFT.Global.Reciprocity
import InverseGalois.CFT.Global.SquarefreeCRT

/-!
# The Hasse principle for ternary quadratic forms over the rationals

A conic `z ^ 2 = a x ^ 2 + b y ^ 2` with nonzero rational coefficients has a rational point as soon
as it has a point over the reals and over every field of `p`-adic numbers.

The argument is Legendre's descent, in the arrangement of Serre's *Cours d'arithmétique*.  Both
coefficients may be taken to be squarefree integers, and the pair is ordered so that the first is
no larger than the second in absolute value.  If the larger one is a unit the statement is
immediate from the real hypothesis.  Otherwise each prime divisor `p` of the larger coefficient
divides it exactly once, so the local hypothesis at `p` says that the smaller coefficient is a
square modulo `p`; by the Chinese remainder theorem there is an integer `t`, reducible modulo the
larger coefficient into the interval of half its length, whose square is congruent to the smaller
coefficient.  The factorisation `t ^ 2 - a = b b'` produces a new coefficient `b'` strictly smaller
than `b`, the identity `t ^ 2 = a · 1 ^ 2 + (t ^ 2 - a) · 1 ^ 2` shows the form `⟨a, b b'⟩` is
isotropic over every field at once, and cancelling this from the hypotheses transports them to the
smaller pair.  The induction closes because the values of a binary form are a group under
multiplication, so isotropy of `⟨a, b'⟩` and of `⟨a, b b'⟩` gives isotropy of `⟨a, b⟩`.

## Main results

* `InverseGalois.CFT.hilbertSymbol_rat_of_forall_local`: the Hasse principle for the Hilbert
  symbol over the rationals.
* `InverseGalois.CFT.isHilbertIsotropic_rat_of_forall_local`: the same statement phrased as the
  existence of a rational point on a conic.
* `InverseGalois.CFT.hilbertSymbol_rat_of_forall_finite`: only the finite places are needed, the
  real place being determined by them through reciprocity.
-/

namespace InverseGalois.CFT

open Local

/-- **The descent, with the size of the pair of coefficients bounded in advance.** -/
theorem hilbertSymbol_int_of_forall_local_bounded (N : ℕ) : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
    Squarefree a → Squarefree b → a.natAbs + b.natAbs ≤ N →
    hilbertSymbol ((a : ℝ)) ((b : ℝ)) = 1 →
    (∀ p : Nat.Primes, hilbertSymbolAt p ((a : ℚ)) ((b : ℚ)) = 1) →
    hilbertSymbol ((a : ℚ)) ((b : ℚ)) = 1 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    have key : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 → Squarefree a → Squarefree b →
        a.natAbs + b.natAbs ≤ N → a.natAbs ≤ b.natAbs →
        hilbertSymbol ((a : ℝ)) ((b : ℝ)) = 1 →
        (∀ p : Nat.Primes, hilbertSymbolAt p ((a : ℚ)) ((b : ℚ)) = 1) →
        hilbertSymbol ((a : ℚ)) ((b : ℚ)) = 1 := by
      intro a b ha hb hsa hsb hN hab hreal hloc
      rcases Nat.lt_or_ge b.natAbs 2 with hb1 | hb1
      · have hA : a = 1 ∨ a = -1 := by omega
        have hB : b = 1 ∨ b = -1 := by omega
        rcases hB with rfl | rfl
        · exact hilbertSymbol_of_isSquare_right _ _ ⟨1, by norm_num⟩
        · rcases hA with rfl | rfl
          · exact hilbertSymbol_of_isSquare_left _ _ ⟨1, by norm_num⟩
          · exfalso
            rw [show (((-1 : ℤ)) : ℝ) = (-1 : ℝ) by norm_num,
              hilbertSymbol_real (-1 : ℝ) (-1 : ℝ) (by norm_num) (by norm_num)] at hreal
            norm_num at hreal
      · have haQ : ((a : ℚ)) ≠ 0 := Int.cast_ne_zero.2 ha
        have hbQ : ((b : ℚ)) ≠ 0 := Int.cast_ne_zero.2 hb
        have hsq : ∀ q : ℕ, q.Prime → ((q : ℤ)) ∣ b → IsSquare ((a : ZMod q)) := by
          intro q hq hqb
          by_cases hqa : ((q : ℤ)) ∣ a
          · have h0 : ((a : ZMod q)) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd a q).2 hqa
            rw [h0]
            exact ⟨0, by simp⟩
          · rcases eq_or_ne q 2 with rfl | hq2
            · have hall : ∀ x : ZMod 2, IsSquare x := by decide
              exact hall _
            · obtain ⟨w, hw⟩ := hqb
              have hqw : ¬ ((q : ℤ)) ∣ w := by
                intro hdvd
                obtain ⟨v, hv⟩ := hdvd
                have hdd : ((q : ℤ)) * ((q : ℤ)) ∣ b := ⟨v, by rw [hw, hv]; ring⟩
                have hu := hsb ((q : ℤ)) hdd
                rw [Int.isUnit_iff] at hu
                have h2 := hq.two_le
                omega
              have hloc2 := hloc ⟨q, hq⟩
              rw [hw] at hloc2
              exact isSquare_zmod_of_hilbertSymbolAt (p := ⟨q, hq⟩) hq2 hqa hqw hloc2
        obtain ⟨t, htdvd, htbd⟩ := exists_sq_sub_dvd hb hsb hsq
        obtain ⟨b', hb'⟩ := htdvd
        have hprod : ((b : ℚ)) * ((b' : ℚ)) = ((t : ℚ)) ^ 2 - ((a : ℚ)) := by
          exact_mod_cast hb'.symm
        have hprodR : ((b : ℝ)) * ((b' : ℝ)) = ((t : ℝ)) ^ 2 - ((a : ℝ)) := by
          exact_mod_cast hb'.symm
        rcases eq_or_ne b' 0 with rfl | hb'0
        · have hat : a = t ^ 2 := by
            rw [mul_zero] at hb'
            linarith
          rw [hat]
          exact hilbertSymbol_of_isSquare_left _ _ ⟨((t : ℚ)), by push_cast; ring⟩
        · have hb'Q : ((b' : ℚ)) ≠ 0 := Int.cast_ne_zero.2 hb'0
          have hbR : ((b : ℝ)) ≠ 0 := Int.cast_ne_zero.2 hb
          have hiso : hilbertSymbol ((a : ℚ)) (((b : ℚ)) * ((b' : ℚ))) = 1 := by
            rw [hprod]
            exact hilbertSymbol_sub_sq _ _
          have hisoR : hilbertSymbol ((a : ℝ)) (((b : ℝ)) * ((b' : ℝ))) = 1 := by
            rw [hprodR]
            exact hilbertSymbol_sub_sq _ _
          have hrealb' : hilbertSymbol ((a : ℝ)) ((b' : ℝ)) = 1 :=
            hilbertSymbol_of_mul hbR hreal hisoR
          have hlocb' : ∀ p : Nat.Primes, hilbertSymbolAt p ((a : ℚ)) ((b' : ℚ)) = 1 := by
            intro p
            refine hilbertSymbolAt_of_mul hbQ (hloc p) ?_
            rw [hprod]
            exact hilbertSymbolAt_sub_sq p _ _
          obtain ⟨b'', k, hb''0, hb''sf, hk0, hb'eq⟩ := exists_squarefree_mul_sq hb'0
          have hkQ : ((k : ℚ)) ≠ 0 := Int.cast_ne_zero.2 hk0
          have hkR : ((k : ℝ)) ≠ 0 := Int.cast_ne_zero.2 hk0
          have hcastQ : ((b' : ℚ)) = ((b'' : ℚ)) * ((k : ℚ)) ^ 2 := by exact_mod_cast hb'eq
          have hcastR : ((b' : ℝ)) = ((b'' : ℝ)) * ((k : ℝ)) ^ 2 := by exact_mod_cast hb'eq
          have hrealb'' : hilbertSymbol ((a : ℝ)) ((b'' : ℝ)) = 1 := by
            rw [hcastR, hilbertSymbol_mul_sq_right _ _ _ hkR] at hrealb'
            exact hrealb'
          have hlocb'' : ∀ p : Nat.Primes, hilbertSymbolAt p ((a : ℚ)) ((b'' : ℚ)) = 1 := by
            intro p
            have h := hlocb' p
            rw [hcastQ, hilbertSymbolAt_mul_sq_right p _ _ _ hkQ] at h
            exact h
          have habsle : |a| ≤ |b| := by
            rw [Int.abs_eq_natAbs a, Int.abs_eq_natAbs b]
            exact_mod_cast hab
          have hbpos : (0 : ℤ) < |b| := abs_pos.2 hb
          have hb1' : (2 : ℤ) ≤ |b| := by
            rw [Int.abs_eq_natAbs b]
            exact_mod_cast hb1
          have h4t : 4 * t ^ 2 ≤ b ^ 2 := by
            have h := mul_self_le_mul_self (by positivity) htbd
            rw [← sq_abs t, ← sq_abs b]
            nlinarith [h]
          have habsb' : |b| * |b'| = |t ^ 2 - a| := by rw [hb', abs_mul]
          have htri : |t ^ 2 - a| ≤ t ^ 2 + |a| := by
            have h1 := abs_add_le (t ^ 2) (-a)
            rw [abs_neg] at h1
            rw [sub_eq_add_neg]
            calc |t ^ 2 + -a| ≤ |t ^ 2| + |a| := h1
              _ = t ^ 2 + |a| := by rw [abs_of_nonneg (sq_nonneg t)]
          have e1 : 4 * (|b| * |b'|) ≤ 4 * (t ^ 2 + |a|) := by
            rw [habsb']
            linarith [htri]
          have e2 : 4 * (t ^ 2 + |a|) ≤ |b| ^ 2 + 4 * |b| := by
            rw [sq_abs]
            linarith [h4t, habsle]
          have e3 : |b| * (4 * |b'|) < |b| * (4 * |b|) := by
            nlinarith [e1, e2, hb1', hbpos,
              mul_nonneg (by linarith : (0 : ℤ) ≤ |b| - 2) (le_of_lt hbpos)]
          have hb'lt : |b'| < |b| := by
            have h := lt_of_mul_lt_mul_left e3 (le_of_lt hbpos)
            linarith
          have hk1 : (1 : ℤ) ≤ k ^ 2 := (one_le_sq_iff_one_le_abs k).2 (Int.one_le_abs hk0)
          have hb''le : |b''| ≤ |b'| := by
            have hfac : |b'| = |b''| * k ^ 2 := by
              rw [hb'eq, abs_mul, abs_of_nonneg (sq_nonneg k)]
            nlinarith [abs_nonneg b'', hfac, hk1]
          have hb''lt : b''.natAbs < b.natAbs := by
            have hlt : |b''| < |b| := lt_of_le_of_lt hb''le hb'lt
            rw [Int.abs_eq_natAbs b'', Int.abs_eq_natAbs b] at hlt
            exact_mod_cast hlt
          have hbound : a.natAbs + b''.natAbs < N := by omega
          have hIH := ih (a.natAbs + b''.natAbs) hbound a b'' ha hb''0 hsa hb''sf le_rfl
            hrealb'' hlocb''
          have h5 : hilbertSymbol ((a : ℚ)) ((b' : ℚ)) = 1 := by
            rw [hcastQ, hilbertSymbol_mul_sq_right _ _ _ hkQ]
            exact hIH
          exact hilbertSymbol_of_mul' hb'Q h5 hiso
    intro a b ha hb hsa hsb hN hreal hloc
    rcases le_total a.natAbs b.natAbs with h | h
    · exact key a b ha hb hsa hsb hN h hreal hloc
    · rw [hilbertSymbol_comm]
      refine key b a hb ha hsb hsa (by omega) h ?_ ?_
      · rw [hilbertSymbol_comm]
        exact hreal
      · intro p
        rw [hilbertSymbolAt_comm]
        exact hloc p

/-- **The Hasse principle for a pair of squarefree integers.** -/
theorem hilbertSymbol_int_of_forall_local {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hsa : Squarefree a) (hsb : Squarefree b)
    (hreal : hilbertSymbol ((a : ℝ)) ((b : ℝ)) = 1)
    (hloc : ∀ p : Nat.Primes, hilbertSymbolAt p ((a : ℚ)) ((b : ℚ)) = 1) :
    hilbertSymbol ((a : ℚ)) ((b : ℚ)) = 1 :=
  hilbertSymbol_int_of_forall_local_bounded (a.natAbs + b.natAbs) a b ha hb hsa hsb le_rfl
    hreal hloc

/-- **The Hasse principle for the Hilbert symbol over the rationals.**  A conic with nonzero
rational coefficients that has a point at every place has a rational point. -/
theorem hilbertSymbol_rat_of_forall_local {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hreal : hilbertSymbol ((a : ℝ)) ((b : ℝ)) = 1)
    (hloc : ∀ p : Nat.Primes, hilbertSymbolAt p a b = 1) :
    hilbertSymbol a b = 1 := by
  obtain ⟨m, c, hm0, hmsf, hc0, hac⟩ := exists_squarefree_intCast_mul_sq ha
  obtain ⟨n, d, hn0, hnsf, hd0, hbd⟩ := exists_squarefree_intCast_mul_sq hb
  have hcQ : c ≠ 0 := hc0
  have hdQ : d ≠ 0 := hd0
  have hcR : ((c : ℝ)) ≠ 0 := by simpa using hc0
  have hdR : ((d : ℝ)) ≠ 0 := by simpa using hd0
  have haR : ((a : ℝ)) = ((m : ℝ)) * ((c : ℝ)) ^ 2 := by rw [hac]; push_cast; ring
  have hbR : ((b : ℝ)) = ((n : ℝ)) * ((d : ℝ)) ^ 2 := by rw [hbd]; push_cast; ring
  have hrealmn : hilbertSymbol ((m : ℝ)) ((n : ℝ)) = 1 := by
    rw [haR, hbR, hilbertSymbol_mul_sq_left _ _ _ hcR,
      hilbertSymbol_mul_sq_right _ _ _ hdR] at hreal
    exact hreal
  have hlocmn : ∀ p : Nat.Primes, hilbertSymbolAt p ((m : ℚ)) ((n : ℚ)) = 1 := by
    intro p
    have h := hloc p
    rw [hac, hbd, hilbertSymbolAt_mul_sq_left p _ _ _ hcQ,
      hilbertSymbolAt_mul_sq_right p _ _ _ hdQ] at h
    exact h
  rw [hac, hbd, hilbertSymbol_mul_sq_left _ _ _ hcQ, hilbertSymbol_mul_sq_right _ _ _ hdQ]
  exact hilbertSymbol_int_of_forall_local hm0 hn0 hmsf hnsf hrealmn hlocmn

/-- **The Hasse principle, phrased as the existence of a rational point on a conic.** -/
theorem isHilbertIsotropic_rat_of_forall_local {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hreal : IsHilbertIsotropic ((a : ℝ)) ((b : ℝ)))
    (hloc : ∀ p : Nat.Primes, IsHilbertIsotropic ((a : ℚ_[(p : ℕ)])) ((b : ℚ_[(p : ℕ)]))) :
    IsHilbertIsotropic a b := by
  refine hilbertSymbol_eq_one_iff.1 (hilbertSymbol_rat_of_forall_local ha hb ?_ ?_)
  · exact hilbertSymbol_eq_one_iff.2 hreal
  · intro p
    exact hilbertSymbol_eq_one_iff.2 (hloc p)

/-- **The real place is redundant.**  If a conic with nonzero rational coefficients has a point
over every field of `p`-adic numbers then it has a rational point, the real place being supplied
by reciprocity. -/
theorem hilbertSymbol_rat_of_forall_finite {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hloc : ∀ p : Nat.Primes, hilbertSymbolAt p a b = 1) :
    hilbertSymbol a b = 1 := by
  refine hilbertSymbol_rat_of_forall_local ha hb ?_ hloc
  rw [← hilbertProduct_finite_eq_real ha hb]
  refine finprod_eq_one_of_forall_eq_one fun p => hloc p

end InverseGalois.CFT

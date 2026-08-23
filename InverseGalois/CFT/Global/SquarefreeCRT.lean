import Mathlib

/-!
# Squarefree representatives of square classes, and square roots modulo a squarefree number

This file collects elementary number theory used by descent arguments: the normalisation of a
square class by a squarefree representative, and a Chinese-remainder assembly of square roots
modulo a squarefree modulus out of square roots modulo each of its prime factors.

## Main results

* `exists_squarefree_mul_sq`: every nonzero integer is a nonzero squarefree integer times the
  square of a nonzero integer.
* `exists_squarefree_intCast_mul_sq`: every nonzero rational is a nonzero squarefree integer
  times the square of a nonzero rational.
* `isSquare_zmod_iff_dvd_sq_sub`: being a square in `ZMod n` is the existence of an integer `t`
  with `n ∣ t ^ 2 - a`.
* `isSquare_zmod_of_forall_prime`: for squarefree `n`, an integer that is a square modulo every
  prime factor of `n` is a square modulo `n`.
* `exists_sq_sub_dvd`: the same statement over `ℤ`, with the square root chosen in the interval
  of absolutely least residues.
-/

namespace InverseGalois.CFT

/-- Every nonzero integer is a nonzero squarefree integer times the square of a nonzero
integer. -/
theorem exists_squarefree_mul_sq {n : ℤ} (hn : n ≠ 0) :
    ∃ m k : ℤ, m ≠ 0 ∧ Squarefree m ∧ k ≠ 0 ∧ n = m * k ^ 2 := by
  obtain ⟨a, b, hab, ha⟩ := Nat.sq_mul_squarefree n.natAbs
  have hnabs : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn
  have hb0 : b ≠ 0 := by rintro rfl; exact hnabs (by simpa using hab.symm)
  have ha0 : a ≠ 0 := by rintro rfl; exact hnabs (by simpa using hab.symm)
  have habs : ((b : ℤ)) ^ 2 * (a : ℤ) = (n.natAbs : ℤ) := by exact_mod_cast hab
  have hbZ : ((b : ℤ)) ≠ 0 := Nat.cast_ne_zero.mpr hb0
  have haZ : ((a : ℤ)) ≠ 0 := Nat.cast_ne_zero.mpr ha0
  rcases lt_trichotomy n 0 with hlt | heq | hgt
  · refine ⟨-(a : ℤ), (b : ℤ), neg_ne_zero.mpr haZ, ?_, hbZ, ?_⟩
    · exact Int.squarefree_natAbs.mp (by simpa using ha)
    · have hna : ((n.natAbs : ℤ)) = -n := by
        rw [← Int.natAbs_neg]; exact Int.natAbs_of_nonneg (by linarith)
      rw [hna] at habs
      linear_combination habs
  · exact absurd heq hn
  · refine ⟨(a : ℤ), (b : ℤ), haZ, Int.squarefree_natCast.mpr ha, hbZ, ?_⟩
    have hna : ((n.natAbs : ℤ)) = n := Int.natAbs_of_nonneg hgt.le
    rw [hna] at habs
    linear_combination -habs

/-- Every nonzero rational is a nonzero squarefree integer times the square of a nonzero
rational. -/
theorem exists_squarefree_intCast_mul_sq {q : ℚ} (hq : q ≠ 0) :
    ∃ (m : ℤ) (c : ℚ), m ≠ 0 ∧ Squarefree m ∧ c ≠ 0 ∧ q = (m : ℚ) * c ^ 2 := by
  have hnum : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  have hdenN : q.den ≠ 0 := q.den_nz
  have hden : ((q.den : ℤ)) ≠ 0 := Nat.cast_ne_zero.mpr hdenN
  have hd : ((q.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hdenN
  obtain ⟨m, k, hm0, hm, hk0, hmk⟩ := exists_squarefree_mul_sq (mul_ne_zero hnum hden)
  refine ⟨m, (k : ℚ) / (q.den : ℚ), hm0, hm, div_ne_zero (Int.cast_ne_zero.mpr hk0) hd, ?_⟩
  have key : ((q.num : ℚ)) * ((q.den : ℚ)) = (m : ℚ) * (k : ℚ) ^ 2 := by exact_mod_cast hmk
  have hqd : ((q.num : ℚ)) = q * ((q.den : ℚ)) := (div_eq_iff hd).mp (Rat.num_div_den q)
  rw [div_pow, ← mul_div_assoc, eq_div_iff (pow_ne_zero 2 hd), ← key, hqd]
  ring

/-- Divisibility of `t ^ 2 - a` depends only on the class of `t` modulo the divisor. -/
theorem dvd_sq_sub_of_dvd_sub {b t u a : ℤ} (h : b ∣ t - u) (hu : b ∣ u ^ 2 - a) :
    b ∣ t ^ 2 - a := by
  have hexp : t ^ 2 - a = (t - u) * (t + u) + (u ^ 2 - a) := by ring
  rw [hexp]
  exact dvd_add (h.mul_right _) hu

/-- An integer is a square modulo `n` exactly when `n` divides `t ^ 2 - a` for some integer
`t`. -/
theorem isSquare_zmod_iff_dvd_sq_sub (n : ℕ) (a : ℤ) :
    IsSquare ((a : ZMod n)) ↔ ∃ t : ℤ, (n : ℤ) ∣ t ^ 2 - a := by
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨t, rfl⟩ := ZMod.intCast_surjective r
    refine ⟨t, ?_⟩
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    push_cast
    rw [hr]
    ring
  · rintro ⟨t, ht⟩
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub] at ht
    refine ⟨(t : ZMod n), ?_⟩
    rw [ht]
    push_cast
    ring

/-- If a squarefree natural number has, at each of its prime factors, an integer square root of
`a`, then it has one itself. -/
theorem exists_dvd_sq_sub_of_forall_prime {a : ℤ} :
    ∀ n : ℕ, Squarefree n →
      (∀ p : ℕ, p.Prime → p ∣ n → ∃ t : ℤ, (p : ℤ) ∣ t ^ 2 - a) →
      ∃ t : ℤ, (n : ℤ) ∣ t ^ 2 - a := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hprime
    rcases eq_or_ne n 1 with rfl | hn1
    · exact ⟨0, by simp⟩
    have hn0 : n ≠ 0 := hn.ne_zero
    obtain ⟨p, hpp, hpdvd⟩ : ∃ p : ℕ, p.Prime ∧ p ∣ n :=
      ⟨n.minFac, Nat.minFac_prime hn1, n.minFac_dvd⟩
    obtain ⟨m, hm⟩ := hpdvd
    have hsf : Squarefree (p * m) := by rw [← hm]; exact hn
    obtain ⟨hcop, -, hmsf⟩ := Nat.squarefree_mul_iff.mp hsf
    have hm0 : m ≠ 0 := by rintro rfl; rw [mul_zero] at hm; exact hn0 hm
    have hmlt : m < n := by
      calc m < 2 * m := by omega
        _ ≤ p * m := Nat.mul_le_mul_right m hpp.two_le
        _ = n := hm.symm
    obtain ⟨t₁, ht₁⟩ := hprime p hpp ⟨m, hm⟩
    obtain ⟨t₂, ht₂⟩ := ih m hmlt hmsf fun q hq hqm => hprime q hq (hqm.trans ⟨p, by rw [hm]; ring⟩)
    have hcopZ : IsCoprime ((p : ℤ)) ((m : ℤ)) := Nat.isCoprime_iff_coprime.mpr hcop
    obtain ⟨u, v, huv⟩ := id hcopZ
    refine ⟨t₂ * (u * (p : ℤ)) + t₁ * (v * (m : ℤ)), ?_⟩
    rw [hm]
    push_cast
    refine hcopZ.mul_dvd (dvd_sq_sub_of_dvd_sub ?_ ht₁) (dvd_sq_sub_of_dvd_sub ?_ ht₂)
    · exact ⟨u * (t₂ - t₁), by linear_combination t₁ * huv⟩
    · exact ⟨v * (t₁ - t₂), by linear_combination t₂ * huv⟩

/-- An integer that is a square modulo every prime factor of a squarefree natural number `n` is
a square modulo `n`. -/
theorem isSquare_zmod_of_forall_prime {n : ℕ} (hn : Squarefree n) {a : ℤ}
    (h : ∀ p : ℕ, p.Prime → p ∣ n → IsSquare ((a : ZMod p))) :
    IsSquare ((a : ZMod n)) := by
  rw [isSquare_zmod_iff_dvd_sq_sub]
  exact exists_dvd_sq_sub_of_forall_prime n hn fun p hp hpn =>
    (isSquare_zmod_iff_dvd_sq_sub p a).mp (h p hp hpn)

/-- For a nonzero squarefree integer `b`, an integer that is a square modulo every prime divisor
of `b` has a square root modulo `b` lying in the interval of absolutely least residues. -/
theorem exists_sq_sub_dvd {b : ℤ} (hb : b ≠ 0) (hbsf : Squarefree b) {a : ℤ}
    (h : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ b → IsSquare ((a : ZMod p))) :
    ∃ t : ℤ, b ∣ t ^ 2 - a ∧ 2 * |t| ≤ |b| := by
  have hsf : Squarefree b.natAbs := Int.squarefree_natAbs.mpr hbsf
  have h' : ∀ p : ℕ, p.Prime → p ∣ b.natAbs → IsSquare ((a : ZMod p)) := fun p hp hpd =>
    h p hp ((Int.natCast_dvd_natCast.mpr hpd).trans (Int.natAbs_dvd.mpr dvd_rfl))
  obtain ⟨t₀, ht₀⟩ :=
    (isSquare_zmod_iff_dvd_sq_sub b.natAbs a).mp (isSquare_zmod_of_forall_prime hsf h')
  have hbt : b ∣ t₀ ^ 2 - a := Int.natAbs_dvd.mp ht₀
  set B := |b| with hBdef
  have hB : 0 < B := abs_pos.mpr hb
  have hbB : b ∣ B := by rw [hBdef]; exact self_dvd_abs b
  obtain ⟨r, hr0, hr1, hrdvd⟩ : ∃ r : ℤ, 0 ≤ r ∧ r < B ∧ b ∣ r - t₀ :=
    ⟨t₀ % B, Int.emod_nonneg t₀ hB.ne', Int.emod_lt_of_pos t₀ hB,
      hbB.trans ⟨-(t₀ / B), by rw [Int.emod_def]; ring⟩⟩
  rcases le_or_gt (2 * r) B with hc | hc
  · refine ⟨r, dvd_sq_sub_of_dvd_sub hrdvd hbt, ?_⟩
    rw [abs_of_nonneg hr0]
    exact hc
  · refine ⟨r - B, dvd_sq_sub_of_dvd_sub ?_ hbt, ?_⟩
    · have hexp : r - B - t₀ = r - t₀ - B := by ring
      rw [hexp]
      exact dvd_sub hrdvd hbB
    · rw [abs_of_nonpos (by omega : r - B ≤ 0)]
      omega

end InverseGalois.CFT

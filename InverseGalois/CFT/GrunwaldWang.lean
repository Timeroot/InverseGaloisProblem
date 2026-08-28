/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.LocalPower
import InverseGalois.CFT.Kummer.RootIndex
import InverseGalois.CFT.Units.SplitOutside
import InverseGalois.CFT.Units.PlaceTower
import InverseGalois.CFT.Approximation.PowClass

/-!
# The Grunwald–Wang theorem

Fix a number field `K` and an exponent `n`.  Two questions can be asked about the classes of `Kˣ`
modulo `n`-th powers and their images in the completions.  Prescribing finitely many local classes
is possible, because the field is dense in the product of finitely many completions and the `n`-th
powers of a completion are open; that is weak approximation, and it is the surjectivity half.  The
injectivity half asks the converse: an element which is an `n`-th power in almost every completion
is an `n`-th power.  This is Wang's theorem, and it is the content of this file for `n` squarefree.

The proof for a prime exponent `p` is Kummer theory against the fact that a solvable extension of
number fields in which almost every place splits completely is trivial.  If the base field carries a
primitive `p`-th root of unity, an element which is not a `p`-th power generates a cyclic extension
of degree `p` by a radical, and the decomposition group at a place fixes that radical exactly when
the radicand is a local `p`-th power there; the hypothesis makes every place outside a finite set
split completely, so the extension is trivial and the degree cannot be `p`.  The root of unity is
then removed by adjoining it: the cyclotomic extension has degree prime to `p`, so the norm turns a
`p`-th root upstairs into a `p`-th root downstairs.  A squarefree exponent is assembled from its
prime factors, coprime exponents combining because their Bezout relation writes `1` as a
combination.

No case is excluded.  Wang's counterexample lives at the exponent `8`, and an exponent divisible by
`8` is never squarefree.

## Main results

* `InverseGalois.CFT.subsingleton_gal_of_forall_localPow_outside`: a radical extension of a number
  field carrying the roots of unity whose radicand is a local `p`-th power outside a finite set of
  places is trivial.
* `InverseGalois.CFT.exists_pow_eq_of_forall_localPow_outside`: **an element of a number field
  carrying a primitive `p`-th root of unity which is a `p`-th power in the completion at every
  place outside a finite set is a `p`-th power.**
* `InverseGalois.CFT.exists_pow_eq_of_forall_localPow_outside_of_prime`: **the same with no
  hypothesis on the roots of unity of the base field**, for a prime exponent.
* `InverseGalois.CFT.exists_pow_eq_of_forall_localPow_outside_of_squarefree`: **the Grunwald–Wang
  theorem**, that an element of a number field which is an `n`-th power in the completion at every
  place outside a finite set is an `n`-th power, for `n` squarefree.
* `InverseGalois.CFT.exists_pow_eq_iff_forall_localPow_outside_of_squarefree`: **the Hasse principle
  for `n`-th powers**, `n` squarefree, packaging both directions.
* `InverseGalois.CFT.exists_ne_zero_forall_pow_mul_eq_adicCompletion`: **prescribed classes modulo
  `n`-th powers at finitely many finite places are matched by an element of the field.**
* `InverseGalois.CFT.exists_ne_zero_not_exists_pow_eq_forall_pow_mul_eq_adicCompletion`: the same
  with an element that is not a global `n`-th power, one prescribed class being no local one.

## Tags

number field, Grunwald-Wang, Kummer theory, local-global, power, weak approximation
-/

namespace InverseGalois.CFT

open IsDedekindDomain IntermediateField MulAction NumberField Polynomial

/-! ### Coprime exponents in a commutative group -/

section Group

variable {G : Type*} [CommGroup G]

/-- A Bezout relation for two coprime naturals, read in the integers. -/
private theorem exists_intBezout {d n : ℕ} (h : Nat.Coprime d n) :
    ∃ u v : ℤ, u * d + v * n = 1 := by
  refine ⟨Nat.gcdA d n, Nat.gcdB d n, ?_⟩
  have hg := Nat.gcd_eq_gcd_ab d n
  rw [Nat.Coprime] at h
  rw [h] at hg
  push_cast at hg
  linear_combination -hg

/-- **An element of a commutative group whose power by an exponent prime to `n` is an `n`-th power
is itself an `n`-th power**: the Bezout relation between the two exponents writes the element as a
combination of the two powers. -/
theorem exists_pow_eq_of_pow_eq_pow_coprime {n d : ℕ} (h : Nat.Coprime d n) {x t : G}
    (hxt : x ^ d = t ^ n) : ∃ z : G, z ^ n = x := by
  obtain ⟨u, v, huv⟩ := exists_intBezout h
  refine ⟨t ^ u * x ^ v, ?_⟩
  have h1 : (t ^ u * x ^ v) ^ (n : ℤ) = (t ^ (n : ℤ)) ^ u * x ^ (v * (n : ℤ)) := by
    rw [mul_zpow, ← zpow_mul, ← zpow_mul, mul_comm u (n : ℤ), zpow_mul]
  rw [zpow_natCast t n, ← hxt, ← zpow_natCast x d, ← zpow_mul, ← zpow_add,
    show (d : ℤ) * u + v * (n : ℤ) = 1 by linear_combination huv, zpow_one] at h1
  rw [← zpow_natCast (t ^ u * x ^ v) n]
  exact h1

/-- **An element of a commutative group which is both an `m`-th power and an `n`-th power, for
coprime exponents, is an `m * n`-th power.** -/
theorem exists_pow_eq_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) {x : G}
    (hm : ∃ y : G, y ^ m = x) (hn : ∃ z : G, z ^ n = x) : ∃ w : G, w ^ (m * n) = x := by
  obtain ⟨y, hy⟩ := hm
  obtain ⟨z, hz⟩ := hn
  obtain ⟨u, v, huv⟩ := exists_intBezout h
  refine ⟨z ^ u * y ^ v, ?_⟩
  have h1 : (z ^ u * y ^ v) ^ ((m : ℤ) * (n : ℤ))
      = (z ^ (n : ℤ)) ^ (u * (m : ℤ)) * (y ^ (m : ℤ)) ^ (v * (n : ℤ)) := by
    rw [mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul]
    ring_nf
  rw [zpow_natCast z n, zpow_natCast y m, hy, hz, ← zpow_add,
    show u * (m : ℤ) + v * (n : ℤ) = 1 by linear_combination huv, zpow_one] at h1
  rw [← zpow_natCast (z ^ u * y ^ v) (m * n)]
  push_cast
  exact h1

/-- An element of a commutative group which is a `q`-th power for every member of a finite set of
distinct primes is a power by their product. -/
private theorem exists_pow_prod_eq {x : G} : ∀ s : Finset ℕ, (∀ q ∈ s, q.Prime) →
    (∀ q ∈ s, ∃ y : G, y ^ q = x) → ∃ w : G, w ^ (∏ q ∈ s, q) = x := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => exact fun _ _ => ⟨x, by simp⟩
  | insert q s hq ih =>
    intro hs hx
    obtain ⟨w, hw⟩ := ih (fun r hr => hs r (Finset.mem_insert_of_mem hr))
      fun r hr => hx r (Finset.mem_insert_of_mem hr)
    have hqp : q.Prime := hs q (Finset.mem_insert_self q s)
    have hcop : Nat.Coprime q (∏ r ∈ s, r) :=
      Nat.Coprime.prod_right fun r hr =>
        (Nat.coprime_primes hqp (hs r (Finset.mem_insert_of_mem hr))).mpr fun h => hq (by
          rw [h]; exact hr)
    obtain ⟨z, hz⟩ :=
      exists_pow_eq_mul_of_coprime hcop (hx q (Finset.mem_insert_self q s)) ⟨w, hw⟩
    rw [Finset.prod_insert hq]
    exact ⟨z, hz⟩

end Group

/-! ### Wang's theorem over a base carrying the roots of unity -/

section RootsOfUnity

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] {p : ℕ}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

/-- **A radical extension of a number field carrying the roots of unity whose radicand is a local
`p`-th power outside a finite set of places is trivial.**  The decomposition group at such a place
fixes the radical, and the radical generates the extension, so every place outside the set splits
completely; a solvable extension with that property is trivial. -/
theorem subsingleton_gal_of_forall_localPow_outside [IsSolvable Gal(L/K)] (hp : p ≠ 0) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite) {b : K} {β : L}
    (hβ : β ^ p = algebraMap K L b) (hgenβ : IntermediateField.adjoin K ({β} : Set L) = ⊤)
    (hb : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∃ c : v.adicCompletion K, c ^ p = algebraMap K (v.adicCompletion K) b) :
    Subsingleton Gal(L/K) := by
  have hone : ∀ g : Gal(L/K), g β = β → g = 1 := by
    intro g hg
    have hmem : g ∈ (K⟮β⟯ : IntermediateField K L).fixingSubgroup := by
      rw [fixingSubgroup_adjoin_simple_eq_stabilizer]
      exact hg
    rw [hgenβ] at hmem
    exact AlgEquiv.ext fun x => hmem ⟨x, IntermediateField.mem_top⟩
  refine subsingleton_gal_of_isSolvable_of_splits_outside hS fun w hw => ?_
  refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg => hone g ?_
  exact (forall_stabilizer_smul_eq_iff_exists_pow w hζ hp hβ.symm).mpr (hb _ hw) ⟨g, hg⟩

end RootsOfUnity

section Wang

variable {K : Type*} [Field K] [NumberField K] {p : ℕ}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

/-- **An element of a number field carrying a primitive `p`-th root of unity which is a `p`-th
power in the completion at every place outside a finite set is a `p`-th power.**  Were it not, the
polynomial `X ^ p - b` would be irreducible and its splitting field a cyclic extension of degree
`p` cut out by a radical, which the local hypotheses force to be trivial. -/
theorem exists_pow_eq_of_forall_localPow_outside (hp : p.Prime) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite) {b : K}
    (hb : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∃ c : v.adicCompletion K, c ^ p = algebraMap K (v.adicCompletion K) b) :
    ∃ y : K, y ^ p = b := by
  by_contra hcon
  push_neg at hcon
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hirr : Irreducible (X ^ p - C b) := X_pow_sub_C_irreducible_of_prime hp hcon
  have hprim : (primitiveRoots p K).Nonempty := ⟨ζ, (mem_primitiveRoots hp.pos).mpr hζ⟩
  haveI : NumberField (X ^ p - C b).SplittingField := NumberField.of_module_finite K _
  haveI : IsGalois K (X ^ p - C b).SplittingField :=
    isGalois_of_isSplittingField_X_pow_sub_C hprim hirr _
  haveI : IsCyclic Gal((X ^ p - C b).SplittingField/K) :=
    isCyclic_of_isSplittingField_X_pow_sub_C hprim hirr _
  haveI : IsSolvable Gal((X ^ p - C b).SplittingField/K) :=
    isSolvable_of_comm
      (letI := IsCyclic.commGroup (α := Gal((X ^ p - C b).SplittingField/K)); mul_comm)
  have hdeg : Module.finrank K (X ^ p - C b).SplittingField = p :=
    finrank_of_isSplittingField_X_pow_sub_C hprim hirr _
  have hβ : (rootOfSplitsXPowSubC (NeZero.pos p) b (X ^ p - C b).SplittingField) ^ p
      = algebraMap K (X ^ p - C b).SplittingField b :=
    rootOfSplitsXPowSubC_pow b _
  have hgenβ : IntermediateField.adjoin K
      ({rootOfSplitsXPowSubC (NeZero.pos p) b (X ^ p - C b).SplittingField} :
        Set (X ^ p - C b).SplittingField) = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    have hx : x ∈ Algebra.adjoin K
        ({rootOfSplitsXPowSubC (NeZero.pos p) b (X ^ p - C b).SplittingField} :
          Set (X ^ p - C b).SplittingField) :=
      (Algebra.adjoin_root_eq_top_of_isSplittingField hprim hirr hβ) ▸ Algebra.mem_top
    exact IntermediateField.algebra_adjoin_le_adjoin K _ hx
  haveI := subsingleton_gal_of_forall_localPow_outside (L := (X ^ p - C b).SplittingField)
    hp.ne_zero hζ hS hβ hgenβ hb
  have hone : Nat.card Gal((X ^ p - C b).SplittingField/K) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  rw [IsGalois.card_aut_eq_finrank, hdeg] at hone
  exact hp.one_lt.ne' hone

/-- **An element of a number field which is a `p`-th power in the completion at every place outside
a finite set is a `p`-th power**, for a prime exponent and with no hypothesis on the roots of unity
of the base field.  Adjoining a primitive `p`-th root of unity is an extension of degree dividing
`p - 1`, hence prime to `p`; the element is a `p`-th power there, and the norm of a `p`-th root
upstairs is a `p`-th root of the power of the element by that degree, which a Bezout relation turns
into a `p`-th root downstairs. -/
theorem exists_pow_eq_of_forall_localPow_outside_of_prime (hp : p.Prime)
    {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite) {b : K}
    (hb : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∃ c : v.adicCompletion K, c ^ p = algebraMap K (v.adicCompletion K) b) :
    ∃ y : K, y ^ p = b := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  rcases eq_or_ne b 0 with rfl | hb0
  · exact ⟨0, zero_pow hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) p
  set Zk : IntermediateField K (AlgebraicClosure K) := K⟮ζ⟯ with hZk
  haveI : IsCyclotomicExtension {p} K ↥Zk := hζ.intermediateField_adjoin_isCyclotomicExtension K
  haveI : FiniteDimensional K ↥Zk :=
    IsCyclotomicExtension.finiteDimensional (S := {p}) (K := K) (C := ↥Zk)
  haveI : NumberField ↥Zk := NumberField.of_module_finite K ↥Zk
  haveI : IsGalois K ↥Zk := IsCyclotomicExtension.isGalois (S := {p}) (K := K) (L := ↥Zk)
  have hζmem : ζ ∈ Zk := by rw [hZk]; exact IntermediateField.mem_adjoin_simple_self K ζ
  have hζ' : IsPrimitiveRoot (⟨ζ, hζmem⟩ : ↥Zk) p := by
    rwa [← IsPrimitiveRoot.coe_submonoidClass_iff]
  -- the degree of the cyclotomic field is prime to `p`
  have hdvd0 : Nat.card Gal(↥Zk/K) ∣ Nat.card (ZMod p)ˣ := by
    rw [Nat.card_congr (MonoidHom.ofInjective (hζ'.autToPow_injective K)).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have hunits : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp]
  have hcardZ : Nat.card Gal(↥Zk/K) ∣ p - 1 := by rwa [hunits] at hdvd0
  have hcardeq : Nat.card Gal(↥Zk/K) = Module.finrank K ↥Zk :=
    IsGalois.card_aut_eq_finrank K ↥Zk
  have hcop : Nat.Coprime (Module.finrank K ↥Zk) p := by
    rw [← hcardeq]
    refine Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun hdvd => ?_)
    have h1 : p ≤ Nat.card Gal(↥Zk/K) := Nat.le_of_dvd Nat.card_pos hdvd
    have h2 : Nat.card Gal(↥Zk/K) ≤ p - 1 := Nat.le_of_dvd (by have := hp.two_le; omega) hcardZ
    have := hp.two_le
    omega
  -- the local hypothesis rises to the cyclotomic field
  have hS' : (primeUnder (𝓞 K) (B := 𝓞 ↥Zk) ⁻¹' S).Finite :=
    finite_preimage_primeUnder (𝓞 K) (𝓞 ↥Zk) (G := Gal(↥Zk/K)) hS
  have hb' : ∀ w : HeightOneSpectrum (𝓞 ↥Zk), w ∉ primeUnder (𝓞 K) (B := 𝓞 ↥Zk) ⁻¹' S →
      ∃ c : w.adicCompletion ↥Zk,
        c ^ p = algebraMap ↥Zk (w.adicCompletion ↥Zk) (algebraMap K ↥Zk b) := by
    intro w hw
    obtain ⟨c, hc⟩ := hb (primeUnder (𝓞 K) w) hw
    refine ⟨adicCompletionComap (𝓞 K) w c, ?_⟩
    rw [← map_pow, hc]
    exact adicCompletionComap_coe (𝓞 K) w b
  obtain ⟨y, hy⟩ := exists_pow_eq_of_forall_localPow_outside hp hζ' hS' hb'
  -- the norm brings the root down
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, zero_pow hp.ne_zero] at hy
    exact hb0 (FaithfulSMul.algebraMap_injective K ↥Zk (by rw [← hy, map_zero]))
  have hn0 : Algebra.norm K y ≠ 0 := (Algebra.norm_ne_zero_iff).mpr hy0
  have hnorm : b ^ Module.finrank K ↥Zk = (Algebra.norm K y) ^ p := by
    rw [← Algebra.norm_algebraMap (L := ↥Zk) b, ← hy, map_pow]
  obtain ⟨z, hz⟩ := exists_pow_eq_of_pow_eq_pow_coprime (G := Kˣ) hcop
    (x := Units.mk0 b hb0) (t := Units.mk0 (Algebra.norm K y) hn0) (Units.ext hnorm)
  exact ⟨(z : K), by rw [← Units.val_pow_eq_pow_val, hz, Units.val_mk0]⟩

/-- **The Grunwald–Wang theorem**: an element of a number field which is an `n`-th power in the
completion at every place outside a finite set is an `n`-th power, the exponent being squarefree.
Each prime factor of the exponent divides it, so the element is a local power by that prime and
therefore a global one, and powers by coprime exponents combine. -/
theorem exists_pow_eq_of_forall_localPow_outside_of_squarefree {n : ℕ} (hn : Squarefree n)
    {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite) {b : K}
    (hb : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∃ c : v.adicCompletion K, c ^ n = algebraMap K (v.adicCompletion K) b) :
    ∃ y : K, y ^ n = b := by
  classical
  have hn0 : n ≠ 0 := hn.ne_zero
  rcases eq_or_ne b 0 with rfl | hb0
  · exact ⟨0, zero_pow hn0⟩
  -- a `q`-th root for every prime factor `q`
  have hq : ∀ q ∈ n.primeFactors, ∃ y : Kˣ, y ^ q = Units.mk0 b hb0 := by
    intro q hqmem
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hqmem
    obtain ⟨m, hm⟩ : q ∣ n := Nat.dvd_of_mem_primeFactors hqmem
    have hbq : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ∃ c : v.adicCompletion K, c ^ q = algebraMap K (v.adicCompletion K) b := by
      intro v hv
      obtain ⟨c, hc⟩ := hb v hv
      refine ⟨c ^ m, ?_⟩
      rw [← pow_mul, mul_comm m q, ← hm, hc]
    obtain ⟨y, hy⟩ := exists_pow_eq_of_forall_localPow_outside_of_prime hqp hS hbq
    have hy0 : y ≠ 0 := by
      intro h
      rw [h, zero_pow hqp.ne_zero] at hy
      exact hb0 hy.symm
    exact ⟨Units.mk0 y hy0,
      Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_mk0, hy])⟩
  obtain ⟨w, hw⟩ := exists_pow_prod_eq (G := Kˣ) (x := Units.mk0 b hb0) n.primeFactors
    (fun q hq => Nat.prime_of_mem_primeFactors hq) hq
  rw [Nat.prod_primeFactors_of_squarefree hn] at hw
  exact ⟨(w : K), by rw [← Units.val_pow_eq_pow_val, hw, Units.val_mk0]⟩

/-- **The Hasse principle for `n`-th powers in a number field**, the exponent being squarefree: an
element is an `n`-th power exactly when it is one in the completion at every place outside a finite
set.  One direction is the image of a global root, the other is Wang's theorem. -/
theorem exists_pow_eq_iff_forall_localPow_outside_of_squarefree {n : ℕ} (hn : Squarefree n)
    {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite) {b : K} :
    (∃ y : K, y ^ n = b) ↔ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∃ c : v.adicCompletion K, c ^ n = algebraMap K (v.adicCompletion K) b := by
  refine ⟨fun ⟨y, hy⟩ v _ => ⟨algebraMap K (v.adicCompletion K) y, by rw [← map_pow, hy]⟩, ?_⟩
  exact exists_pow_eq_of_forall_localPow_outside_of_squarefree hn hS

end Wang

/-! ### Prescribing the local classes -/

section Prescribe

variable {K : Type*} [Field K] [NumberField K]

/-- **Prescribed classes modulo `n`-th powers at finitely many finite places are matched by an
element of the field.**  This is weak approximation: the `n`-th powers of a completion form a
neighbourhood of any nonzero element of it, so an element of the field close enough to the
prescribed data at each of the finitely many places differs from it by an `n`-th power there. -/
theorem exists_ne_zero_forall_pow_mul_eq_adicCompletion {n : ℕ} (hn : n ≠ 0)
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (c : ∀ v : {v // v ∈ T}, ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K))
    (hc : ∀ v, c v ≠ 0) :
    ∃ b : K, b ≠ 0 ∧ ∀ v : {v // v ∈ T},
      ∃ z : ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K),
        z ^ n * c v = algebraMap K ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K) b := by
  obtain ⟨b, hb0, -, hbT⟩ := exists_ne_zero_pow_mul_eq_completion (K := K)
    (ι := fun v : {v // v ∈ T} => (v : HeightOneSpectrum (𝓞 K))) hn Subtype.val_injective
    (fun _ => 1) (fun _ => one_ne_zero) c hc
  exact ⟨b, hb0, hbT⟩

/-- Prescribed classes modulo `n`-th powers at finitely many finite places are matched by an element
of the field which is itself not an `n`-th power, as soon as one of the prescribed classes is not a
local `n`-th power: a global root would be a local one at that place. -/
theorem exists_ne_zero_not_exists_pow_eq_forall_pow_mul_eq_adicCompletion {n : ℕ} (hn : n ≠ 0)
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (c : ∀ v : {v // v ∈ T}, ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K))
    (hc : ∀ v, c v ≠ 0) (v₀ : {v // v ∈ T})
    (hv₀ : ¬ ∃ z : ((v₀ : HeightOneSpectrum (𝓞 K)).adicCompletion K), z ^ n = c v₀) :
    ∃ b : K, b ≠ 0 ∧ (¬ ∃ y : K, y ^ n = b) ∧ ∀ v : {v // v ∈ T},
      ∃ z : ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K),
        z ^ n * c v = algebraMap K ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K) b := by
  obtain ⟨b, hb0, hbT⟩ := exists_ne_zero_forall_pow_mul_eq_adicCompletion hn T c hc
  refine ⟨b, hb0, ?_, hbT⟩
  rintro ⟨y, hy⟩
  obtain ⟨z, hz⟩ := hbT v₀
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hn, zero_mul] at hz
    exact hb0 ((algebraMap K _).injective (by rw [← hz, map_zero]))
  refine hv₀ ⟨algebraMap K ((v₀ : HeightOneSpectrum (𝓞 K)).adicCompletion K) y / z, ?_⟩
  rw [div_pow, ← map_pow, hy, ← hz]
  exact mul_div_cancel_left₀ _ (pow_ne_zero n hz0)

end Prescribe

end InverseGalois.CFT

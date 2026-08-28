/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PiDual
import InverseGalois.CFT.Scholz.AuxPrimeChoice
import InverseGalois.CFT.Scholz.PowerResidue
import InverseGalois.CFT.Scholz.PrimeIndependence
import InverseGalois.CFT.Scholz.ResidueSymbol

/-!
# The power residue vectors of the auxiliary primes

Fix a finite set `S` of rational primes.  An auxiliary prime `q` splitting completely in a given
Galois extension of the rationals records, through its power residue symbol, a vector of `ZMod ℓ`
indexed by `S`.  Which vectors are combinations of those is decided by duality: a coefficient
vector annihilating all of them is a vector of exponents for which the corresponding product of
powers of the primes of `S` is an `ℓ`-th power residue modulo every auxiliary prime, and that
happens as soon as the product is already an `ℓ`-th power in the extension.  So a vector belongs to
the span provided it is orthogonal to every exponent vector whose product of prime powers becomes
an `ℓ`-th power there.

For an odd prime and a nilpotent extension containing the `ℓ`-th roots of unity no nonzero exponent
vector has that property, the primes of `S` being multiplicatively independent modulo `ℓ`-th
powers, and the residue vectors span the whole space.

The space of vectors being finite, finitely many auxiliary primes already span their span, and the
product of those primes is a modulus which works for every admissible vector at once: such a vector
is realised by a character of the units modulo that one modulus, obtained by pulling the characters
of the individual primes back along the reduction maps and multiplying them with the appropriate
exponents.

## Main definitions

* `InverseGalois.CFT.residueVector`: the vector of power residue symbols of the primes of `S`.
* `InverseGalois.CFT.residueRadicand`: the product of the primes of `S` raised to the exponents
  recorded by a vector of residues.

## Main results

* `InverseGalois.CFT.residueVector_mem_of_forall_pow_eq`: **a vector orthogonal to every exponent
  vector whose radicand is an `ℓ`-th power in the extension is a combination of the power residue
  vectors of the auxiliary primes.**
* `InverseGalois.CFT.residueVectors_span_eq_top`: **for an odd prime the power residue vectors of
  the auxiliary primes span the whole space.**
* `InverseGalois.CFT.exists_modulus_powerResidueSymbol_of_forall_pow_eq` and
  `InverseGalois.CFT.exists_modulus_powerResidueSymbol`: **a single product of auxiliary primes
  serves as a modulus for which every admissible vector of power residue symbols is realised by a
  character of the units.**

## Tags

power residue symbol, linear algebra over a finite field, auxiliary prime, Scholz–Reichardt
-/

open Finset NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

variable {ℓ : ℕ} {S : Finset ℕ} {A : IntermediateField ℚ (AlgebraicClosure ℚ)}

/-- The vector of power residue symbols of the elements of `S` attached to a character of the units
modulo an auxiliary prime. -/
noncomputable def residueVector (S : Finset ℕ) {q : ℕ}
    (κ : (ZMod q)ˣ →* Multiplicative (ZMod ℓ)) : {p // p ∈ S} → ZMod ℓ :=
  fun p => powerResidueSymbol κ p.1

/-- The product of the primes of `S` raised to the exponents recorded by a vector of residues. -/
def residueRadicand (S : Finset ℕ) (a : {p // p ∈ S} → ZMod ℓ) : ℕ :=
  ∏ i : {p // p ∈ S}, (i : ℕ) ^ (a i).val

/-- The radicand of a vector of residues read as a product over `S` of prime powers. -/
theorem residueRadicand_eq_prod {e : ℕ → ℕ} (a : {p // p ∈ S} → ZMod ℓ)
    (he : ∀ (p : ℕ) (h : p ∈ S), e p = (a ⟨p, h⟩).val) :
    residueRadicand S a = ∏ p ∈ S, p ^ e p := by
  rw [residueRadicand, Finset.univ_eq_attach, ← Finset.prod_attach S fun p => p ^ e p]
  exact Finset.prod_congr rfl fun i _ => by rw [he i.1 i.2]

/-- An exponent vector always admits an extension by zero to all of the natural numbers. -/
theorem exists_exponents (a : {p // p ∈ S} → ZMod ℓ) :
    ∃ e : ℕ → ℕ, ∀ (p : ℕ) (h : p ∈ S), e p = (a ⟨p, h⟩).val :=
  ⟨fun p => if h : p ∈ S then (a ⟨p, h⟩).val else 0, fun _ h => dif_pos h⟩

/-- A prime of `S` is a unit modulo an auxiliary prime, the two being distinct primes. -/
theorem isUnit_natCast_of_mem {q p : ℕ} (hq : q.Prime) (hqS : q ∉ S)
    (hSprime : ∀ p ∈ S, p.Prime) (hp : p ∈ S) : IsUnit ((p : ZMod q)) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  refine (ZMod.isUnit_iff_coprime p q).mpr ((Nat.coprime_primes (hSprime p hp) hq).mpr ?_)
  rintro rfl
  exact hqS hp

/-- **A vector orthogonal to every exponent vector whose radicand is an `ℓ`-th power in the
extension is a combination of the power residue vectors of the auxiliary primes.**  A coefficient
vector annihilating the subspace is a vector of exponents; were the corresponding product of powers
of the primes of `S` not an `ℓ`-th power in the extension, some auxiliary prime would fail to have
it as a power residue, contradicting the vanishing of the pairing.  So the radicand is a power and
the hypothesis applies. -/
theorem residueVector_mem_of_forall_pow_eq [Fact ℓ.Prime] [NumberField ↥A] [IsGalois ℚ ↥A]
    (hSprime : ∀ p ∈ S, p.Prime)
    (hdvd : ∀ q : ℕ, q.Prime → q ≠ ℓ → SplitsCompletely ↥A q → ℓ ∣ q - 1)
    (V : Submodule (ZMod ℓ) ({p // p ∈ S} → ZMod ℓ))
    (hV : ∀ (q : ℕ) (κ : (ZMod q)ˣ →* Multiplicative (ZMod ℓ)), q.Prime → q ∉ S → q ≠ ℓ →
      SplitsCompletely ↥A q → (∀ x : (ZMod q)ˣ, κ x = 1 ↔ (x : ZMod q) ^ ((q - 1) / ℓ) = 1) →
      residueVector S κ ∈ V)
    (t : {p // p ∈ S} → ZMod ℓ)
    (ht : ∀ a : {p // p ∈ S} → ZMod ℓ, (∃ u ∈ A,
        u ^ ℓ = algebraMap ℚ (AlgebraicClosure ℚ) ((residueRadicand S a : ℕ) : ℚ)) →
      ∑ i, t i * a i = 0) :
    t ∈ V := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  refine mem_of_forall_dualCoeff V t fun a ha => ?_
  by_cases hpow : ∃ u ∈ A,
      u ^ ℓ = algebraMap ℚ (AlgebraicClosure ℚ) ((residueRadicand S a : ℕ) : ℚ)
  · exact ht a hpow
  push_neg at hpow
  exfalso
  -- the radicand is not an `ℓ`-th power in the extension, so an auxiliary prime detects it
  obtain ⟨e, he⟩ := exists_exponents a
  have hve : residueRadicand S a = ∏ p ∈ S, p ^ e p := residueRadicand_eq_prod a he
  have hnp : ∀ u ∈ A,
      u ^ ℓ ≠ algebraMap ℚ (AlgebraicClosure ℚ) (((residueRadicand S a : ℤ) : ℚ)) := by
    intro u hu
    rw [Int.cast_natCast]
    exact hpow u hu
  obtain ⟨q, hqp, hqS, hqne, hqA, hqres⟩ :=
    exists_prime_splitsCompletely_pow_ne_one_of_forall_pow_ne hnp S hdvd
  obtain ⟨κ, -, hκ⟩ := exists_powerResidueHom hℓ hqp (hdvd q hqp hqne hqA)
  have hunit : ∀ p ∈ S, IsUnit ((p : ZMod q)) := fun p hp =>
    isUnit_natCast_of_mem hqp hqS hSprime hp
  have hvunit : IsUnit (((residueRadicand S a : ℕ) : ZMod q)) := by
    rw [hve]
    push_cast
    exact Finset.prod_induction (fun p : ℕ => ((p : ZMod q)) ^ e p) IsUnit
      (fun _ _ => IsUnit.mul) isUnit_one fun p hp => (hunit p hp).pow _
  -- the symbol of the radicand is both nonzero and zero
  have hsymb : powerResidueSymbol κ (residueRadicand S a) ≠ 0 := by
    intro h0
    rw [powerResidueSymbol_eq_zero_iff κ hκ hvunit] at h0
    exact hqres (by push_cast; exact h0)
  refine hsymb ?_
  rw [hve, powerResidueSymbol_prod_pow κ hunit,
    ← Finset.sum_attach S fun p => e p • powerResidueSymbol κ p]
  have hterm : ∀ i ∈ S.attach, e i.1 • powerResidueSymbol κ i.1 =
      residueVector S κ i * a i := by
    intro i _
    rw [nsmul_eq_mul, he i.1 i.2]
    simp only [residueVector, ZMod.natCast_val, ZMod.cast_id]
    exact mul_comm _ _
  rw [Finset.sum_congr rfl hterm, ← Finset.univ_eq_attach]
  exact ha _ (hV q κ hqp hqS hqne hqA hκ)

/-- **For an odd prime exponent only the zero vector has a radicand which is an `ℓ`-th power.**  The
primes of `S` are multiplicatively independent modulo `ℓ`-th powers, so a nonzero vector of
exponents produces a radicand which is not an `ℓ`-th power in the rationals, and a rational number
which is not an `ℓ`-th power stays one in a nilpotent extension containing the `ℓ`-th roots of
unity. -/
theorem eq_zero_of_pow_eq_residueRadicand [Fact ℓ.Prime] (hodd : Odd ℓ) [NumberField ↥A]
    [IsGalois ℚ ↥A] (hnil : Group.IsNilpotent Gal(↥A/ℚ)) {ζ : AlgebraicClosure ℚ}
    (hζ : IsPrimitiveRoot ζ ℓ) (hζA : ζ ∈ A) (hSprime : ∀ p ∈ S, p.Prime)
    {a : {p // p ∈ S} → ZMod ℓ} {u : AlgebraicClosure ℚ} (huA : u ∈ A)
    (hu : u ^ ℓ = algebraMap ℚ (AlgebraicClosure ℚ) ((residueRadicand S a : ℕ) : ℚ)) :
    a = 0 := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  by_contra hane
  obtain ⟨i₀, hi₀⟩ : ∃ i, a i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hane (funext hc)
  obtain ⟨e, he⟩ := exists_exponents a
  have hediv : ¬ ℓ ∣ e i₀.1 := by
    rw [he i₀.1 i₀.2]
    refine Nat.not_dvd_of_pos_of_lt ?_ (ZMod.val_lt (a i₀))
    exact Nat.pos_of_ne_zero fun h => hi₀ ((ZMod.val_eq_zero (a i₀)).mp h)
  have hnp : ∀ y : ℚ, y ^ ℓ ≠ ((residueRadicand S a : ℕ) : ℚ) := by
    intro y
    rw [residueRadicand_eq_prod a he]
    exact pow_ne_prod_pow hSprime i₀.2 hediv y
  exact pow_ne_of_isNilpotent hodd hnil hζ hζA hnp huA hu

/-- **The power residue vectors of the auxiliary primes span the whole space.**  For an odd prime
exponent the only exponent vector whose radicand becomes an `ℓ`-th power in the extension is the
zero vector, so every vector is orthogonal to all of them. -/
theorem residueVectors_span_eq_top [Fact ℓ.Prime] (hodd : Odd ℓ) [NumberField ↥A] [IsGalois ℚ ↥A]
    (hnil : Group.IsNilpotent Gal(↥A/ℚ)) {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ ℓ)
    (hζA : ζ ∈ A) (hSprime : ∀ p ∈ S, p.Prime)
    (hdvd : ∀ q : ℕ, q.Prime → q ≠ ℓ → SplitsCompletely ↥A q → ℓ ∣ q - 1)
    (V : Submodule (ZMod ℓ) ({p // p ∈ S} → ZMod ℓ))
    (hV : ∀ (q : ℕ) (κ : (ZMod q)ˣ →* Multiplicative (ZMod ℓ)), q.Prime → q ∉ S → q ≠ ℓ →
      SplitsCompletely ↥A q → (∀ x : (ZMod q)ˣ, κ x = 1 ↔ (x : ZMod q) ^ ((q - 1) / ℓ) = 1) →
      residueVector S κ ∈ V) :
    V = ⊤ := by
  refine eq_top_iff.mpr fun t _ =>
    residueVector_mem_of_forall_pow_eq hSprime hdvd V hV t fun a ha => ?_
  obtain ⟨u, huA, hu⟩ := ha
  rw [eq_zero_of_pow_eq_residueRadicand hodd hnil hζ hζA hSprime huA hu]
  simp

/-- **A single modulus realises every admissible vector of power residue symbols.**  The vectors of
the auxiliary primes span a subspace of a finite space, so finitely many auxiliary primes already
span it and the product of those primes is the modulus, chosen once and for all.  An admissible
vector is a combination of the vectors of those primes, and the character realising it is the
product of the corresponding powers of the characters of the individual primes, pulled back along
the reduction maps; the symbol being unchanged by such a pullback and additive in the character,
the combination is reproduced exactly. -/
theorem exists_modulus_powerResidueSymbol_of_forall_pow_eq [Fact ℓ.Prime] [NumberField ↥A]
    [IsGalois ℚ ↥A] (hSprime : ∀ p ∈ S, p.Prime)
    (hdvd : ∀ q : ℕ, q.Prime → q ≠ ℓ → SplitsCompletely ↥A q → ℓ ∣ q - 1) :
    ∃ Q : ℕ, Q ≠ 0 ∧
      (∀ r : ℕ, r.Prime → r ∣ Q → r ∉ S ∧ r ≠ ℓ ∧ SplitsCompletely ↥A r) ∧
      ∀ t : {p // p ∈ S} → ZMod ℓ, (∀ a : {p // p ∈ S} → ZMod ℓ, (∃ u ∈ A,
          u ^ ℓ = algebraMap ℚ (AlgebraicClosure ℚ) ((residueRadicand S a : ℕ) : ℚ)) →
        ∑ i, t i * a i = 0) →
        ∃ κ : (ZMod Q)ˣ →* Multiplicative (ZMod ℓ),
          ∀ (p : ℕ) (hp : p ∈ S), powerResidueSymbol κ p = t ⟨p, hp⟩ := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  -- the vectors of the auxiliary primes, of which there are only finitely many
  set s : Set ({p // p ∈ S} → ZMod ℓ) :=
    {w : {p // p ∈ S} → ZMod ℓ | ∃ (q : ℕ) (κ : (ZMod q)ˣ →* Multiplicative (ZMod ℓ)),
      q.Prime ∧ q ∉ S ∧ q ≠ ℓ ∧ SplitsCompletely ↥A q ∧
      (∀ x : (ZMod q)ˣ, κ x = 1 ↔ (x : ZMod q) ^ ((q - 1) / ℓ) = 1) ∧
      w = residueVector S κ}
  letI : Fintype ↥s := Fintype.ofFinite _
  have hmem : ∀ w : ↥s, ∃ (q : ℕ) (κ : (ZMod q)ˣ →* Multiplicative (ZMod ℓ)),
      q.Prime ∧ q ∉ S ∧ q ≠ ℓ ∧ SplitsCompletely ↥A q ∧
      (∀ x : (ZMod q)ˣ, κ x = 1 ↔ (x : ZMod q) ^ ((q - 1) / ℓ) = 1) ∧
      (w : {p // p ∈ S} → ZMod ℓ) = residueVector S κ := fun w => w.2
  choose qq κκ hqqp hqqS hqqne hqqA hqqκ hqqvec using hmem
  -- the modulus
  set Q : ℕ := ∏ w : ↥s, qq w with hQdef
  have hQ0 : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => (hqqp w).ne_zero
  haveI : NeZero Q := ⟨hQ0⟩
  have hdvdQ : ∀ w : ↥s, qq w ∣ Q := fun w => Finset.dvd_prod_of_mem _ (Finset.mem_univ w)
  refine ⟨Q, hQ0, ?_, ?_⟩
  · intro r hr hrQ
    obtain ⟨w, -, hrw⟩ := (Nat.Prime.prime hr).exists_mem_finset_dvd hrQ
    obtain rfl : r = qq w := (Nat.prime_dvd_prime_iff_eq hr (hqqp w)).mp hrw
    exact ⟨hqqS w, hqqne w, hqqA w⟩
  · -- the character attached to an admissible vector
    intro t htorth
    have ht : t ∈ Submodule.span (ZMod ℓ) s :=
      residueVector_mem_of_forall_pow_eq hSprime hdvd (Submodule.span (ZMod ℓ) s)
        (fun q κ hq hqS hqne hqA hκ =>
          Submodule.subset_span ⟨q, κ, hq, hqS, hqne, hqA, hκ, rfl⟩) t htorth
    obtain ⟨c, hc⟩ := Submodule.mem_span_iff_of_fintype.mp ht
    refine ⟨∏ w : ↥s, ((κκ w).comp (ZMod.unitsMap (hdvdQ w))) ^ (c w).val, ?_⟩
    intro p hp
    -- a prime of `S` is a unit modulo the product of the auxiliary primes
    have hpQ : IsUnit ((p : ZMod Q)) := by
      refine (ZMod.isUnit_iff_coprime p Q).mpr (Nat.Coprime.prod_right fun w _ => ?_)
      exact (Nat.coprime_primes (hSprime p hp) (hqqp w)).mpr fun h => hqqS w (h ▸ hp)
    rw [powerResidueSymbol_prod_hom _ _ hpQ]
    have hterm : ∀ w : ↥s, powerResidueSymbol
        (((κκ w).comp (ZMod.unitsMap (hdvdQ w))) ^ (c w).val) p =
          c w * (w : {p // p ∈ S} → ZMod ℓ) ⟨p, hp⟩ := by
      intro w
      rw [powerResidueSymbol_pow_hom _ _ hpQ,
        powerResidueSymbol_comp_unitsMap (κκ w) (hdvdQ w) hpQ, hqqvec w, residueVector,
        nsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id]
    rw [Finset.sum_congr rfl fun w _ => hterm w, ← hc, Finset.sum_apply]
    exact Finset.sum_congr rfl fun w _ => rfl

/-- **A single modulus realises every prescribed vector of power residue symbols.**  For an odd
prime exponent every vector is admissible. -/
theorem exists_modulus_powerResidueSymbol [Fact ℓ.Prime] (hodd : Odd ℓ) [NumberField ↥A]
    [IsGalois ℚ ↥A] (hnil : Group.IsNilpotent Gal(↥A/ℚ)) {ζ : AlgebraicClosure ℚ}
    (hζ : IsPrimitiveRoot ζ ℓ) (hζA : ζ ∈ A) (hSprime : ∀ p ∈ S, p.Prime)
    (hdvd : ∀ q : ℕ, q.Prime → q ≠ ℓ → SplitsCompletely ↥A q → ℓ ∣ q - 1) :
    ∃ Q : ℕ, Q ≠ 0 ∧
      (∀ r : ℕ, r.Prime → r ∣ Q → r ∉ S ∧ r ≠ ℓ ∧ SplitsCompletely ↥A r) ∧
      ∀ t : {p // p ∈ S} → ZMod ℓ, ∃ κ : (ZMod Q)ˣ →* Multiplicative (ZMod ℓ),
        ∀ (p : ℕ) (hp : p ∈ S), powerResidueSymbol κ p = t ⟨p, hp⟩ := by
  obtain ⟨Q, hQ0, hQr, hQt⟩ := exists_modulus_powerResidueSymbol_of_forall_pow_eq
    (A := A) hSprime hdvd
  refine ⟨Q, hQ0, hQr, fun t => hQt t fun a ha => ?_⟩
  obtain ⟨u, huA, hu⟩ := ha
  rw [eq_zero_of_pow_eq_residueRadicand hodd hnil hζ hζA hSprime huA hu]
  simp

end InverseGalois.CFT

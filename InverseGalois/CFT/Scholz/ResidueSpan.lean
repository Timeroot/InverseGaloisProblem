/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Scholz.AuxPrimeChoice
import InverseGalois.CFT.Scholz.PowerResidue
import InverseGalois.CFT.Scholz.PrimeIndependence
import InverseGalois.CFT.Scholz.ResidueSymbol

/-!
# The power residue vectors of the auxiliary primes span everything

Fix a finite set `S` of rational primes.  An auxiliary prime `q` splitting completely in a given
nilpotent extension of the rationals containing the `ℓ`-th roots of unity records, through its power
residue symbol, a vector of `ZMod ℓ` indexed by `S`.  Those vectors span the whole space: a proper
subspace is annihilated by a nonzero linear form, the form is a vector of exponents, and the
corresponding product of powers of the primes of `S` is then an `ℓ`-th power residue modulo every
auxiliary prime — which is impossible, since that product is not an `ℓ`-th power in the rationals
and therefore admits an auxiliary prime for which it is not a power residue.

Consequently every prescribed vector of `ZMod ℓ` indexed by `S` is realised by a single character of
the units modulo a product of auxiliary primes, obtained by pulling the characters of the individual
primes back along the reduction maps and multiplying them with the appropriate exponents.

## Main definitions

* `InverseGalois.CFT.residueVector`: the vector of power residue symbols of the primes of `S`.

## Main results

* `InverseGalois.CFT.residueVectors_span_eq_top`: **the power residue vectors of the auxiliary
  primes span the whole space.**
* `InverseGalois.CFT.exists_modulus_powerResidueSymbol`: **every prescribed vector of power residue
  symbols is realised by a character of the units modulo a product of auxiliary primes.**

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

/-- A prime of `S` is a unit modulo an auxiliary prime, the two being distinct primes. -/
theorem isUnit_natCast_of_mem {q p : ℕ} (hq : q.Prime) (hqS : q ∉ S)
    (hSprime : ∀ p ∈ S, p.Prime) (hp : p ∈ S) : IsUnit ((p : ZMod q)) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  refine (ZMod.isUnit_iff_coprime p q).mpr ((Nat.coprime_primes (hSprime p hp) hq).mpr ?_)
  rintro rfl
  exact hqS hp

/-- **The power residue vectors of the auxiliary primes span the whole space.**  A proper subspace
is annihilated by a nonzero linear form; the form is a vector of exponents, and the corresponding
product of powers of the primes of `S` is not an `ℓ`-th power in the rationals, so some auxiliary
prime fails to have it as a power residue, contradicting the vanishing of the form. -/
theorem residueVectors_span_eq_top [Fact ℓ.Prime] (hodd : Odd ℓ) [NumberField ↥A] [IsGalois ℚ ↥A]
    (hnil : Group.IsNilpotent Gal(↥A/ℚ)) {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ ℓ)
    (hζA : ζ ∈ A) (hSprime : ∀ p ∈ S, p.Prime)
    (hdvd : ∀ q : ℕ, q.Prime → SplitsCompletely ↥A q → ℓ ∣ q - 1)
    (V : Submodule (ZMod ℓ) ({p // p ∈ S} → ZMod ℓ))
    (hV : ∀ (q : ℕ) (κ : (ZMod q)ˣ →* Multiplicative (ZMod ℓ)), q.Prime → q ∉ S →
      SplitsCompletely ↥A q → (∀ x : (ZMod q)ˣ, κ x = 1 ↔ (x : ZMod q) ^ ((q - 1) / ℓ) = 1) →
      residueVector S κ ∈ V) :
    V = ⊤ := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  by_contra hne
  -- a nonzero linear form annihilating the subspace
  obtain ⟨f, hf0, hfV⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (lt_of_le_of_ne le_top hne) inferInstance
  have hfker : ∀ x ∈ V, f x = 0 := by
    intro x hx
    have : f x ∈ V.map f := Submodule.mem_map_of_mem hx
    rw [hfV, Submodule.mem_bot] at this
    exact this
  set a : {p // p ∈ S} → ZMod ℓ := fun i => f (Pi.single i 1) with hadef
  have hfa : ∀ x : {p // p ∈ S} → ZMod ℓ, f x = ∑ i, x i * a i := by
    intro x
    conv_lhs => rw [pi_eq_sum_univ' x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
  obtain ⟨i₀, hi₀⟩ : ∃ i, a i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hf0 (LinearMap.ext fun x => by rw [hfa x]; simp [hc])
  -- the radicand attached to the linear form
  set e : ℕ → ℕ := fun p => if h : p ∈ S then (a ⟨p, h⟩).val else 0 with hedef
  have hei₀ : e i₀.1 = (a i₀).val := by simp only [hedef, dif_pos i₀.2]
  have hediv : ¬ ℓ ∣ e i₀.1 := by
    rw [hei₀]
    refine Nat.not_dvd_of_pos_of_lt ?_ (ZMod.val_lt (a i₀))
    exact Nat.pos_of_ne_zero fun h => hi₀ ((ZMod.val_eq_zero (a i₀)).mp h)
  set v : ℕ := ∏ p ∈ S, p ^ e p with hvdef
  have hnp : ∀ y : ℚ, y ^ ℓ ≠ ((v : ℤ) : ℚ) := by
    intro y
    have h := pow_ne_prod_pow (ℓ := ℓ) (a := e) hSprime i₀.2 hediv y
    rw [hvdef]
    push_cast at h ⊢
    exact h
  -- an auxiliary prime for which it is not a power residue
  obtain ⟨q, hqp, hqS, hqA, hqres⟩ :=
    exists_prime_splitsCompletely_pow_ne_one hodd hnil hζ hζA hnp S hdvd
  obtain ⟨κ, -, hκ⟩ := exists_powerResidueHom hℓ hqp (hdvd q hqp hqA)
  have hunit : ∀ p ∈ S, IsUnit ((p : ZMod q)) := fun p hp =>
    isUnit_natCast_of_mem hqp hqS hSprime hp
  have hvunit : IsUnit ((v : ZMod q)) := by
    rw [hvdef]
    push_cast
    exact Finset.prod_induction (fun p : ℕ => ((p : ZMod q)) ^ e p) IsUnit
      (fun _ _ => IsUnit.mul) isUnit_one fun p hp => (hunit p hp).pow _
  -- the symbol of the radicand is both nonzero and zero
  have hsymb : powerResidueSymbol κ v ≠ 0 := by
    intro h0
    rw [powerResidueSymbol_eq_zero_iff κ hκ hvunit] at h0
    exact hqres (by push_cast; exact h0)
  refine hsymb ?_
  rw [hvdef, powerResidueSymbol_prod_pow κ hunit,
    ← Finset.sum_attach S fun p => e p • powerResidueSymbol κ p]
  have hterm : ∀ i ∈ S.attach, e i.1 • powerResidueSymbol κ i.1 =
      residueVector S κ i * a i := by
    intro i _
    rw [nsmul_eq_mul]
    simp only [hedef, dif_pos i.2, Subtype.coe_eta, residueVector, ZMod.natCast_val, ZMod.cast_id]
    exact mul_comm _ _
  rw [Finset.sum_congr rfl hterm, ← Finset.univ_eq_attach, ← hfa]
  exact hfker _ (hV q κ hqp hqS hqA hκ)

/-- **Every prescribed vector of power residue symbols is realised by a character of the units
modulo a product of auxiliary primes.**  Writing the vector as a combination of the vectors of
finitely many auxiliary primes, the product of those primes is the modulus and the character is the
product of the corresponding powers of the characters of the individual primes, pulled back along
the reduction maps; the symbol being unchanged by such a pullback and additive in the character,
the combination is reproduced exactly. -/
theorem exists_modulus_powerResidueSymbol [Fact ℓ.Prime] (hodd : Odd ℓ) [NumberField ↥A]
    [IsGalois ℚ ↥A] (hnil : Group.IsNilpotent Gal(↥A/ℚ)) {ζ : AlgebraicClosure ℚ}
    (hζ : IsPrimitiveRoot ζ ℓ) (hζA : ζ ∈ A) (hSprime : ∀ p ∈ S, p.Prime)
    (hdvd : ∀ q : ℕ, q.Prime → SplitsCompletely ↥A q → ℓ ∣ q - 1) (t : {p // p ∈ S} → ZMod ℓ) :
    ∃ (Q : ℕ) (κ : (ZMod Q)ˣ →* Multiplicative (ZMod ℓ)), Q ≠ 0 ∧
      (∀ r : ℕ, r.Prime → r ∣ Q → r ∉ S ∧ SplitsCompletely ↥A r) ∧
      ∀ (p : ℕ) (hp : p ∈ S), powerResidueSymbol κ p = t ⟨p, hp⟩ := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  -- the vectors of the auxiliary primes span, so the target is a combination of finitely many
  have hspan : Submodule.span (ZMod ℓ)
      {w : {p // p ∈ S} → ZMod ℓ | ∃ (q : ℕ) (κ : (ZMod q)ˣ →* Multiplicative (ZMod ℓ)),
        q.Prime ∧ q ∉ S ∧ SplitsCompletely ↥A q ∧
        (∀ x : (ZMod q)ˣ, κ x = 1 ↔ (x : ZMod q) ^ ((q - 1) / ℓ) = 1) ∧
        w = residueVector S κ} = ⊤ :=
    residueVectors_span_eq_top hodd hnil hζ hζA hSprime hdvd _
      fun q κ hq hqS hqA hκ => Submodule.subset_span ⟨q, κ, hq, hqS, hqA, hκ, rfl⟩
  have ht : t ∈ Submodule.span (ZMod ℓ)
      {w : {p // p ∈ S} → ZMod ℓ | ∃ (q : ℕ) (κ : (ZMod q)ˣ →* Multiplicative (ZMod ℓ)),
        q.Prime ∧ q ∉ S ∧ SplitsCompletely ↥A q ∧
        (∀ x : (ZMod q)ˣ, κ x = 1 ↔ (x : ZMod q) ^ ((q - 1) / ℓ) = 1) ∧
        w = residueVector S κ} := by
    rw [hspan]; trivial
  obtain ⟨n, c, g, hg⟩ := Submodule.mem_span_set'.mp ht
  have hmem : ∀ i : Fin n, ∃ (q : ℕ) (κ : (ZMod q)ˣ →* Multiplicative (ZMod ℓ)),
      q.Prime ∧ q ∉ S ∧ SplitsCompletely ↥A q ∧
      (∀ x : (ZMod q)ˣ, κ x = 1 ↔ (x : ZMod q) ^ ((q - 1) / ℓ) = 1) ∧
      (g i : {p // p ∈ S} → ZMod ℓ) = residueVector S κ := fun i => (g i).2
  choose qq κκ hqqp hqqS hqqA hqqκ hqqvec using hmem
  -- the modulus and the character
  set Q : ℕ := ∏ i, qq i with hQdef
  have hQ0 : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => (hqqp i).ne_zero
  haveI : NeZero Q := ⟨hQ0⟩
  have hdvdQ : ∀ i, qq i ∣ Q := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  refine ⟨Q, ∏ i : Fin n, ((κκ i).comp (ZMod.unitsMap (hdvdQ i))) ^ (c i).val, hQ0, ?_, ?_⟩
  · intro r hr hrQ
    obtain ⟨i, -, hri⟩ := (Nat.Prime.prime hr).exists_mem_finset_dvd hrQ
    obtain rfl : r = qq i := (Nat.prime_dvd_prime_iff_eq hr (hqqp i)).mp hri
    exact ⟨hqqS i, hqqA i⟩
  · intro p hp
    -- a prime of `S` is a unit modulo the product of the auxiliary primes
    have hpQ : IsUnit ((p : ZMod Q)) := by
      refine (ZMod.isUnit_iff_coprime p Q).mpr (Nat.Coprime.prod_right fun i _ => ?_)
      exact (Nat.coprime_primes (hSprime p hp) (hqqp i)).mpr fun h => hqqS i (h ▸ hp)
    have hpi : ∀ i : Fin n, IsUnit ((p : ZMod (qq i))) :=
      fun i => isUnit_natCast_of_mem (hqqp i) (hqqS i) hSprime hp
    rw [powerResidueSymbol_prod_hom _ _ hpQ]
    have hterm : ∀ i : Fin n, powerResidueSymbol
        (((κκ i).comp (ZMod.unitsMap (hdvdQ i))) ^ (c i).val) p =
          c i * (g i : {p // p ∈ S} → ZMod ℓ) ⟨p, hp⟩ := by
      intro i
      rw [powerResidueSymbol_pow_hom _ _ hpQ,
        powerResidueSymbol_comp_unitsMap (κκ i) (hdvdQ i) hpQ, hqqvec i, residueVector,
        nsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id]
    rw [Finset.sum_congr rfl fun i _ => hterm i, ← hg, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => rfl

end InverseGalois.CFT

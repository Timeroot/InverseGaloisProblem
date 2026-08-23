import Mathlib

/-!
# The Frobenius element of a cyclotomic field

For a cyclotomic field `K = ℚ(ζₙ)` and a rational prime `p` not dividing `n`, the Frobenius
automorphism at a prime of `𝓞 K` above `p` is the element `p` of `(ℤ/nℤ)ˣ` under the canonical
identification of `Gal(ℚ(ζₙ)/ℚ)` with `(ℤ/nℤ)ˣ`. This is the reciprocity law for the rational field:
the Artin symbol of `p` is its own residue class.

## Main results

* `InverseGalois.CFT.galEquivZMod_eq_of_isArithFrobAt`: an arithmetic Frobenius at a prime above `p`
  corresponds to the unit `p` of `ZMod n`.
* `InverseGalois.CFT.galEquivZMod_arithFrobAt`: the same for the chosen Frobenius element
  `arithFrobAt`.
* `InverseGalois.CFT.orderOf_arithFrobAt`: the order of the Frobenius at `p` is the multiplicative
  order of `p` modulo `n`.
-/

open NumberField IsCyclotomicExtension

namespace InverseGalois.CFT

/-- The ring of integers of a Galois number field is invariant over `ℤ`: an algebraic integer
fixed by the whole Galois group is rational, hence an ordinary integer. -/
instance isInvariant_ringOfIntegers (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K] :
    Algebra.IsInvariant ℤ (𝓞 K) Gal(K/ℚ) := by
  refine ⟨fun b hb => ?_⟩
  obtain ⟨q, hq⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := ℚ) (b : K)).mpr
    fun g => congrArg (algebraMap (𝓞 K) K) (hb g)
  have hqint : IsIntegral ℤ q := by
    rw [← isIntegral_algebraMap_iff (B := K) (algebraMap ℚ K).injective, hq]
    exact b.isIntegral.map (IsScalarTower.toAlgHom ℤ (𝓞 K) K)
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hqint
  refine ⟨m, ?_⟩
  apply FaithfulSMul.algebraMap_injective (𝓞 K) K
  rw [← IsScalarTower.algebraMap_apply ℤ (𝓞 K) K, IsScalarTower.algebraMap_apply ℤ ℚ K, hm, hq]

variable (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {n} ℚ K]

omit [NeZero n] [NumberField K] [IsCyclotomicExtension {n} ℚ K] in
/-- A rational prime not dividing the conductor is coprime to it. -/
theorem coprime_of_prime_not_dvd {p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n) : Nat.Coprime p n :=
  (Nat.Prime.coprime_iff_not_dvd hp).mpr hpn

variable {n K}

omit [NeZero n] [NumberField K] [IsCyclotomicExtension {n} ℚ K] in
/-- The rational prime below a prime of a cyclotomic field does not lie in that prime unless it
divides the conductor. -/
theorem natCast_conductor_notMem {p : ℕ} (hpn : ¬ p ∣ n) (P : Ideal (𝓞 K))
    (hP : P.under ℤ = Ideal.span {(p : ℤ)}) : (n : 𝓞 K) ∉ P := by
  intro hmem
  have hZ : (n : ℤ) ∈ P.under ℤ := by
    rw [Ideal.under, Ideal.mem_comap]
    simpa using hmem
  rw [hP, Ideal.mem_span_singleton] at hZ
  exact hpn (Int.ofNat_dvd.mp (by exact_mod_cast hZ))

omit [NumberField K] in
/-- The residue field of the rational prime below `P` has cardinality `p`. -/
theorem card_quotient_under {p : ℕ} (P : Ideal (𝓞 K)) (hP : P.under ℤ = Ideal.span {(p : ℤ)}) :
    Nat.card (ℤ ⧸ P.under ℤ) = p := by
  rw [hP, Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]

/-- **The reciprocity law for the rational field.**  An arithmetic Frobenius at a prime of `ℚ(ζₙ)`
above a rational prime `p` not dividing `n` is the class of `p` in `(ℤ/nℤ)ˣ`. -/
theorem galEquivZMod_eq_of_isArithFrobAt {p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n)
    (P : Ideal (𝓞 K)) (hP : P.under ℤ = Ideal.span {(p : ℤ)})
    (σ : Gal(K/ℚ)) (hσ : IsArithFrobAt ℤ σ P) :
    Rat.galEquivZMod n K σ = ZMod.unitOfCoprime p (coprime_of_prime_not_dvd n hp hpn) := by
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ K
  set z : 𝓞 K := hζ.toInteger with hzdef
  have hz : IsPrimitiveRoot z n := hζ.toInteger_isPrimitiveRoot
  -- the Frobenius raises the root of unity to the `p`-th power
  have hfrob : σ • z = z ^ p := by
    have := hσ.apply_of_pow_eq_one hz.pow_eq_one (natCast_conductor_notMem hpn P hP)
    rwa [card_quotient_under P hP] at this
  -- and it raises it to the power recorded by the Galois-theoretic identification
  have hgal : σ • z = z ^ (Rat.galEquivZMod n K σ).val.val :=
    Rat.galEquivZMod_smul_of_pow_eq n K σ hz.pow_eq_one
  have hpow : z ^ (Rat.galEquivZMod n K σ).val.val = z ^ p := hgal.symm.trans hfrob
  rw [(hz.isOfFinOrder (NeZero.ne _)).pow_inj_mod, ← hz.eq_orderOf,
    ← ZMod.natCast_eq_natCast_iff', ZMod.natCast_val, ZMod.cast_id] at hpow
  rw [Units.ext_iff, ZMod.coe_unitOfCoprime]
  exact hpow

variable (n K) [IsGalois ℚ K]

/-- The chosen Frobenius element at a prime of `ℚ(ζₙ)` above `p` is the class of `p` in
`(ℤ/nℤ)ˣ`. -/
theorem galEquivZMod_arithFrobAt {p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n)
    (P : Ideal (𝓞 K)) [P.IsPrime] [Finite (𝓞 K ⧸ P)]
    (hP : P.under ℤ = Ideal.span {(p : ℤ)}) :
    Rat.galEquivZMod n K (arithFrobAt ℤ Gal(K/ℚ) P) =
      ZMod.unitOfCoprime p (coprime_of_prime_not_dvd n hp hpn) :=
  galEquivZMod_eq_of_isArithFrobAt hp hpn P hP _ (IsArithFrobAt.arithFrobAt ℤ Gal(K/ℚ) P)

/-- The Frobenius at `p` has order the multiplicative order of `p` modulo `n`. -/
theorem orderOf_arithFrobAt {p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n)
    (P : Ideal (𝓞 K)) [P.IsPrime] [Finite (𝓞 K ⧸ P)]
    (hP : P.under ℤ = Ideal.span {(p : ℤ)}) :
    orderOf (arithFrobAt ℤ Gal(K/ℚ) P) = orderOf (p : ZMod n) := by
  rw [← orderOf_injective (Rat.galEquivZMod n K).toMonoidHom (Rat.galEquivZMod n K).injective,
    MulEquiv.coe_toMonoidHom, galEquivZMod_arithFrobAt n K hp hpn P hP, ← orderOf_units,
    ZMod.coe_unitOfCoprime]

end InverseGalois.CFT

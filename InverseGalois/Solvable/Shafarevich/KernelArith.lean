/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.NamedUnits
import InverseGalois.CFT.PoitouTate.OrbitLine
import InverseGalois.Solvable.Shafarevich.KernelPlaces

/-!
# The families of units the prescription is made of, bought from the arithmetic

The whole prescription over the field the base realization cuts out was reduced to a single
statement about that level: name finitely many places lying in distinct orbits, prescribe a class
at each of them in each coordinate, and ask for a family of units of the level carrying those
classes, dying at the proper conjugates of the named places and at a further prescribed finite set
of places, and confined everywhere else to places sitting over a named one or completely decomposed
in a given finite level.  That is exactly the shape the two-place construction over a number field
answers, and this file matches the two.

Setting the bookkeeping up is a matter of reading the named places as a finite set of places, the
prescribed classes as a family indexed by that finite set, and the lines the classes at one place
lie on as a family spread over the orbits of the named places, so that the line at the image of a
place is the image of the line there.  The finite level the leftover places are asked to be
decomposed in is replaced by its normal closure over the base, which changes nothing: a place
decomposed in the larger field is decomposed in the smaller one, and the decomposition group of a
prime of the closure lands in the one of the prime below it.  The places ramified in that closure
are finitely many, because a place ramifies exactly when the prime below it divides the different
and a nonzero ideal has finitely many prime divisors.

What the construction does not carry by itself is the reciprocity residue.  The product of the
power residue symbols over all the places of a global unit against the prescribed classes vanishes,
and away from the named places the prescription contributes nothing, so what is left is a condition
relating the classes named at the named places to the units of the level which become
exponent-th powers in the auxiliary field.  That condition is named here and is the one arithmetic
input the prescription still asks for.

## Main definitions

* `InverseGalois.Shafarevich.HasNamedPairing` — the classes prescribed at a finite family of places
  pair trivially with every unit supported at those places which is an exponent-th power in a given
  finite level and trivial at every infinite place.

## Main results

* `InverseGalois.Shafarevich.exists_finset_forall_ramIdx_eq_one` — **outside a finite set of places
  every place of a number field has an unramified prime above it in a finite extension.**
* `InverseGalois.Shafarevich.exists_prime_natCast_mem_asIdeal` — **every finite place lies above a
  rational prime**, its residue characteristic.
* `InverseGalois.Shafarevich.stabilizer_le_fixingSubgroup_of_stabilizer_eq_bot` — **a prime of the
  closure lying over a place with trivial decomposition group in a finite level has its whole
  decomposition group fixing that level.**
* `InverseGalois.Shafarevich.hasPrescribedUnits_of_hasNamedPairing` — **a level whose prescribed
  classes pair trivially with the units carries the families of units the prescription is made
  of.**

## Tags

Shafarevich's theorem, embedding problem, power residue symbol, reciprocity, Kummer theory
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT IsDedekindDomain IntermediateField MulAction NumberField

open scoped Pointwise

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 1600000

/-! ### The places ramified in a finite extension -/

section Ramified

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra in
/-- **Outside a finite set of places every place of a number field has an unramified prime above it
in a finite extension.**  A prime above a place is unramified exactly when it does not divide the
different, the different is nonzero, and a nonzero ideal has finitely many prime divisors. -/
theorem exists_finset_forall_ramIdx_eq_one (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), ∀ v ∉ T,
      ∃ W : HeightOneSpectrum (𝓞 L), primeUnder (𝓞 K) W = v ∧ ramIdx (𝓞 K) W = 1 := by
  classical
  have hD : differentIdeal (𝓞 K) (𝓞 L) ≠ 0 := by
    simpa [Ideal.zero_eq_bot] using (differentIdeal_ne_bot (A := 𝓞 K) (B := 𝓞 L))
  have hfin : {W : HeightOneSpectrum (𝓞 L) | W.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 L)}.Finite :=
    Ideal.finite_factors hD
  refine ⟨hfin.toFinset.image (fun W => primeUnder (𝓞 K) W), ?_⟩
  intro v hv
  obtain ⟨W, hW⟩ := exists_primeUnder_eq (𝓞 K) (𝓞 L) v
  refine ⟨W, hW, ?_⟩
  have hnd : ¬ W.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 L) := by
    intro hdvd
    exact hv (Finset.mem_image.2 ⟨W, hfin.mem_toFinset.2 hdvd, hW⟩)
  haveI : W.asIdeal.IsPrime := W.isPrime
  haveI : Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal := not_dvd_differentIdeal_iff.1 hnd
  exact ramIdx_eq_one_of_isUnramifiedAt W

/-- **Every finite place lies above a rational prime**, the characteristic of its residue field.
The residue field is a finite field, so its characteristic is a prime, and a natural number is
zero in the residue field exactly when it lies in the place. -/
theorem exists_prime_natCast_mem_asIdeal (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) : ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  haveI := v.isPrime
  haveI : v.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal v.isPrime v.ne_bot
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := inferInstance
  letI : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  refine ⟨ringChar (𝓞 K ⧸ v.asIdeal), ?_, ?_⟩
  · haveI : CharP (𝓞 K ⧸ v.asIdeal) (ringChar (𝓞 K ⧸ v.asIdeal)) := ringChar.charP _
    exact CharP.char_is_prime (𝓞 K ⧸ v.asIdeal) (ringChar (𝓞 K ⧸ v.asIdeal))
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact (ringChar.spec _ _).2 dvd_rfl

end Ramified

/-! ### The decomposition group of a prime over a decomposed place -/

section Decomposition

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]

/-- **A prime of the closure lying over a place with trivial decomposition group in a finite level
has its whole decomposition group fixing that level.**  The place below the prime and the place
with trivial decomposition group lie over the same place of the base, so they are conjugate, and
conjugate places have conjugate decomposition groups. -/
theorem stabilizer_le_fixingSubgroup_of_stabilizer_eq_bot {W : IntermediateField k Ω}
    [NumberField ↥W] [FiniteDimensional k ↥W] [IsGalois k ↥W]
    {W' : HeightOneSpectrum (𝓞 ↥W)} (hW' : stabilizer Gal(↥W/k) W' = ⊥)
    {P : Ideal (𝓞 Ω)} [P.IsPrime] (hP : P ≠ ⊥)
    (hPu : Ideal.under (𝓞 k) P = Ideal.under (𝓞 k) W'.asIdeal) :
    stabilizer Gal(Ω/k) P ≤ W.fixingSubgroup := by
  classical
  have hunder : primeUnder (𝓞 k) W' = primeUnder (𝓞 k) (placeUnder W P hP) := by
    refine HeightOneSpectrum.ext ?_
    rw [primeUnder_asIdeal, primeUnder_asIdeal, placeUnder_asIdeal, Ideal.under_under, hPu]
  obtain ⟨τ, hτ⟩ := exists_smul_eq_of_primeUnder_eq (A := 𝓞 k) (G := Gal(↥W/k)) hunder
  have hst : stabilizer Gal(↥W/k) (placeUnder W P hP) = ⊥ := by
    rw [← hτ, MulAction.stabilizer_smul_eq_stabilizer_map_conj, hW']
    exact Subgroup.map_bot _
  rw [← IntermediateField.restrictNormalHom_ker W]
  exact stabilizer_le_ker_of_stabilizer_placeUnder_eq_bot
    (φ := AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥W)
    (IntermediateField.restrictNormalHom_ker W).symm hP hst

end Decomposition

/-! ### The reciprocity residue -/

section Pairing

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  [IsAlgClosed Ω]

/-- **The classes prescribed at a finite family of places pair trivially with every unit supported
at those places which is an exponent-th power in a given finite level and trivial at every infinite
place.**

The product formula makes the power residue symbol of a global unit against a family of local
classes trivial over all the places at once, and away from the named places the family prescribed
here contributes nothing.  What is left is a condition on the classes named at the named places,
read against the units of the level which become exponent-th powers in a finite level named along
with them; the level enters only through the units it turns into exponent-th powers, so it is asked
for as a subfield of the closure rather than as an extension of the level. -/
def HasNamedPairing (ℓ : ℕ) [NeZero ℓ] (K : IntermediateField k Ω) [NumberField ↥K]
    {Pc Ec : HeightOneSpectrum (𝓞 ↥K) → ℕ}
    (hres : ∀ v : HeightOneSpectrum (𝓞 ↥K), HasResidueChar (v.adicCompletion ↥K) (Pc v) (Ec v))
    {ζ : ↥K} (hζ : IsPrimitiveRoot ζ ℓ) : Prop :=
  ∀ W : IntermediateField k Ω, FiniteDimensional k ↥W → K ≤ W →
    ∀ (Tp Tn : Finset (HeightOneSpectrum (𝓞 ↥K))), Tp ⊆ Tn →
      ∀ (cl : (w : ↥Tp) → ℕ → localClasses (w : HeightOneSpectrum (𝓞 ↥K)) ℓ) (t : ℕ)
        (u : ↥(sUnits ↥K (Set.range (Subtype.val : ↥Tn → HeightOneSpectrum (𝓞 ↥K))))),
        (∀ w : InfinitePlace ↥K, infClassHom w ℓ ((u : (↥K)ˣ)) = 1) →
        (∃ y : Ω, y ∈ W ∧ y ^ ℓ = algebraMap ↥K Ω ((u : (↥K)ˣ) : ↥K)) →
        localSymbolPiPairing hres hζ (Subtype.val : ↥Tn → HeightOneSpectrum (𝓞 ↥K))
          (sUnitClassHom (Subtype.val : ↥Tn → HeightOneSpectrum (𝓞 ↥K)) ℓ u)
          (fun y => spreadClasses Tp cl t (y : HeightOneSpectrum (𝓞 ↥K))) = 1

/-- **A level whose prescribed classes pair trivially with the units carries the families of units
the prescription is made of.**

The named places are read as a finite set of places and the classes prescribed at them as a family
indexed by that set, the transport along the naming being harmless because the naming is injective.
The lines the classes lie on are named by units of the level, which lets them be spread over the
orbits of the named places, and the finite level the leftover places are asked to be decomposed in
is replaced by its normal closure over the base.  With that bookkeeping the two-place construction
produces the family of units, and each of the four clauses of the demand is one of its four
conclusions read back through the naming. -/
theorem hasPrescribedUnits_of_hasNamedPairing {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) (hodd : 2 < ℓ)
    (K : IntermediateField k Ω) [FiniteDimensional k ↥K] [IsGalois k ↥K] [NumberField ↥K]
    {Pc Ec : HeightOneSpectrum (𝓞 ↥K) → ℕ}
    (hres : ∀ v : HeightOneSpectrum (𝓞 ↥K), HasResidueChar (v.adicCompletion ↥K) (Pc v) (Ec v))
    {ζ : ↥K} (hζ : IsPrimitiveRoot ζ ℓ) (hpair : HasNamedPairing ℓ K hres hζ) :
    HasPrescribedUnits ℓ K := by
  classical
  intro E hEfin hKE ι hι w hwinj hwconj Tz hTz hℓw d c hline
  haveI := hι
  haveI := hEfin
  letI : Fintype ι := Fintype.ofFinite ι
  -- the finite normal level the leftover places are asked to be decomposed in
  obtain ⟨W, hWdef⟩ : ∃ W : IntermediateField k Ω, W = normalClosure k ↥E Ω := ⟨_, rfl⟩
  haveI : FiniteDimensional k ↥W := by
    rw [hWdef]; exact normalClosure.is_finiteDimensional k ↥E Ω
  haveI : Normal k ↥W := by rw [hWdef]; exact normalClosure.normal k ↥E Ω
  haveI : IsGalois k ↥W := ⟨⟩
  haveI : NumberField ↥W := NumberField.of_module_finite k ↥W
  have hEW : E ≤ W := by rw [hWdef]; exact IntermediateField.le_normalClosure _
  have hKW : K ≤ W := le_trans hKE hEW
  letI : Algebra ↥K ↥W := inferInstanceAs (Algebra ↥K ↥(extendScalars hKW))
  haveI : IsScalarTower k ↥K ↥W := inferInstanceAs (IsScalarTower k ↥K ↥(extendScalars hKW))
  haveI : IsScalarTower ↥K ↥W Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsGalois ↥K ↥W := IsGalois.tower_top_of_isGalois k ↥K ↥W
  -- the named places, read as a finite set
  obtain ⟨Tp, hTpdef⟩ : ∃ Tp : Finset (HeightOneSpectrum (𝓞 ↥K)),
      Tp = Finset.image w Finset.univ := ⟨_, rfl⟩
  have hmemTp : ∀ μ : ι, w μ ∈ Tp := by
    intro μ
    rw [hTpdef]
    exact Finset.mem_image.2 ⟨μ, Finset.mem_univ μ, rfl⟩
  have hmem : ∀ v ∈ Tp, ∃ μ : ι, w μ = v := by
    intro v hv
    rw [hTpdef] at hv
    obtain ⟨μ, -, hμ⟩ := Finset.mem_image.1 hv
    exact ⟨μ, hμ⟩
  have hex : ∀ x : ↥Tp, ∃ μ : ι, w μ = (x : HeightOneSpectrum (𝓞 ↥K)) := fun x => hmem _ x.2
  choose idx hidx using hex
  -- the prescribed classes, read at the finite set
  have htr : ∀ (ν μ : ι) (h : w ν = w μ) (q : Fin d),
      cast (congrArg (fun v => localClasses v ℓ) h) (c ν q) = c μ q := by
    intro ν μ h q
    obtain rfl : ν = μ := hwinj h
    rfl
  obtain ⟨cl, hcldef⟩ : ∃ cl : (x : ↥Tp) → ℕ → localClasses (x : HeightOneSpectrum (𝓞 ↥K)) ℓ,
      cl = fun x t => if h : t < d then
        cast (congrArg (fun v => localClasses v ℓ) (hidx x)) (c (idx x) ⟨t, h⟩) else 1 :=
    ⟨_, rfl⟩
  have hclval : ∀ (μ : ι) (hwm : w μ ∈ Tp) (q : Fin d),
      cl ⟨w μ, hwm⟩ (q : ℕ) = c μ q := by
    intro μ hwm q
    rw [hcldef]
    simp only [dif_pos q.isLt]
    exact htr (idx ⟨w μ, hwm⟩) μ (hidx ⟨w μ, hwm⟩) q
  -- the lines the classes at the named places lie on
  choose aU haU using hline
  obtain ⟨a, hadef⟩ : ∃ a : ↥Tp → (↥K)ˣ, a = fun x => aU (idx x) := ⟨_, rfl⟩
  have hfree : ∀ σ : Gal(↥K/k), σ ≠ 1 → ∀ x ∈ Tp, σ • x ∉ Tp := by
    intro σ hσ x hx hcon
    rw [hTpdef] at hx hcon
    obtain ⟨μ, -, hμ⟩ := Finset.mem_image.1 hx
    obtain ⟨ν, -, hν⟩ := Finset.mem_image.1 hcon
    exact hwconj μ ν σ hσ (by rw [hμ, hν])
  have hDcl : ∀ (x : ↥Tp) (t : ℕ),
      cl x t ∈ Subgroup.zpowers (orbitLine k Tp a ℓ (x : HeightOneSpectrum (𝓞 ↥K))) := by
    intro x t
    rw [orbitLine_mem hfree]
    by_cases h : t < d
    · rw [hcldef]
      simp only [dif_pos h]
      have hgen : ∀ (v : HeightOneSpectrum (𝓞 ↥K)) (hv : w (idx x) = v),
          cast (congrArg (fun v => localClasses v ℓ) hv) (c (idx x) ⟨t, h⟩)
            ∈ Subgroup.zpowers (localClassHom v ℓ (a x)) := by
        intro v hv
        subst hv
        rw [hadef]
        simpa using haU (idx x) ⟨t, h⟩
      exact hgen _ (hidx x)
    · rw [hcldef]
      simp only [dif_neg h]
      exact Subgroup.one_mem _
  have hcln : ∀ (x : ↥Tp) (t : ℕ),
      FinitePlace.mk (x : HeightOneSpectrum (𝓞 ↥K)) ((ℓ : ℕ) : ↥K) ≠ 1 → cl x t = 1 := by
    intro x t hne
    refine absurd ((finitePlace_natCast_eq_one_iff _ ℓ).2 ?_) hne
    rw [← hidx x]
    exact hℓw (idx x)
  have hdisj : ∀ v ∈ Tp, v ∉ Tz := by
    intro v hv
    rw [hTpdef] at hv
    obtain ⟨μ, -, rfl⟩ := Finset.mem_image.1 hv
    exact hTz μ
  obtain ⟨Tram, hTram⟩ := exists_finset_forall_ramIdx_eq_one ↥K ↥W
  -- the reciprocity residue
  have horth : ∀ Tn : Finset (HeightOneSpectrum (𝓞 ↥K)), Tp ⊆ Tn → ∀ (t : ℕ)
      (u : ↥(sUnits ↥K (Set.range (Subtype.val : ↥Tn → HeightOneSpectrum (𝓞 ↥K))))),
      (∀ y : InfinitePlace ↥K, infClassHom y ℓ ((u : (↥K)ˣ)) = 1) →
      (∃ y : (↥W)ˣ, Units.map (algebraMap ↥K ↥W : ↥K →* ↥W) ((u : (↥K)ˣ)) = y ^ ℓ) →
      localSymbolPiPairing hres hζ (Subtype.val : ↥Tn → HeightOneSpectrum (𝓞 ↥K))
        (sUnitClassHom (Subtype.val : ↥Tn → HeightOneSpectrum (𝓞 ↥K)) ℓ u)
        (fun y => spreadClasses Tp cl t (y : HeightOneSpectrum (𝓞 ↥K))) = 1 := by
    intro Tn hsub t u hinf hpow
    refine hpair W inferInstance hKW Tp Tn hsub cl t u hinf ?_
    obtain ⟨y, hy⟩ := hpow
    refine ⟨((y : ↥W) : Ω), (y : ↥W).2, ?_⟩
    have hval : algebraMap ↥K ↥W ((u : (↥K)ˣ) : ↥K) = ((y : ↥W)) ^ ℓ := by
      simpa using congrArg Units.val hy
    have hcoe : ((algebraMap ↥K ↥W ((u : (↥K)ˣ) : ↥K) : ↥W) : Ω) = (((y : ↥W) : Ω)) ^ ℓ := by
      rw [hval]
      push_cast
      ring
    rw [← hcoe, IsScalarTower.algebraMap_apply ↥K ↥W Ω]
    rfl
  obtain ⟨z, hz1, hz2, hz3, hz4⟩ := exists_units_named_prescribed (k := k) (A := Ω) (K := ↥K)
    (Ω := W) (p := ℓ) hℓ hodd hζ hres (Tp := Tp) (Tz := Tz) (Tram := Tram) hdisj hTram
    (cl := cl) hfree hcln (D := orbitLine k Tp a ℓ) (orbitLine_zpowers_smul hfree a) hDcl horth d
  refine ⟨fun q => z (q : ℕ), fun q v hv => hz1 q q.isLt v hv, ?_, ?_, ?_⟩
  · intro μ q
    rw [hz2 q q.isLt ⟨w μ, hmemTp μ⟩]
    exact hclval μ (hmemTp μ) q
  · intro μ σ hσ q
    exact hz3 q q.isLt σ ⟨w μ, hmemTp μ⟩ hσ
  · intro v hv
    obtain ⟨q, hq⟩ := hv
    rcases hz4 v ⟨q, q.isLt, hq⟩ with ⟨σ, x, hvx⟩ | ⟨⟨W', hW'u, hW'st⟩, ⟨q₀, hq₀d, hq₀⟩, hconj⟩
    · exact Or.inl ⟨idx x, σ, by rw [hidx x]; exact hvx⟩
    · refine Or.inr ⟨?_, ⟨⟨q₀, hq₀d⟩, fun q hqne => hq₀ q q.isLt fun hcon => hqne (Fin.ext hcon)⟩,
        fun σ hσ q => hconj σ hσ q q.isLt⟩
      intro P hPp hPbot hPu
      haveI := hPp
      refine le_trans ?_ (IntermediateField.fixingSubgroup_le hEW)
      refine stabilizer_le_fixingSubgroup_of_stabilizer_eq_bot hW'st hPbot ?_
      have h1 : Ideal.under (𝓞 k) P = Ideal.under (𝓞 k) v.asIdeal := by
        rw [← hPu, Ideal.under_under]
      have h2 : Ideal.under (𝓞 k) W'.asIdeal = Ideal.under (𝓞 k) v.asIdeal := by
        rw [← Ideal.under_under (A := 𝓞 k) (B := 𝓞 ↥K) W'.asIdeal, ← primeUnder_asIdeal, hW'u]
      rw [h1, h2]

end Pairing

end InverseGalois.Shafarevich

import Mathlib
import InverseGalois.CFT.Cyclotomic.InertiaOrder
import InverseGalois.CFT.Decomposition
import InverseGalois.CFT.InertiaAbelian
import InverseGalois.CFT.InertiaRestrict
import InverseGalois.CFT.Scholz.Condition

/-!
# The inertia subgroup dictionary

Let `K` be a number field which is Galois over `ℚ`, let `p` be a rational prime and let `P` be a
prime of `𝓞 K` lying over `(p)`.  The local invariants `e` and `f` of `P` are visible inside the
Galois group `Gal(K/ℚ)`: the order of the inertia subgroup `Ideal.inertia Gal(K/ℚ) P` is `e`, the
order of the decomposition subgroup `MulAction.stabilizer Gal(K/ℚ) P` is `e * f`, and the two
subgroups agree exactly when `f = 1`.  This file translates the ramification predicates used
elsewhere in this development — membership in `ramifiedSet K`, the residue-degree condition
`IsSplitInertia`, total ramification — into statements about these subgroups.

Restriction to a normal subextension `F` maps inertia into inertia, so if `p` is unramified in `F`
then the inertia subgroup at `p` upstairs acts trivially on `F`, that is, it is contained in the
fixing subgroup of `F`.  Inertia subgroups at `p` therefore see only the part of `K` where `p`
actually ramifies.  The last section turns this containment into an equality for cyclotomic
fields: if `p` divides the conductor `M` exactly once, the inertia subgroup at `p` in `ℚ(ζ_M)` is
precisely the subgroup fixing `ℚ(ζ_{M / p})`, the two subgroups both having order `p - 1`.

## Main results

* `InverseGalois.CFT.card_inertia_eq_ramificationIdx_span`: the order of the inertia subgroup is
  the ramification index of `P` over `(p)`.
* `InverseGalois.CFT.inertia_ne_bot_iff_mem_ramifiedSet`: **a rational prime is ramified exactly
  when the inertia subgroup above it is nontrivial.**
* `InverseGalois.CFT.inertia_eq_bot_of_notMem_ramifiedSet`: at an unramified prime the inertia
  subgroup is trivial.
* `InverseGalois.CFT.inertiaDeg_eq_one_iff_inertia_eq_stabilizer`: **the residue degree is one
  exactly when inertia is the whole decomposition group.**
* `InverseGalois.CFT.inertia_eq_stabilizer_of_isSplitInertia`: split inertia realises the
  decomposition group at a ramified prime as its inertia group.
* `InverseGalois.CFT.inertia_eq_top_iff_card_eq_finrank` and
  `InverseGalois.CFT.inertia_eq_top_iff_ramificationIdx_eq_finrank`: **the inertia subgroup is the
  whole Galois group exactly when the prime is totally ramified.**
* `InverseGalois.CFT.map_inertia_le_inertia`: restriction to a normal subextension maps the inertia
  subgroup into the inertia subgroup below.
* `InverseGalois.CFT.inertia_le_fixingSubgroup`: **inertia at a prime unramified in a normal
  subextension `F` acts trivially on `F`.**
* `InverseGalois.CFT.inertia_eq_fixingSubgroup_of_mul` and
  `InverseGalois.CFT.inertia_eq_fixingSubgroup_of_squarefree`: **the inertia subgroup of
  `Gal(ℚ(ζ_M)/ℚ)` at a prime exactly dividing `M` is the subgroup fixing `ℚ(ζ_{M / p})`.**
-/

open NumberField InverseGalois.NumberTheory

open scoped Pointwise

namespace InverseGalois.CFT

variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K] {p : ℕ}

section Basic

/-- Two subgroups of a finite group, one contained in the other and of the same order, are
equal. -/
theorem eq_of_le_of_card_eq {G : Type*} [Group G] [Finite G] {H J : Subgroup G} (hle : H ≤ J)
    (hcard : Nat.card H = Nat.card J) : H = J :=
  le_antisymm hle (Subgroup.subgroupOf_eq_top.mp (Subgroup.eq_top_of_card_eq _
    ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv).trans hcard)))

omit [NumberField K] [IsGalois ℚ K] in
/-- The rational prime under a prime of `𝓞 K` lying over `(p)` is `(p)`. -/
theorem under_eq_span_of_liesOver (P : Ideal (𝓞 K)) [P.LiesOver (Ideal.span {(p : ℤ)})] :
    P.under ℤ = Ideal.span {(p : ℤ)} :=
  Ideal.LiesOver.over.symm

/-- **The order of the inertia subgroup is the ramification index**, in the form indexed by the
rational prime below. -/
theorem card_inertia_eq_ramificationIdx_span (hp : p.Prime) (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Nat.card (Ideal.inertia Gal(K/ℚ) P) =
      Ideal.ramificationIdx (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) P := by
  haveI := Fact.mk hp
  rw [card_inertia_eq_ramificationIdx P (ne_bot_of_liesOver p P),
    under_eq_span_of_liesOver (p := p) P]

end Basic

section Ramified

/-- **A rational prime ramifies exactly when the inertia subgroup above it is nontrivial.**  The
order of the inertia subgroup at `P` is the ramification index of `P`, and in a Galois extension
that index does not depend on the prime above `p` chosen to witness ramification. -/
theorem inertia_ne_bot_iff_mem_ramifiedSet (hp : p.Prime) (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Ideal.inertia Gal(K/ℚ) P ≠ ⊥ ↔ p ∈ ramifiedSet K := by
  haveI := Fact.mk hp
  refine ⟨fun h => mem_ramifiedSet_of_inertia_ne_bot P (ne_bot_of_liesOver p P) p hp
    (under_eq_span_of_liesOver P) h, ?_⟩
  rintro ⟨-, Q, ⟨hQprime, hQover⟩, hQe⟩
  haveI := hQprime
  haveI := hQover
  rw [Ne, ← Subgroup.card_eq_one, card_inertia_eq_ramificationIdx_span hp P,
    Ideal.ramificationIdx_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P Q Gal(K/ℚ)]
  exact hQe

/-- **At an unramified prime the inertia subgroup is trivial.** -/
theorem inertia_eq_bot_of_notMem_ramifiedSet (hp : p.Prime) (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (h : p ∉ ramifiedSet K) :
    Ideal.inertia Gal(K/ℚ) P = ⊥ :=
  not_not.mp fun hc => h ((inertia_ne_bot_iff_mem_ramifiedSet hp P).mp hc)

/-- **A prime with nontrivial inertia subgroup is ramified**, stated for a prime lying over `(p)`.
-/
theorem mem_ramifiedSet_of_inertia_ne_bot' (hp : p.Prime) (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (h : Ideal.inertia Gal(K/ℚ) P ≠ ⊥) :
    p ∈ ramifiedSet K :=
  (inertia_ne_bot_iff_mem_ramifiedSet hp P).mp h

end Ramified

section SplitInertia

/-- **The residue degree is one exactly when inertia is the whole decomposition group.**  The
inertia subgroup is contained in the decomposition subgroup, their orders are `e` and `e * f`, and
`e` is positive, so the containment is an equality precisely when `f = 1`. -/
theorem inertiaDeg_eq_one_iff_inertia_eq_stabilizer (hp : p.Prime) (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    (Ideal.span {(p : ℤ)}).inertiaDeg P = 1 ↔
      Ideal.inertia Gal(K/ℚ) P = MulAction.stabilizer Gal(K/ℚ) P := by
  have hle := Ideal.inertia_le_stabilizer (M := Gal(K/ℚ)) P
  have hstab := card_stabilizer_eq_mul K hp P
  have hcard := card_inertia_eq_ramificationIdx_span hp P
  have hepos : 0 < Ideal.ramificationIdx (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) P := by
    rw [← hcard]
    exact Nat.card_pos
  constructor
  · intro hf
    refine eq_of_le_of_card_eq hle ?_
    rw [hcard, hstab, hf, mul_one]
  · intro heq
    have hcards : Nat.card (Ideal.inertia Gal(K/ℚ) P) =
        Nat.card (MulAction.stabilizer Gal(K/ℚ) P) := by rw [heq]
    rw [hcard, hstab] at hcards
    exact Nat.eq_of_mul_eq_mul_left hepos (by rw [← hcards, mul_one])

/-- **Split inertia makes the decomposition group at a ramified prime its inertia group.** -/
theorem inertia_eq_stabilizer_of_isSplitInertia (h : IsSplitInertia K) (hmem : p ∈ ramifiedSet K)
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Ideal.inertia Gal(K/ℚ) P = MulAction.stabilizer Gal(K/ℚ) P :=
  (inertiaDeg_eq_one_iff_inertia_eq_stabilizer hmem.1 P).mp
    (h p hmem P inferInstance inferInstance)

end SplitInertia

section TotallyRamified

/-- **The inertia subgroup has the order of the Galois group exactly when it is everything.** -/
theorem inertia_eq_top_iff_card_eq_finrank (P : Ideal (𝓞 K)) :
    Nat.card (Ideal.inertia Gal(K/ℚ) P) = Module.finrank ℚ K ↔
      Ideal.inertia Gal(K/ℚ) P = ⊤ := by
  rw [← IsGalois.card_aut_eq_finrank ℚ K]
  refine ⟨Subgroup.eq_top_of_card_eq _, fun h => ?_⟩
  rw [h, Subgroup.card_top]

/-- **A prime is totally ramified exactly when its inertia subgroup is the whole Galois group.** -/
theorem inertia_eq_top_iff_ramificationIdx_eq_finrank (hp : p.Prime) (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Ideal.ramificationIdx (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) P = Module.finrank ℚ K ↔
      Ideal.inertia Gal(K/ℚ) P = ⊤ := by
  rw [← card_inertia_eq_ramificationIdx_span hp P, inertia_eq_top_iff_card_eq_finrank]

end TotallyRamified

section Restrict

variable {N : Type*} [Field N] [NumberField N] [IsGalois ℚ N]

omit [IsGalois ℚ N] in
/-- The prime of `𝓞 F` lying under a prime of `𝓞 N` over `(p)` again lies over `(p)`. -/
theorem liesOver_under_intermediateField (F : IntermediateField ℚ N) (P : Ideal (𝓞 N))
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    (P.under (𝓞 ↥F)).LiesOver (Ideal.span {(p : ℤ)}) :=
  ⟨by rw [Ideal.under_under]; exact Ideal.LiesOver.over⟩

omit [IsGalois ℚ N] in
/-- **Restriction sends the inertia subgroup into the inertia subgroup below.**  The image of the
inertia subgroup of `P` under restriction to a normal subextension `F` lies in the inertia subgroup
of the prime of `𝓞 F` under `P`. -/
theorem map_inertia_le_inertia (F : IntermediateField ℚ N) [Normal ℚ ↥F] (P : Ideal (𝓞 N)) :
    (Ideal.inertia Gal(N/ℚ) P).map (AlgEquiv.restrictNormalHom ↥F) ≤
      Ideal.inertia Gal(↥F/ℚ) (P.under (𝓞 ↥F)) := by
  rw [Subgroup.map_le_iff_le_comap]
  exact fun σ hσ => restrictNormal_mem_inertia F P hσ

/-- **Inertia at a prime unramified in a normal subextension acts trivially on it.**  Restriction
to `F` carries the inertia subgroup of `P` into the inertia subgroup of the prime of `𝓞 F` below
`P`, which is trivial because `p` does not ramify in `F`; an automorphism of `N` restricting to the
identity on `F` fixes `F` pointwise. -/
theorem inertia_le_fixingSubgroup (F : IntermediateField ℚ N) [Normal ℚ ↥F] (hp : p.Prime)
    (P : Ideal (𝓞 N)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (hF : p ∉ ramifiedSet ↥F) :
    Ideal.inertia Gal(N/ℚ) P ≤ F.fixingSubgroup := by
  haveI : NumberField ↥F := ⟨⟩
  haveI : IsGalois ℚ ↥F := ⟨⟩
  haveI := liesOver_under_intermediateField (p := p) F P
  intro σ hσ
  refine mem_fixingSubgroup_of_restrictNormal_eq_one ?_
  have hmem := restrictNormal_mem_inertia F P hσ
  rw [inertia_eq_bot_of_notMem_ramifiedSet hp (P.under (𝓞 ↥F)) hF] at hmem
  simpa using hmem

end Restrict

section Cyclotomic

variable {M m : ℕ} {L : Type*} [Field L] [NumberField L] [IsCyclotomicExtension {M} ℚ L]

/-- **The inertia subgroup at a prime exactly dividing the conductor.**  Let `M = p * m` with `p`
prime not dividing `m`, let `L = ℚ(ζ_M)` and let `F` be an intermediate field of `L / ℚ` which is
the cyclotomic field `ℚ(ζ_m)`.  Then the inertia subgroup at any prime of `𝓞 L` above `p` is
exactly the subgroup fixing `F`: the containment holds because `p` is unramified in `F`, and both
subgroups have order `p - 1`, the first because the ramification index of `p` in `ℚ(ζ_M)` is
`φ p`, the second because `[L : F] = φ M / φ m = p - 1`. -/
theorem inertia_eq_fixingSubgroup_of_mul (hp : p.Prime) (hM : M = p * m) (hpm : ¬ p ∣ m)
    (F : IntermediateField ℚ L) [IsCyclotomicExtension {m} ℚ ↥F] (P : Ideal (𝓞 L)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Ideal.inertia Gal(L/ℚ) P = F.fixingSubgroup := by
  haveI := Fact.mk hp
  have hm0 : m ≠ 0 := fun h => hpm (h ▸ dvd_zero p)
  haveI : NeZero m := ⟨hm0⟩
  haveI : NeZero M := ⟨by rw [hM]; exact Nat.mul_ne_zero hp.ne_zero hm0⟩
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm
  haveI : IsGalois ℚ L := IsCyclotomicExtension.isGalois {M} ℚ L
  haveI : NumberField ↥F := ⟨⟩
  haveI : IsGalois ℚ ↥F := IsCyclotomicExtension.isGalois {m} ℚ ↥F
  haveI : IsGalois ↥F L := IsGalois.tower_top_of_isGalois ℚ ↥F L
  haveI := liesOver_under_intermediateField (p := p) F P
  have hbot : Ideal.inertia Gal(↥F/ℚ) (P.under (𝓞 ↥F)) = ⊥ :=
    Subgroup.card_eq_one.mp (card_inertia_eq_one_of_not_dvd m ↥F p (P.under (𝓞 ↥F)) hpm)
  have hF : p ∉ ramifiedSet ↥F := fun hc =>
    (inertia_ne_bot_iff_mem_ramifiedSet hp (P.under (𝓞 ↥F))).mpr hc hbot
  refine eq_of_le_of_card_eq (inertia_le_fixingSubgroup F hp P hF) ?_
  have hfact : M.factorization p = 1 := by
    rw [hM, Nat.factorization_mul hp.ne_zero hm0]
    simp [hp.factorization, Nat.factorization_eq_zero_of_not_dvd hpm]
  have hI : Nat.card (Ideal.inertia Gal(L/ℚ) P) = p - 1 := by
    rw [card_inertia_eq_totient M L p P, hfact, pow_one, Nat.totient_prime hp]
  have hdeg : Module.finrank ℚ ↥F * Module.finrank ↥F L = Module.finrank ℚ L :=
    Module.finrank_mul_finrank ℚ ↥F L
  rw [finrank_cyclotomic m ↥F, finrank_cyclotomic M L, hM, Nat.totient_mul hcop,
    Nat.totient_prime hp] at hdeg
  have hmpos : 0 < m.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hFL : Module.finrank ↥F L = p - 1 :=
    Nat.eq_of_mul_eq_mul_left hmpos (by rw [hdeg]; ring)
  rw [hI, Nat.card_congr (IntermediateField.fixingSubgroupEquiv F).toEquiv,
    IsGalois.card_aut_eq_finrank ↥F L, hFL]

/-- **The inertia subgroup at a prime divisor of a squarefree conductor.**  For `M` squarefree and
`p` a prime dividing `M`, the inertia subgroup of `Gal(ℚ(ζ_M)/ℚ)` at a prime above `p` is the
subgroup fixing the intermediate field `ℚ(ζ_{M / p})`. -/
theorem inertia_eq_fixingSubgroup_of_squarefree (hM : Squarefree M) (hp : p.Prime) (hpM : p ∣ M)
    (F : IntermediateField ℚ L) [IsCyclotomicExtension {M / p} ℚ ↥F] (P : Ideal (𝓞 L)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Ideal.inertia Gal(L/ℚ) P = F.fixingSubgroup := by
  refine inertia_eq_fixingSubgroup_of_mul hp (Nat.mul_div_cancel' hpM).symm (fun hdvd => ?_) F P
  obtain ⟨c, hc⟩ := hdvd
  refine hp.not_isUnit (hM p ⟨c, ?_⟩)
  rw [← Nat.mul_div_cancel' hpM, hc]
  ring

end Cyclotomic

end InverseGalois.CFT

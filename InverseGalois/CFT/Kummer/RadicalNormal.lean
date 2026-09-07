import Mathlib
import InverseGalois.CFT.Kummer.AmbientRadical

/-!
# Radicals of a power basis inside an ambient field

Fix a field `k`, an ambient normal extension `A` of `k`, and an intermediate field `Ω` of `A / k`
which is itself normal over `k` and contains a primitive `p`-th root of unity.  Given a power basis
`g_1, …, g_s` of a subgroup `B` of `Ω^×` modulo `p`-th powers and a choice `w_i` of a `p`-th root of
`g_i` inside `A`, the field `Ω(w_1, …, w_s)` is the natural home for the Kummer theory of `B`.

Two things are proved about it.  First, it contains a `p`-th root of *every* element of `B`, not
just of the chosen basis: the presentation `b = ∏ g_i^{m_i} z^p` of an element of `B` exhibits
`∏ w_i^{m_i} z` as such a root.  Secondly — and this is what makes the field usable as the top of a
tower over `k` — the field is normal over `k` as soon as `B` is carried into itself by every
`k`-embedding of the ambient field.  Indeed a conjugate `τ(w_i)` is a `p`-th root of the element
`τ(g_i)` of `B`, which already has a root `v` inside the field, so `τ(w_i)/v` is a `p`-th root of
unity and therefore lies in `Ω`.

## Main definitions

* `IsEmbeddingStable`: a subgroup of `Ω^×` carried into itself by every `k`-embedding of `A`.
* `ambientRadField`: the subfield `Ω(w_1, …, w_s)` of `A`.

## Main results

* `exists_mem_pow_eq_ambientRadField`: every element of `B` has a `p`-th root in `Ω(w_1, …, w_s)`.
* `map_mem_ambientRadField`: the conjugates of the chosen radicals stay inside the field.
* `normal_ambientRadField`: **the field is normal over `k`.**
* `normal_ambientRadField_base`, `finiteDimensional_ambientRadField`: it is finite and normal
  over `Ω`.
* `exists_aut_fix_iff_ambientRadField`: a character of a subgroup of `B`, trivial on the `p`-th
  powers it contains, is realised by an automorphism over `Ω`.

## Tags

Kummer theory, radical extension, normal extension
-/

namespace InverseGalois.CFT

section AmbientRadField

variable {k A : Type*} [Field k] [Field A] [Algebra k A]

/-- A subgroup of the unit group of an intermediate field is *embedding stable* when every
`k`-embedding of the ambient field carries it into itself. -/
def IsEmbeddingStable (Ω : IntermediateField k A) (B : Subgroup (↥Ω)ˣ) : Prop :=
  ∀ (τ : A →ₐ[k] A) (b : (↥Ω)ˣ), b ∈ B →
    ∃ c : (↥Ω)ˣ, c ∈ B ∧ τ (algebraMap ↥Ω A (b : ↥Ω)) = algebraMap ↥Ω A (c : ↥Ω)

/-- The subfield of the ambient field generated over an intermediate field by a chosen system of
radicals. -/
abbrev ambientRadField (Ω : IntermediateField k A) {ι : Type*} (w : ι → A) :
    IntermediateField ↥Ω A :=
  IntermediateField.adjoin ↥Ω (Set.range w)

/-- Each chosen radical lies in the field it generates. -/
theorem mem_ambientRadField (Ω : IntermediateField k A) {ι : Type*} (w : ι → A) (i : ι) :
    w i ∈ ambientRadField Ω w :=
  IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩

variable {Ω : IntermediateField k A} {p s : ℕ} {B : Subgroup (↥Ω)ˣ}

/-- **A `p`-th root of unity of the ambient field lies in the radical field**, because the base
intermediate field already contains a primitive one. -/
theorem mem_ambientRadField_of_pow_eq_one [NeZero p] {ζ : ↥Ω} (hζ : IsPrimitiveRoot ζ p)
    {ι : Type*} (w : ι → A) {x : A} (hx : x ^ p = 1) : x ∈ ambientRadField Ω w := by
  obtain ⟨i, -, rfl⟩ :=
    (hζ.map_of_injective (algebraMap ↥Ω A).injective).eq_pow_of_pow_eq_one hx
  exact pow_mem ((ambientRadField Ω w).algebraMap_mem ζ) i

/-- **Every element of the subgroup has a `p`-th root in the radical field.** -/
theorem exists_mem_pow_eq_ambientRadField (P : PowBasis B p s) {ζ : ↥Ω}
    (hζ : IsPrimitiveRoot ζ p) (w : Fin s → A) (hw : ∀ i, w i ^ p = algebraMap ↥Ω A (P.rad i))
    {b : (↥Ω)ˣ} (hb : b ∈ B) :
    ∃ v ∈ ambientRadField Ω w, v ^ p = algebraMap ↥Ω A (b : ↥Ω) := by
  obtain ⟨v, hv⟩ :=
    P.exists_root_ambient hζ w hw (ambientRadField Ω w) (mem_ambientRadField Ω w) rfl hb
  refine ⟨(v : A), v.2, ?_⟩
  simpa using congrArg (fun x : ↥(ambientRadField Ω w) => (x : A)) hv

variable [Normal k A]

omit [Normal k A] in
/-- **The conjugates of the chosen radicals stay inside the radical field.**  A conjugate of a
radical is a `p`-th root of an element of the subgroup, hence differs from a radical of that
element by a root of unity. -/
theorem map_mem_ambientRadField (P : PowBasis B p s) (hp : p.Prime) {ζ : ↥Ω}
    (hζ : IsPrimitiveRoot ζ p) (w : Fin s → A) (hw : ∀ i, w i ^ p = algebraMap ↥Ω A (P.rad i))
    (hstab : IsEmbeddingStable Ω B) (τ : A →ₐ[k] A) (i : Fin s) :
    τ (w i) ∈ ambientRadField Ω w := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨c, hc, hτ⟩ := hstab τ (P.g i) (P.mem i)
  have hτ' : τ (algebraMap ↥Ω A (P.rad i)) = algebraMap ↥Ω A (c : ↥Ω) := hτ
  obtain ⟨v, hvmem, hv⟩ := exists_mem_pow_eq_ambientRadField P hζ w hw hc
  have hcne : algebraMap ↥Ω A (c : ↥Ω) ≠ 0 := fun h =>
    Units.ne_zero c ((algebraMap ↥Ω A).injective (by rw [h, map_zero]))
  have hvne : v ≠ 0 := fun h => hcne (by rw [← hv, h, zero_pow hp.ne_zero])
  have hpow : τ (w i) ^ p = algebraMap ↥Ω A (c : ↥Ω) := by
    rw [← map_pow, hw i]
    exact hτ'
  have hone : (τ (w i) / v) ^ p = 1 := by rw [div_pow, hpow, hv, div_self hcne]
  have hsplit : τ (w i) = τ (w i) / v * v := (div_mul_cancel₀ _ hvne).symm
  rw [hsplit]
  exact mul_mem (mem_ambientRadField_of_pow_eq_one hζ w hone) hvmem

/-- **The radical field is normal over the base field.**  It is generated over the base by the
intermediate field, which is normal, together with the radicals, whose conjugates it contains. -/
theorem normal_ambientRadField [Normal k ↥Ω] (P : PowBasis B p s) (hp : p.Prime) {ζ : ↥Ω}
    (hζ : IsPrimitiveRoot ζ p) (w : Fin s → A) (hw : ∀ i, w i ^ p = algebraMap ↥Ω A (P.rad i))
    (hstab : IsEmbeddingStable Ω B) : Normal k ↥(ambientRadField Ω w) := by
  refine (IntermediateField.restrictScalars_normal (F := k)).mp ?_
  refine IntermediateField.normal_iff_forall_map_le.2 fun τ => ?_
  rw [IntermediateField.map_le_iff_le_comap]
  refine (IntermediateField.restrictScalars_adjoin_eq_sup k Ω (Set.range w)).trans_le ?_
  refine sup_le (fun x hx => ?_) (IntermediateField.adjoin_le_iff.2 ?_)
  · show τ x ∈ ambientRadField Ω w
    have hxΩ : τ x ∈ Ω :=
      IntermediateField.normal_iff_forall_map_le.1 ‹Normal k ↥Ω› τ ⟨x, hx, rfl⟩
    exact (ambientRadField Ω w).algebraMap_mem ⟨τ x, hxΩ⟩
  · rintro _ ⟨i, rfl⟩
    show τ (w i) ∈ ambientRadField Ω w
    exact map_mem_ambientRadField P hp hζ w hw hstab τ i

end AmbientRadField

section Base

variable {k A : Type*} [Field k] [Field A] [Algebra k A] {Ω : IntermediateField k A}
  [CharZero ↥Ω] {p s : ℕ} {B : Subgroup (↥Ω)ˣ}

/-- The radical field is finite over the intermediate field it is built on. -/
theorem finiteDimensional_ambientRadField [NeZero p] (P : PowBasis B p s) {ζ : ↥Ω}
    (hζ : IsPrimitiveRoot ζ p) (w : Fin s → A) (hw : ∀ i, w i ^ p = algebraMap ↥Ω A (P.rad i)) :
    FiniteDimensional ↥Ω ↥(ambientRadField Ω w) :=
  P.finiteDimensional_ambient hζ w hw _ (mem_ambientRadField Ω w) rfl

/-- The radical field is normal over the intermediate field it is built on, being a splitting
field of a product of binomials. -/
theorem normal_ambientRadField_base [NeZero p] (P : PowBasis B p s) {ζ : ↥Ω}
    (hζ : IsPrimitiveRoot ζ p) (w : Fin s → A) (hw : ∀ i, w i ^ p = algebraMap ↥Ω A (P.rad i)) :
    Normal ↥Ω ↥(ambientRadField Ω w) :=
  (P.setupOfRoots hζ w hw _ (mem_ambientRadField Ω w) rfl).normal

/-- The radical field is Galois over the intermediate field it is built on. -/
theorem isGalois_ambientRadField [NeZero p] (P : PowBasis B p s) {ζ : ↥Ω}
    (hζ : IsPrimitiveRoot ζ p) (w : Fin s → A) (hw : ∀ i, w i ^ p = algebraMap ↥Ω A (P.rad i)) :
    IsGalois ↥Ω ↥(ambientRadField Ω w) :=
  (P.setupOfRoots hζ w hw _ (mem_ambientRadField Ω w) rfl).isGalois

/-- **A character of a subgroup of the subgroup, trivial on the `p`-th powers it contains, is
realised by an automorphism of the radical field over the intermediate field it is built on.** -/
theorem exists_aut_fix_iff_ambientRadField (P : PowBasis B p s) (hp : p.Prime) {ζ : ↥Ω}
    (hζ : IsPrimitiveRoot ζ p) (hfin : Finite (powQuotient B p))
    (hsat : ∀ y : (↥Ω)ˣ, y ^ p ∈ B → y ∈ B) (w : Fin s → A)
    (hw : ∀ i, w i ^ p = algebraMap ↥Ω A (P.rad i)) {U : Subgroup (↥Ω)ˣ} (hU : U ≤ B)
    (Φ : ↥U →* (↥Ω)ˣ)
    (hΦ : ∀ (u : (↥Ω)ˣ) (hu : u ∈ U) (y : (↥Ω)ˣ), u = y ^ p → Φ ⟨u, hu⟩ = 1) :
    ∃ σ : ↥(ambientRadField Ω w) ≃ₐ[↥Ω] ↥(ambientRadField Ω w),
      ∀ (u : (↥Ω)ˣ) (hu : u ∈ U) (v : ↥(ambientRadField Ω w)),
        v ^ p = algebraMap ↥Ω ↥(ambientRadField Ω w) (u : ↥Ω) →
          (σ v = v ↔ Φ ⟨u, hu⟩ = 1) :=
  P.exists_aut_fix_iff_ambient hp hζ hfin hsat w hw _ (mem_ambientRadField Ω w) rfl hU Φ hΦ

end Base

end InverseGalois.CFT

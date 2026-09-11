/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.CorestrictionInertia

/-!
# The trace of an equivariant homomorphism over the cosets of a subgroup

A homomorphism of a normal subgroup into a module over the whole group is equivariant when
conjugating the argument by a group element moves the value by that same element.  Equivariance for
the whole group is what a cocycle of the whole group restricts to along a normal subgroup acting
trivially, so it is what has to be produced.  Equivariance for a subgroup is cheaper, and the two
are related by a trace: the product, over the cosets of the subgroup, of the values of the
homomorphism at the conjugates of the argument by the chosen representatives, each carried back by
that representative.

The trace of a homomorphism equivariant for the subgroup is equivariant for the whole group.  The
cosets are permuted by the group; the discrepancy between a representative moved by a group element
and the representative of the moved coset lies in the subgroup, and equivariance there absorbs it
exactly.

Nothing is lost to a norm along the subgroup, and that is the point of tracing over the cosets
rather than over the whole group.  A trace over the whole group repeats, at an element the subgroup
fixes, one and the same value as many times as the subgroup has elements, and such a power can be
trivial; the trace over the cosets contributes that value once.

Equivariance is cheaper still than it looks: a homomorphism of the kernel of the homomorphism the
coefficients are acted on through does not see conjugation by the kernel, so equivariance for a
subgroup is already equivariance for the saturation of that subgroup, the elements whose image is
the image of a member of it.  The saturation contains the kernel, so it has finite index whenever
the image is finite — which is what makes the cosets it is traced over a finite family.

At a point whose stabiliser lies inside the subgroup the trace reproduces the homomorphism, provided
the homomorphism kills the stabilisers of the points the elements outside the subgroup carry it to
and the coset of the identity is represented by the identity.  Where the trace is nontrivial the
homomorphism is nontrivial at a conjugate, which confines the ramification of the trace to the orbit
of the ramification of the homomorphism; and a homomorphism killing a normal subgroup traces to one
killing it as well.

## Main definitions

* `InverseGalois.CFT.conjHom`: conjugation by a group element, as an endomorphism of a normal
  subgroup.
* `InverseGalois.CFT.conjTraceHom`: **the trace of a homomorphism of a normal subgroup over the
  cosets of a subgroup.**
* `InverseGalois.CFT.saturate`: the saturation of a subgroup along a homomorphism, the elements
  whose image is the image of a member of the subgroup.

## Main results

* `InverseGalois.CFT.exists_section_coe_one`: a section of the projection onto the cosets of an
  arbitrary subgroup may be chosen to send the coset of the identity to the identity.
* `InverseGalois.CFT.conjTraceHom_conj`: **the trace of a homomorphism equivariant for the subgroup
  is equivariant for the whole group.**
* `InverseGalois.CFT.apply_conjHom_of_mem_saturate`: **equivariance for a subgroup lifts to
  equivariance for its saturation.**
* `InverseGalois.CFT.conjTraceHom_eq_self_of_stabilizer_le`: **at a point whose stabiliser lies
  inside the subgroup the trace reproduces the homomorphism.**
* `InverseGalois.CFT.exists_mem_inertia_section_of_conjTraceHom_ne_one`: **where the trace ramifies
  the homomorphism ramifies at a prime of the same orbit.**

## Tags

class field theory, transfer, equivariant homomorphism, decomposition group, ramification
-/

namespace InverseGalois.CFT

open MulAction

open scoped Pointwise

/-! ### A section sending the coset of the identity to the identity -/

section Section

variable {G : Type*} [Group G] (H : Subgroup G)

/-- **A section of the projection onto the cosets of an arbitrary subgroup may be chosen to send the
coset of the identity to the identity**: correct an arbitrary section at that one coset. -/
theorem exists_section_coe_one :
    ∃ s : G ⧸ H → G, (∀ x : G ⧸ H, (s x : G ⧸ H) = x) ∧ s ((1 : G) : G ⧸ H) = 1 := by
  classical
  refine ⟨Function.update (fun x : G ⧸ H => x.out) ((1 : G) : G ⧸ H) 1, fun x => ?_, ?_⟩
  · by_cases hx : x = ((1 : G) : G ⧸ H)
    · subst hx
      rw [Function.update_self]
    · rw [Function.update_of_ne hx]
      exact QuotientGroup.out_eq' x
  · rw [Function.update_self]

/-- **The representative of a coset other than the coset of the identity lies outside the
subgroup.** -/
theorem section_notMem_of_ne_coe_one {σ : G ⧸ H → G} (hσ : ∀ x : G ⧸ H, (σ x : G ⧸ H) = x)
    {x : G ⧸ H} (hx : x ≠ ((1 : G) : G ⧸ H)) : σ x ∉ H := fun h =>
  hx ((hσ x).symm.trans (QuotientGroup.eq.2 (by simpa using H.inv_mem h)))

end Section

/-! ### Conjugation inside a normal subgroup -/

section Conj

variable {G : Type*} [Group G] (K : Subgroup G) [K.Normal]

/-- **Conjugation by a group element, as an endomorphism of a normal subgroup.** -/
def conjHom (g : G) : ↥K →* ↥K := (MulAut.conjNormal g).toMonoidHom

/-- Conjugation inside a normal subgroup, read in the whole group. -/
theorem coe_conjHom (g : G) (y : ↥K) : (conjHom K g y : G) = g * (y : G) * g⁻¹ := rfl

/-- Conjugating twice is conjugating by the product. -/
theorem conjHom_conjHom (a b : G) (y : ↥K) : conjHom K a (conjHom K b y) = conjHom K (a * b) y :=
  Subtype.ext (by
    show a * (b * (y : G) * b⁻¹) * a⁻¹ = a * b * (y : G) * (a * b)⁻¹
    group)

/-- Conjugating by the identity changes nothing. -/
theorem conjHom_one (y : ↥K) : conjHom K 1 y = y :=
  Subtype.ext (by
    show (1 : G) * (y : G) * (1 : G)⁻¹ = (y : G)
    group)

/-- Conjugation by a member of the normal subgroup, read inside the subgroup. -/
theorem conjHom_of_mem {z : G} (hz : z ∈ K) (y : ↥K) :
    conjHom K z y = ⟨z, hz⟩ * y * ⟨z, hz⟩⁻¹ := Subtype.ext rfl

/-- **A homomorphism into an abelian group does not see conjugation by a member of the normal
subgroup itself**, such a conjugation being inner there. -/
theorem apply_conjHom_of_mem {M : Type*} [CommGroup M] (u : ↥K →* M) {z : G} (hz : z ∈ K)
    (y : ↥K) : u (conjHom K z y) = u y := by
  rw [conjHom_of_mem K hz, _root_.map_mul, _root_.map_mul, _root_.map_inv,
    mul_comm (u ⟨z, hz⟩) (u y), mul_assoc, mul_inv_cancel, mul_one]

end Conj

/-! ### The saturation of a subgroup along a homomorphism -/

section Saturate

variable {G : Type*} [Group G] {U : Type*} [Group U] (φ : G →* U) (H : Subgroup G)

/-- **The saturation of a subgroup along a homomorphism**: the elements whose image is the image of
a member of the subgroup. -/
def saturate : Subgroup G := Subgroup.comap φ (Subgroup.map φ H)

/-- Membership in the saturation is membership of the image. -/
theorem mem_saturate_iff {g : G} : g ∈ saturate φ H ↔ ∃ h ∈ H, φ h = φ g := Subgroup.mem_map

/-- A subgroup lies inside its saturation. -/
theorem le_saturate : H ≤ saturate φ H := fun h hh => (mem_saturate_iff φ H).2 ⟨h, hh, rfl⟩

/-- The kernel lies inside every saturation. -/
theorem ker_le_saturate : φ.ker ≤ saturate φ H := fun g hg =>
  (mem_saturate_iff φ H).2 ⟨1, one_mem _, by rw [_root_.map_one, MonoidHom.mem_ker.1 hg]⟩

/-- **Equivariance for a subgroup lifts to equivariance for its saturation.**

An element of the saturation is an element of the subgroup corrected by a member of the kernel, and
a homomorphism of a normal subgroup containing the kernel into an abelian group does not see
conjugation by such a correction. -/
theorem apply_conjHom_of_mem_saturate {K : Subgroup G} [K.Normal] (hK : φ.ker ≤ K) {M : Type*}
    [CommGroup M] [MulDistribMulAction U M] {u : ↥K →* M}
    (hu : ∀ h ∈ H, ∀ y : ↥K, u (conjHom K h y) = φ h • u y) {g : G} (hg : g ∈ saturate φ H)
    (y : ↥K) : u (conjHom K g y) = φ g • u y := by
  obtain ⟨h, hh, hφ⟩ := (mem_saturate_iff φ H).1 hg
  have hz : g * h⁻¹ ∈ K :=
    hK (by rw [MonoidHom.mem_ker, _root_.map_mul, _root_.map_inv, hφ, mul_inv_cancel])
  have hsplit : conjHom K g y = conjHom K (g * h⁻¹) (conjHom K h y) := by
    rw [conjHom_conjHom]
    congr 1
    group
  rw [hsplit, apply_conjHom_of_mem K u hz, hu h hh y, hφ]

end Saturate

/-! ### The trace over the cosets -/

section Trace

variable {G : Type*} [Group G] (K : Subgroup G) [K.Normal] (H : Subgroup G) (σ : G ⧸ H → G)
  {U : Type*} [Group U] (φ : G →* U) {M : Type*} [CommGroup M] [MulDistribMulAction U M]

/-- **The trace of a homomorphism of a normal subgroup over the cosets of a subgroup**: the product
over the cosets of its values at the conjugates of the argument by the inverses of the chosen
representatives, each carried back by that representative. -/
def conjTraceHom [Fintype (G ⧸ H)] (u : ↥K →* M) : ↥K →* M :=
  MonoidHom.mk' (fun y => ∏ x : G ⧸ H, φ (σ x) • u (conjHom K (σ x)⁻¹ y)) fun a b => by
    show ∏ x : G ⧸ H, φ (σ x) • u (conjHom K (σ x)⁻¹ (a * b))
      = (∏ x : G ⧸ H, φ (σ x) • u (conjHom K (σ x)⁻¹ a))
        * ∏ x : G ⧸ H, φ (σ x) • u (conjHom K (σ x)⁻¹ b)
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun x _ => by
      rw [_root_.map_mul (conjHom K (σ x)⁻¹), _root_.map_mul u, smul_mul']

/-- The trace, read at an element of the normal subgroup. -/
theorem conjTraceHom_apply [Fintype (G ⧸ H)] (u : ↥K →* M) (y : ↥K) :
    conjTraceHom K H σ φ u y = ∏ x : G ⧸ H, φ (σ x) • u (conjHom K (σ x)⁻¹ y) := rfl

/-- **The trace of a homomorphism equivariant for the subgroup is equivariant for the whole
group.**

Conjugating the argument by a group element permutes the cosets, and the chosen representative of a
moved coset differs from the moved representative by an element of the subgroup.  Equivariance for
the subgroup turns that discrepancy into the very factor which, absorbed into the representative,
rebuilds the term of the trace at the moved coset — leaving the group element in front of the whole
product. -/
theorem conjTraceHom_conj [Fintype (G ⧸ H)] (hσ : ∀ x : G ⧸ H, (σ x : G ⧸ H) = x) {u : ↥K →* M}
    (hu : ∀ h ∈ H, ∀ y : ↥K, u (conjHom K h y) = φ h • u y) (g : G) (y : ↥K) :
    conjTraceHom K H σ φ u (conjHom K g y) = φ g • conjTraceHom K H σ φ u y := by
  rw [conjTraceHom_apply, conjTraceHom_apply, Finset.smul_prod']
  refine (Fintype.prod_equiv (MulAction.toPerm g)
    (fun x => φ g • φ (σ x) • u (conjHom K (σ x)⁻¹ y))
    (fun x => φ (σ x) • u (conjHom K (σ x)⁻¹ (conjHom K g y))) fun x => ?_).symm
  have he : ((transversalElt H σ hσ g x : ↥H) : G) = (σ (g • x))⁻¹ * g * σ x :=
    coe_transversalElt H σ hσ g x
  have hkey : conjHom K (σ (g • x))⁻¹ (conjHom K g y)
      = conjHom K ((transversalElt H σ hσ g x : ↥H) : G) (conjHom K (σ x)⁻¹ y) := by
    simp only [conjHom_conjHom]
    congr 1
    rw [he]
    group
  show φ g • φ (σ x) • u (conjHom K (σ x)⁻¹ y)
    = φ (σ (g • x)) • u (conjHom K (σ (g • x))⁻¹ (conjHom K g y))
  rw [hkey, hu _ (transversalElt H σ hσ g x).2, smul_smul, smul_smul, ← _root_.map_mul φ,
    ← _root_.map_mul φ, mul_coe_transversalElt]

/-- **A homomorphism killing a normal subgroup traces to one killing it as well**, the conjugates of
a member of a normal subgroup staying inside it. -/
theorem conjTraceHom_eq_one_of_mem_normal [Fintype (G ⧸ H)] {u : ↥K →* M} {V : Subgroup G}
    (hV : V.Normal) (hu : ∀ y : ↥K, (y : G) ∈ V → u y = 1) {y : ↥K} (hy : (y : G) ∈ V) :
    conjTraceHom K H σ φ u y = 1 := by
  rw [conjTraceHom_apply]
  refine Finset.prod_eq_one fun x _ => ?_
  rw [hu _ (by rw [coe_conjHom]; exact hV.conj_mem _ hy _), smul_one]

/-- **The trace kills an element all of whose conjugates lie inside a subgroup the homomorphism is
asked about at every conjugate.** -/
theorem conjTraceHom_eq_one_of_forall_conj [Fintype (G ⧸ H)] {u : ↥K →* M} {D : Subgroup G}
    (hu : ∀ (ρ : G) (y : ↥K), ρ * (y : G) * ρ⁻¹ ∈ D → u y = 1) {y : ↥K} (hy : (y : G) ∈ D) :
    conjTraceHom K H σ φ u y = 1 := by
  rw [conjTraceHom_apply]
  refine Finset.prod_eq_one fun x _ => ?_
  refine (congrArg _ (hu (σ x) _ ?_)).trans (smul_one _)
  rw [show σ x * ((conjHom K (σ x)⁻¹ y : ↥K) : G) * (σ x)⁻¹ = (y : G) from by
    rw [coe_conjHom]; group]
  exact hy

/-- **At a point whose stabiliser lies inside the subgroup the trace reproduces the
homomorphism.**

The representatives of the other cosets lie outside the subgroup, so they move the point, and the
homomorphism was asked to kill the stabilisers of the points they move it to; the coset of the
identity being represented by the identity, the surviving term is the value of the homomorphism
itself. -/
theorem conjTraceHom_eq_self_of_stabilizer_le [Fintype (G ⧸ H)]
    (hσ : ∀ x : G ⧸ H, (σ x : G ⧸ H) = x) (hσ1 : σ ((1 : G) : G ⧸ H) = 1) {u : ↥K →* M}
    {α : Type*} [MulAction G α] {P : α}
    (hvan : ∀ ρ : G, ρ ∉ H → ∀ y : ↥K, (y : G) ∈ stabilizer G (ρ • P) → u y = 1)
    {y : ↥K} (hy : (y : G) ∈ stabilizer G P) :
    conjTraceHom K H σ φ u y = u y := by
  classical
  have hsingle : ∏ x : G ⧸ H, φ (σ x) • u (conjHom K (σ x)⁻¹ y)
      = φ (σ ((1 : G) : G ⧸ H)) • u (conjHom K (σ ((1 : G) : G ⧸ H))⁻¹ y) := by
    refine Finset.prod_eq_single _ (fun x _ hx => ?_) fun h => absurd (Finset.mem_univ _) h
    have hinv : (σ x)⁻¹ ∉ H := fun hc =>
      section_notMem_of_ne_coe_one H hσ hx ((Subgroup.inv_mem_iff H).1 hc)
    refine (congrArg _ (hvan (σ x)⁻¹ hinv _ ?_)).trans (smul_one _)
    refine mem_stabilizer_smul_iff.2 ?_
    rw [show ((σ x)⁻¹)⁻¹ * ((conjHom K (σ x)⁻¹ y : ↥K) : G) * (σ x)⁻¹ = (y : G) from by
      rw [coe_conjHom]; group]
    exact hy
  rw [conjTraceHom_apply, hsingle, hσ1, inv_one, _root_.map_one φ, one_smul, conjHom_one]

/-- **Where the trace is nontrivial the homomorphism is nontrivial at a conjugate.** -/
theorem exists_ne_one_of_conjTraceHom_ne_one [Fintype (G ⧸ H)] {u : ↥K →* M} {y : ↥K}
    (h : conjTraceHom K H σ φ u y ≠ 1) : ∃ x : G ⧸ H, u (conjHom K (σ x)⁻¹ y) ≠ 1 := by
  by_contra hc
  push_neg at hc
  refine h ?_
  rw [conjTraceHom_apply]
  exact Finset.prod_eq_one fun x _ => by rw [hc x, smul_one]

/-- **Where the trace ramifies the homomorphism ramifies at a prime of the same orbit**, and the
representative carrying the given prime there is recorded. -/
theorem exists_mem_inertia_section_of_conjTraceHom_ne_one [Fintype (G ⧸ H)] {R : Type*}
    [CommRing R] [MulSemiringAction G R] {u : ↥K →* M} {P : Ideal R} {y : ↥K}
    (hyI : (y : G) ∈ Ideal.inertia G P) (h : conjTraceHom K H σ φ u y ≠ 1) :
    ∃ x : G ⧸ H, ((conjHom K (σ x)⁻¹ y : ↥K) : G) ∈ Ideal.inertia G ((σ x)⁻¹ • P)
      ∧ u (conjHom K (σ x)⁻¹ y) ≠ 1 := by
  obtain ⟨x, hx⟩ := exists_ne_one_of_conjTraceHom_ne_one K H σ φ h
  refine ⟨x, mem_inertia_smul_iff.2 ?_, hx⟩
  rw [show ((σ x)⁻¹)⁻¹ * ((conjHom K (σ x)⁻¹ y : ↥K) : G) * (σ x)⁻¹ = (y : G) from by
    rw [coe_conjHom]; group]
  exact hyI

end Trace

end InverseGalois.CFT

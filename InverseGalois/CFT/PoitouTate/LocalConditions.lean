/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.Isotropic

/-!
# Prescribing values against a set of local conditions

A perfect self-pairing of a finite abelian group has two orthogonal complements, one taken on
each side of the pairing.  They agree on a subgroup which is already known to be its own
complement on one side, because the pairing obtained by exchanging the two arguments is again
perfect and the subgroup is again isotropic for it.  So a maximal isotropic subgroup needs no
symmetry of the pairing to be recognised from either side.

The interest of the two-sided statement is the following counting theorem.  Let `V` be a maximal
isotropic subgroup and let `L` be an arbitrary subgroup, thought of as a set of conditions imposed
one factor at a time.  Then

  the elements pairing trivially with `V ⊓ L^⊥` are exactly the elements of `V ⊔ L`,

where `L^⊥` is the complement of `L` taken on the left.  One inclusion is immediate: an element of
`V` kills `V` and an element of `L` kills `L^⊥`.  The other is a count.  Pairing against `L`
identifies `V` modulo `V ⊓ L^⊥` with a group of characters of `L` which kill `V ⊓ L`, so `V` has at
most as many elements as `V ⊓ L^⊥` times the index of `V ⊓ L` in `L`; the maximal isotropy of `V`
turns that inequality into the reverse of the one wanted, and the second isomorphism theorem
rewrites the index of `V ⊓ L` in `L` as the index of `V` in `V ⊔ L`.

This is the linear algebra behind the existence of global classes with prescribed local behaviour.
Take for `V` the image of the global classes in the product of the local ones, which is its own
orthogonal complement, and for `L` a set of local conditions.  The theorem says that an element of
the product of the local groups is congruent modulo the conditions to a global class exactly when
it pairs trivially with the global classes satisfying the dual conditions.  That is the exactness
of the Poitou-Tate sequence in the only place where it is used to build extensions of number
fields.

A set of conditions imposed one factor at a time has its orthogonal complement computed one factor
at a time, since the pairing on a product is the product of the pairings.

## Main results

* `InverseGalois.CFT.injective_of_injective_flip`: a self-pairing of a finite abelian group which
  is nondegenerate in one argument is nondegenerate in the other.
* `InverseGalois.CFT.perpSubgroupLeft_eq_self`: **a subgroup which is its own orthogonal
  complement on the right is its own orthogonal complement on the left.**
* `InverseGalois.CFT.perpSubgroup_inf_perpSubgroupLeft`: **the elements pairing trivially with the
  part of a maximal isotropic subgroup dual to a set of conditions are exactly the elements
  congruent to that subgroup modulo the conditions.**
* `InverseGalois.CFT.exists_mul_eq_of_forall_pairing_eq_one`: the same statement as an existence
  theorem for an element of the subgroup differing from a given element by a condition.
* `InverseGalois.CFT.perpSubgroup_piPairing_pi`, `InverseGalois.CFT.perpSubgroupLeft_piPairing_pi`:
  the orthogonal complement of a product of subgroups is the product of the orthogonal
  complements.

## Tags

perfect pairing, orthogonal complement, maximal isotropic, local conditions, Selmer group,
Poitou-Tate duality, class field theory
-/

namespace InverseGalois.CFT

/-! ### The orthogonal complement on the left -/

section Left

variable {A M : Type*} [CommGroup A] [CommGroup M]

/-- The elements of a group pairing trivially with a subgroup when placed in the first argument of
a self-pairing. -/
def perpSubgroupLeft (φ : A →* A →* M) (V : Subgroup A) : Subgroup A :=
  perpSubgroup φ.flip V

@[simp]
theorem mem_perpSubgroupLeft {φ : A →* A →* M} {V : Subgroup A} {b : A} :
    b ∈ perpSubgroupLeft φ V ↔ ∀ a ∈ V, φ b a = 1 := Iff.rfl

/-- Exchanging the two arguments of a pairing twice returns the pairing. -/
theorem flip_flip_pairing (φ : A →* A →* M) : φ.flip.flip = φ := rfl

@[simp]
theorem perpSubgroup_bot (φ : A →* A →* M) : perpSubgroup φ ⊥ = ⊤ :=
  eq_top_iff.2 fun b _ => mem_perpSubgroup.2 fun a ha => by
    rw [Subgroup.mem_bot.1 ha, _root_.map_one, MonoidHom.one_apply]

@[simp]
theorem perpSubgroupLeft_bot (φ : A →* A →* M) : perpSubgroupLeft φ ⊥ = ⊤ :=
  perpSubgroup_bot φ.flip

end Left

/-! ### Nondegeneracy on both sides -/

section Nondegenerate

variable {A : Type*} [CommGroup A] [Finite A]

/-- **A self-pairing of a finite abelian group which is nondegenerate in one argument is
nondegenerate in the other**: every character is a pairing against some element, so every character
kills the elements pairing trivially with everything, and only the unit is killed by every
character. -/
theorem injective_of_injective_flip {φ : A →* A →* Multiplicative QModZ}
    (hφ : Function.Injective φ.flip) : Function.Injective φ := by
  haveI := finite_monoidHom_qModZ (A := A)
  rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.card_eq_one]
  have htop : dualAnnihilator (M := Multiplicative QModZ) φ.ker = ⊤ :=
    eq_top_iff.2 fun f _ => mem_dualAnnihilator.2 fun a ha => by
      obtain ⟨b, rfl⟩ := surjective_flip hφ f
      rw [MonoidHom.flip_apply, MonoidHom.mem_ker.1 ha, MonoidHom.one_apply]
  have hcard := card_dualAnnihilator φ.ker
  rw [htop, Subgroup.card_top, card_monoidHom_qModZ] at hcard
  have h2 := Subgroup.card_mul_index φ.ker
  rw [← hcard] at h2
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h2.trans (one_mul _).symm)

/-- **A subgroup which is its own orthogonal complement on the right is its own orthogonal
complement on the left.**  No symmetry of the pairing is needed: the pairing with its arguments
exchanged is again perfect, and the subgroup is again isotropic for it. -/
theorem perpSubgroupLeft_eq_self {φ : A →* A →* Multiplicative QModZ}
    (hφ : Function.Injective φ.flip) {V : Subgroup A} (hV : perpSubgroup φ V = V) :
    perpSubgroupLeft φ V = V := by
  show perpSubgroup φ.flip V = V
  refine perpSubgroup_eq_self ?_ ?_ ?_
  · exact injective_of_injective_flip hφ
  · exact fun b hb => mem_perpSubgroup.2 fun a ha =>
      mem_perpSubgroup.1 (hV.ge ha) b hb
  · have h := card_perpSubgroup_mul_card hφ V
    rwa [hV] at h

end Nondegenerate

/-! ### Elements congruent to a maximal isotropic subgroup modulo a set of conditions -/

section Conditions

variable {A : Type*} [CommGroup A] [Finite A]

/-- **The elements pairing trivially with the part of a maximal isotropic subgroup dual to a set of
conditions are exactly the elements congruent to that subgroup modulo the conditions.**

One inclusion holds because the subgroup is isotropic and the conditions kill their own dual.  The
other is a count: pairing against the conditions identifies the subgroup modulo the part dual to
them with characters of the conditions killing their intersection with the subgroup, and the
second isomorphism theorem turns the resulting inequality of orders into the one wanted. -/
theorem perpSubgroup_inf_perpSubgroupLeft {φ : A →* A →* Multiplicative QModZ}
    (hφ : Function.Injective φ.flip) {V : Subgroup A} (hV : perpSubgroup φ V = V)
    (L : Subgroup A) :
    perpSubgroup φ (V ⊓ perpSubgroupLeft φ L) = V ⊔ L := by
  haveI := finite_monoidHom_qModZ (A := ↥L)
  have hle : V ⊔ L ≤ perpSubgroup φ (V ⊓ perpSubgroupLeft φ L) := by
    refine sup_le (fun a ha => mem_perpSubgroup.2 fun x hx => ?_)
      (fun a ha => mem_perpSubgroup.2 fun x hx => ?_)
    · exact mem_perpSubgroup.1 (hV.ge ha) x (Subgroup.mem_inf.1 hx).1
    · exact mem_perpSubgroupLeft.1 (Subgroup.mem_inf.1 hx).2 a ha
  -- Pairing an element of the subgroup against the conditions.
  set ψ : ↥V →* (↥L →* Multiplicative QModZ) :=
    MonoidHom.mk' (fun v => (φ (v : A)).comp L.subtype) (fun v w => by ext x; simp)
  have hψapp : ∀ (v : ↥V) (x : ↥L), ψ v x = φ (v : A) (x : A) := fun _ _ => rfl
  have hker : ψ.ker = (V ⊓ perpSubgroupLeft φ L).subgroupOf V := by
    ext v
    refine ⟨fun hv => Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨v.2,
      mem_perpSubgroupLeft.2 fun a ha => ?_⟩), fun hv => MonoidHom.mem_ker.2 ?_⟩
    · have h := DFunLike.congr_fun (MonoidHom.mem_ker.1 hv) (⟨a, ha⟩ : ↥L)
      rw [hψapp] at h
      simpa using h
    · ext x
      have h := mem_perpSubgroupLeft.1 (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hv)).2
        (x : A) x.2
      rw [hψapp]
      simpa using h
  have hkercard : Nat.card ↥ψ.ker = Nat.card ↥(V ⊓ perpSubgroupLeft φ L) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left)).toEquiv
  have hrange : ψ.range ≤ dualAnnihilator (M := Multiplicative QModZ) (V.subgroupOf L) := by
    rintro _ ⟨v, rfl⟩
    refine mem_dualAnnihilator.2 fun x hx => ?_
    rw [hψapp]
    exact mem_perpSubgroup.1 (hV.ge (Subgroup.mem_subgroupOf.1 hx)) (v : A) v.2
  have hrangecard : Nat.card ↥ψ.range ≤ V.relIndex L := by
    have h := Subgroup.card_le_of_le hrange
    rwa [card_dualAnnihilator] at h
  have hVsplit : Nat.card ↥ψ.ker * Nat.card ↥ψ.range = Nat.card ↥V := by
    rw [← Subgroup.index_ker ψ]
    exact Subgroup.card_mul_index ψ.ker
  have hcardA : Nat.card ↥V * Nat.card ↥V = Nat.card A := by
    have h := card_perpSubgroup_mul_card hφ V
    rwa [hV] at h
  -- The second isomorphism theorem, in the form of an index.
  have hsup : Nat.card ↥V * V.relIndex L = Nat.card ↥(V ⊔ L) := by
    have h1 : Nat.card ↥(V.subgroupOf (V ⊔ L)) * (V.subgroupOf (V ⊔ L)).index
        = Nat.card ↥(V ⊔ L) := Subgroup.card_mul_index _
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : V ≤ V ⊔ L)).toEquiv] at h1
    rwa [show (V.subgroupOf (V ⊔ L)).index = V.relIndex L from
      Subgroup.relIndex_sup_left (K := V) (H := L)] at h1
  have hvle : Nat.card ↥V ≤ Nat.card ↥(V ⊓ perpSubgroupLeft φ L) * V.relIndex L := by
    rw [← hVsplit, hkercard]
    exact Nat.mul_le_mul le_rfl hrangecard
  have hkey : Nat.card ↥(V ⊓ perpSubgroupLeft φ L) * (V ⊓ perpSubgroupLeft φ L).index
      ≤ Nat.card ↥(V ⊓ perpSubgroupLeft φ L) * (Nat.card ↥V * V.relIndex L) := by
    rw [Subgroup.card_mul_index, ← hcardA]
    calc Nat.card ↥V * Nat.card ↥V
        ≤ Nat.card ↥V * (Nat.card ↥(V ⊓ perpSubgroupLeft φ L) * V.relIndex L) :=
          Nat.mul_le_mul le_rfl hvle
      _ = Nat.card ↥(V ⊓ perpSubgroupLeft φ L) * (Nat.card ↥V * V.relIndex L) := by ring
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [card_perpSubgroup hφ, ← hsup]
  exact Nat.le_of_mul_le_mul_left hkey Nat.card_pos

/-- **An element pairing trivially with the part of a maximal isotropic subgroup dual to a set of
conditions differs from an element of the subgroup by a condition.** -/
theorem exists_mul_eq_of_forall_pairing_eq_one {φ : A →* A →* Multiplicative QModZ}
    (hφ : Function.Injective φ.flip) {V : Subgroup A} (hV : perpSubgroup φ V = V)
    {L : Subgroup A} {a : A} (ha : ∀ b ∈ V ⊓ perpSubgroupLeft φ L, φ b a = 1) :
    ∃ x ∈ V, ∃ y ∈ L, x * y = a := by
  rw [← Subgroup.mem_sup, ← perpSubgroup_inf_perpSubgroupLeft hφ hV L]
  exact mem_perpSubgroup.2 ha

end Conditions

/-! ### Conditions imposed one factor at a time -/

section Pi

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*} [∀ i, CommGroup (A i)]
  {M : Type*} [CommGroup M]

/-- Exchanging the two arguments of a pairing on a product exchanges them on each factor. -/
theorem flip_piPairing (φ : ∀ i, A i →* A i →* M) :
    (piPairing φ).flip = piPairing fun i => (φ i).flip := by
  ext b a
  rfl

/-- **The orthogonal complement of a product of subgroups is the product of the orthogonal
complements**: an element supported at a single factor isolates that factor from the product
defining the pairing. -/
theorem perpSubgroup_piPairing_pi (φ : ∀ i, A i →* A i →* M) (L : ∀ i, Subgroup (A i)) :
    perpSubgroup (piPairing φ) (Subgroup.pi Set.univ L)
      = Subgroup.pi Set.univ fun i => perpSubgroup (φ i) (L i) := by
  ext b
  refine ⟨fun hb => (Subgroup.mem_pi _).2 fun j _ => mem_perpSubgroup.2 fun x hx => ?_,
    fun hb => mem_perpSubgroup.2 fun a ha => ?_⟩
  · have hsingle : Pi.mulSingle j x ∈ Subgroup.pi (Set.univ : Set ι) L := by
      refine (Subgroup.mem_pi _).2 fun i _ => ?_
      rcases eq_or_ne i j with rfl | hij
      · simpa using hx
      · rw [Pi.mulSingle_eq_of_ne hij]
        exact one_mem _
    have h := mem_perpSubgroup.1 hb _ hsingle
    rw [piPairing_apply, Finset.prod_eq_single j] at h
    · simpa using h
    · intro i _ hij
      rw [Pi.mulSingle_eq_of_ne hij, _root_.map_one, MonoidHom.one_apply]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  · rw [piPairing_apply]
    exact Finset.prod_eq_one fun i _ =>
      mem_perpSubgroup.1 ((Subgroup.mem_pi _).1 hb i (Set.mem_univ i)) (a i)
        ((Subgroup.mem_pi _).1 ha i (Set.mem_univ i))

/-- **The orthogonal complement on the left of a product of subgroups is the product of the
orthogonal complements on the left.** -/
theorem perpSubgroupLeft_piPairing_pi (φ : ∀ i, A i →* A i →* M) (L : ∀ i, Subgroup (A i)) :
    perpSubgroupLeft (piPairing φ) (Subgroup.pi Set.univ L)
      = Subgroup.pi Set.univ fun i => perpSubgroupLeft (φ i) (L i) := by
  rw [perpSubgroupLeft, flip_piPairing, perpSubgroup_piPairing_pi]
  rfl

end Pi

end InverseGalois.CFT

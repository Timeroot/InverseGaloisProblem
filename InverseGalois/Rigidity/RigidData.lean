/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.Certificate

/-!
# Rigid class data and stability under a subgroup of the cyclotomic action

The rigidity method needs two independent things from its prescribed conjugacy classes:

* **rigidity** — the generating product-one tuples in the classes form a single simultaneous
  conjugacy orbit; this is pure group theory and knows nothing about a base field;
* **invariance under the cyclotomic action** — the classes are fixed by `c ↦ c ^ k`; this is
  what pins the *field of definition* of the resulting cover.

`RigidityCertificate` bundles both, with the invariance demanded for **every** `k` coprime to the
order (rationality), which is what lands the realization over `ℚ`.  Many groups — `M₁₁` and `M₁₂`
among them — have rigid class tuples that are invariant only under a **subgroup** `H` of the
cyclotomic action; those tuples still realize the group, but over the subfield of the cyclotomic
field cut out by `H`.  This file separates the two ingredients:

* `RigidData` — the rigidity half alone (no invariance condition).  The descent tower is
  parameterized by this, so it can be run on a class tuple that is not rational.
* `ConjClasses.powClass` — the cyclotomic action `c ↦ c ^ k` on conjugacy classes.
* `IsStableClass n H c` — invariance of `c` under `H ≤ (ZMod n)ˣ`.
* `StableRigidData` / `RigidityCertificateH` — the two halves recombined at a subgroup `H`.

## The twist ambiguity

A branch cycle of a cover is only well defined up to the choice of a *generator* of the inertia
group, i.e. up to an arbitrary coprime power.  Rationality hides this ambiguity; without it the
realized class tuple is some coordinatewise twist `(C₁^{u₁}, …, C_r^{u_r})` of the prescribed one.
`RigidityCertificateH` therefore asks for rigidity of **every** such twist (`orbitRigid`), and
`RigidityCertificateH.twist` packages a twist as a `StableRigidData` — stability is inherited
because the cyclotomic action is abelian (`IsStableClass.powClass`).

## Main definitions

* `RigidData G`, `RigidityCertificate.toRigidData`
* `ConjClasses.powClass`, `IsStableClass`
* `StableRigidData G n H`, `RigidityCertificateH G n H`
* `RigidityCertificateH.twist`, `RigidityCertificate.toH`
-/

open scoped BigOperators

namespace ConjClasses

variable {G : Type*} [Group G]

/-- The **cyclotomic action on conjugacy classes**: `powClass u c` is the class of `g ^ u` for any
`g ∈ c`.  Well defined because conjugation is a group homomorphism, so it commutes with taking
powers. -/
def powClass (u : ℕ) (c : ConjClasses G) : ConjClasses G :=
  Quotient.liftOn c (fun g => ConjClasses.mk (g ^ u)) <| by
    intro a b hab
    obtain ⟨d, hd⟩ := isConj_iff.mp (hab : IsConj a b)
    refine ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨d, ?_⟩)
    have h : (MulAut.conj d) (a ^ u) = ((MulAut.conj d) a) ^ u := map_pow _ _ _
    simpa only [MulAut.conj_apply, hd] using h

@[simp] theorem powClass_mk (u : ℕ) (g : G) :
    powClass u (ConjClasses.mk g) = ConjClasses.mk (g ^ u) := rfl

@[simp] theorem powClass_one (c : ConjClasses G) : powClass 1 c = c := by
  obtain ⟨g, rfl⟩ := Quotient.exists_rep c
  show powClass 1 (ConjClasses.mk g) = ConjClasses.mk g
  rw [powClass_mk, pow_one]

/-- Iterating the cyclotomic action multiplies the exponents. -/
theorem powClass_powClass (u v : ℕ) (c : ConjClasses G) :
    powClass u (powClass v c) = powClass (v * u) c := by
  obtain ⟨g, rfl⟩ := Quotient.exists_rep c
  show powClass u (powClass v (ConjClasses.mk g)) = powClass (v * u) (ConjClasses.mk g)
  rw [powClass_mk, powClass_mk, powClass_mk, pow_mul]

/-- Conjugate elements have the same order. -/
theorem orderOf_eq_of_mk_eq {g h : G} (hgh : ConjClasses.mk g = ConjClasses.mk h) :
    orderOf g = orderOf h := by
  obtain ⟨d, hd⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hgh)
  have hord : orderOf ((MulAut.conj d).toMonoidHom g) = orderOf g :=
    orderOf_injective _ (MulAut.conj d).injective _
  rw [show (MulAut.conj d).toMonoidHom g = h from hd] at hord
  exact hord.symm

/-- Elements of a twisted class have order dividing the order of elements of the original class. -/
theorem orderOf_dvd_of_mk_eq_powClass {u : ℕ} {c : ConjClasses G} {g h : G}
    (hg : ConjClasses.mk g = powClass u c) (hh : ConjClasses.mk h = c) :
    orderOf g ∣ orderOf h := by
  rw [← hh, powClass_mk] at hg
  obtain ⟨d, hd⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hg)
  have hord : orderOf ((MulAut.conj d).toMonoidHom g) = orderOf g :=
    orderOf_injective _ (MulAut.conj d).injective _
  rw [show (MulAut.conj d).toMonoidHom g = h ^ u from hd] at hord
  rw [← hord]
  exact orderOf_pow_dvd u

end ConjClasses

variable {G : Type*} [Group G]

/-- A conjugacy class `c` is **`H`-stable**, for a subgroup `H` of the units of `ZMod n`, if it is
fixed by every cyclotomic power `c ↦ c ^ k` whose exponent `k` reduces into `H` mod `n`.

Rationality (`IsRationalClass`) is the case `H = ⊤`; a proper `H` cuts out a proper subfield of the
`n`-th cyclotomic field as the field of definition. -/
def IsStableClass (n : ℕ) (H : Subgroup (ZMod n)ˣ) (c : ConjClasses G) : Prop :=
  ∀ u ∈ H, ∀ k : ℕ, (k : ZMod n) = ((u : (ZMod n)ˣ) : ZMod n) → ConjClasses.powClass k c = c

/-- **Stability is inherited by the twists.**  The cyclotomic action is by an abelian group, so
`c ^ v` is `H`-stable whenever `c` is. -/
theorem IsStableClass.powClass {n : ℕ} {H : Subgroup (ZMod n)ˣ} {c : ConjClasses G}
    (hc : IsStableClass n H c) (v : ℕ) : IsStableClass n H (ConjClasses.powClass v c) := by
  intro u hu k hk
  rw [ConjClasses.powClass_powClass, mul_comm, ← ConjClasses.powClass_powClass, hc u hu k hk]

/-- A rational class is stable under the **whole** cyclotomic action, provided the modulus `n` is a
multiple of the order of its elements. -/
theorem isStableClass_top_of_isRationalClass {n : ℕ} [NeZero n] {c : ConjClasses G}
    (hord : ∀ g : G, ConjClasses.mk g = c → orderOf g ∣ n) (hc : IsRationalClass c) :
    IsStableClass n ⊤ c := by
  intro u _ k hk
  obtain ⟨g, rfl⟩ := Quotient.exists_rep c
  have hcn : Nat.Coprime k n := by
    refine (ZMod.isUnit_iff_coprime k n).mp ?_
    rw [hk]
    exact (u : (ZMod n)ˣ).isUnit
  show ConjClasses.powClass k (ConjClasses.mk g) = ConjClasses.mk g
  rw [ConjClasses.powClass_mk]
  exact hc g rfl k (hcn.coprime_dvd_right (hord g rfl))

/-- **A rational class absorbs every admissible twist.**  If the exponent `u` is coprime to the
order of every element of `c`, then `c ^ u = c`.  This is the form in which rationality collapses
the inertia-generator ambiguity of a branch cycle. -/
theorem IsRationalClass.powClass_eq {c : ConjClasses G} (hc : IsRationalClass c) {u : ℕ}
    (hu : ∀ x : G, ConjClasses.mk x = c → Nat.Coprime u (orderOf x)) :
    ConjClasses.powClass u c = c := by
  obtain ⟨g, rfl⟩ := Quotient.exists_rep c
  show ConjClasses.powClass u (ConjClasses.mk g) = ConjClasses.mk g
  rw [ConjClasses.powClass_mk]
  exact hc g rfl u (hu g rfl)

/-- **The rigidity half of a certificate**, with no invariance condition on the classes: a
centerless group together with a class tuple whose generating product-one tuples form a single
simultaneous-conjugacy orbit.

This is what the branch-cycle descent tower is built over.  Splitting it off from
`RigidityCertificate` is what lets the tower be run on a class tuple that is *not* rational — the
invariance condition is only consumed at the very end, where it fixes the field of definition. -/
structure RigidData (G : Type*) [Group G] [Finite G] where
  /-- the number of prescribed classes (branch points). -/
  r : ℕ
  /-- the prescribed conjugacy classes `C₁,…,C_r`. -/
  C : Fin r → ConjClasses G
  /-- `G` is centerless (trivial center). -/
  center_triv : ∀ g : G, g ∈ Subgroup.center G → g = 1
  /-- there is at least one generating product-one tuple in the prescribed classes. -/
  gen : (rigidTuples C).Nonempty
  /-- **rigidity**: exactly `|G|` such tuples (structure constant `= 1`). -/
  rigid : Nat.card (rigidTuples C) = Nat.card G

/-- Forgetting the rationality of a certificate's classes. -/
def RigidityCertificate.toRigidData {G : Type*} [Group G] [Finite G]
    (cert : RigidityCertificate G) : RigidData G where
  r := cert.r
  C := cert.C
  center_triv := cert.center_triv
  gen := cert.gen
  rigid := cert.rigid

@[simp] theorem RigidityCertificate.toRigidData_r {G : Type*} [Group G] [Finite G]
    (cert : RigidityCertificate G) : cert.toRigidData.r = cert.r := rfl

@[simp] theorem RigidityCertificate.toRigidData_C {G : Type*} [Group G] [Finite G]
    (cert : RigidityCertificate G) : cert.toRigidData.C = cert.C := rfl

/-- **The coordinatewise cyclotomic twist of rigid class data.**  The class tuple is replaced by
`(C₁^{u₁}, …, C_r^{u_r})`; rigidity of the twisted tuple is the hypothesis, and nonemptiness follows
from it because `|G| ≠ 0`.

This is the shape in which the geometry delivers its class tuple: a branch cycle is only determined
up to the choice of a generator of its inertia group, so the realized tuple is a twist of the
prescribed one.  For a rational tuple the twist is the tuple itself (`twistBy_eq_self`). -/
def RigidData.twistBy {G : Type*} [Group G] [Finite G] (rd : RigidData G) (u : Fin rd.r → ℕ)
    (hrig : Nat.card (rigidTuples fun i => ConjClasses.powClass (u i) (rd.C i)) = Nat.card G) :
    RigidData G where
  r := rd.r
  C := fun i => ConjClasses.powClass (u i) (rd.C i)
  center_triv := rd.center_triv
  gen := by
    have hpos : Nat.card G ≠ 0 := Nat.card_pos.ne'
    rw [← hrig, Nat.card_ne_zero] at hpos
    exact Set.nonempty_coe_sort.mp hpos.1
  rigid := hrig

@[simp] theorem RigidData.twistBy_r {G : Type*} [Group G] [Finite G] (rd : RigidData G)
    (u : Fin rd.r → ℕ) (hrig) : (rd.twistBy u hrig).r = rd.r := rfl

@[simp] theorem RigidData.twistBy_C {G : Type*} [Group G] [Finite G] (rd : RigidData G)
    (u : Fin rd.r → ℕ) (hrig) (i : Fin rd.r) :
    (rd.twistBy u hrig).C i = ConjClasses.powClass (u i) (rd.C i) := rfl

/-- **A twist that fixes every class changes nothing.**  This is what makes the twist ambiguity
invisible for a rational class tuple. -/
theorem RigidData.twistBy_eq_self {G : Type*} [Group G] [Finite G] (rd : RigidData G)
    (u : Fin rd.r → ℕ) (hrig) (h : ∀ i, ConjClasses.powClass (u i) (rd.C i) = rd.C i) :
    rd.twistBy u hrig = rd := by
  obtain ⟨r, C, ct, gen, rigid⟩ := rd
  have hC : (fun i => ConjClasses.powClass (u i) (C i)) = C := funext h
  show RigidData.mk r (fun i => ConjClasses.powClass (u i) (C i)) _ _ _ = RigidData.mk r C _ _ _
  congr 1

/-- **Rigid class data whose classes are stable under `H ≤ (ZMod n)ˣ`.**  This is the input of the
descent that lands over the subfield of `ℚ(ζ_n)` fixed by `H`, in place of `ℚ` itself. -/
structure StableRigidData (G : Type*) [Group G] [Finite G] (n : ℕ) (H : Subgroup (ZMod n)ˣ)
    extends RigidData G where
  /-- the modulus is a multiple of the order of every element of every prescribed class. -/
  order_dvd : ∀ (i : Fin r) (g : G), ConjClasses.mk g = C i → orderOf g ∣ n
  /-- each prescribed class is `H`-stable. -/
  stable : ∀ i, IsStableClass n H (C i)

/-- A **rigidity certificate at a subgroup `H` of the cyclotomic action**: the classes are only
required to be `H`-stable rather than rational, and rigidity is required of every coordinatewise
cyclotomic twist of the class tuple.

The twists must be included because a branch cycle is only determined up to the choice of a
generator of its inertia group; with rational classes that ambiguity is invisible, and
`RigidityCertificate.toH` shows the extra condition is then vacuous. -/
structure RigidityCertificateH (G : Type*) [Group G] [Finite G] (n : ℕ)
    (H : Subgroup (ZMod n)ˣ) where
  /-- the number of prescribed classes (branch points). -/
  r : ℕ
  /-- the prescribed conjugacy classes `C₁,…,C_r`. -/
  C : Fin r → ConjClasses G
  /-- `G` is centerless (trivial center). -/
  center_triv : ∀ g : G, g ∈ Subgroup.center G → g = 1
  /-- the modulus is a multiple of the order of every element of every prescribed class. -/
  order_dvd : ∀ (i : Fin r) (g : G), ConjClasses.mk g = C i → orderOf g ∣ n
  /-- each prescribed class is `H`-stable. -/
  stable : ∀ i, IsStableClass n H (C i)
  /-- there is at least one generating product-one tuple in the prescribed classes. -/
  gen : (rigidTuples C).Nonempty
  /-- **rigidity of every cyclotomic twist**: for every tuple of exponents coprime to `n`, the
  twisted class tuple again has exactly `|G|` generating product-one tuples. -/
  orbitRigid : ∀ u : Fin r → ℕ, (∀ i, Nat.Coprime (u i) n) →
    Nat.card (rigidTuples fun i => ConjClasses.powClass (u i) (C i)) = Nat.card G

namespace RigidityCertificateH

variable {G : Type*} [Group G] [Finite G] {n : ℕ} {H : Subgroup (ZMod n)ˣ}

/-- **A cyclotomic twist of the certificate's class tuple is again stable rigid data.**

* rigidity is the `orbitRigid` field;
* nonemptiness of the tuple set follows from rigidity (`|G| ≠ 0`);
* stability is inherited (`IsStableClass.powClass`);
* the order bound is inherited because `orderOf (g ^ u) ∣ orderOf g`. -/
def twist (certH : RigidityCertificateH G n H) (u : Fin certH.r → ℕ)
    (hu : ∀ i, Nat.Coprime (u i) n) : StableRigidData G n H where
  r := certH.r
  C := fun i => ConjClasses.powClass (u i) (certH.C i)
  center_triv := certH.center_triv
  gen := by
    have hcard := certH.orbitRigid u hu
    have hpos : Nat.card G ≠ 0 := Nat.card_pos.ne'
    rw [← hcard, Nat.card_ne_zero] at hpos
    exact Set.nonempty_coe_sort.mp hpos.1
  rigid := certH.orbitRigid u hu
  order_dvd := by
    intro i g hg
    obtain ⟨h, hh⟩ := Quotient.exists_rep (certH.C i)
    exact (ConjClasses.orderOf_dvd_of_mk_eq_powClass hg hh).trans (certH.order_dvd i h hh)
  stable := fun i => (certH.stable i).powClass (u i)

@[simp] theorem twist_r (certH : RigidityCertificateH G n H) (u : Fin certH.r → ℕ)
    (hu : ∀ i, Nat.Coprime (u i) n) : (certH.twist u hu).r = certH.r := rfl

@[simp] theorem twist_C (certH : RigidityCertificateH G n H) (u : Fin certH.r → ℕ)
    (hu : ∀ i, Nat.Coprime (u i) n) (i : Fin certH.r) :
    (certH.twist u hu).C i = ConjClasses.powClass (u i) (certH.C i) := rfl

end RigidityCertificateH

/-- **A rational certificate is a certificate at the full cyclotomic action.**  Rationality makes
every cyclotomic twist of the class tuple equal to the tuple itself, so the twist-rigidity
condition collapses to plain rigidity. -/
def RigidityCertificate.toH {G : Type*} [Group G] [Finite G] (cert : RigidityCertificate G)
    (n : ℕ) [NeZero n]
    (hord : ∀ (i : Fin cert.r) (g : G), ConjClasses.mk g = cert.C i → orderOf g ∣ n) :
    RigidityCertificateH G n ⊤ where
  r := cert.r
  C := cert.C
  center_triv := cert.center_triv
  order_dvd := hord
  stable := fun i => isStableClass_top_of_isRationalClass (hord i) (cert.rational i)
  gen := cert.gen
  orbitRigid := by
    intro u hu
    have hC : (fun i => ConjClasses.powClass (u i) (cert.C i)) = cert.C := by
      funext i
      obtain ⟨g, hg₀⟩ := Quotient.exists_rep (cert.C i)
      have hg : ConjClasses.mk g = cert.C i := hg₀
      rw [← hg, ConjClasses.powClass_mk, hg]
      exact cert.rational i g hg (u i) ((hu i).coprime_dvd_right (hord i g hg))
    rw [hC]
    exact cert.rigid

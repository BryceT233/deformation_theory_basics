/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

module

public import Mathlib

@[expose] public section

universe w w' v u

instance (priority := 100) {R : Type*} [CommRing R] [IsArtinianRing R] [IsLocalRing R] :
    IsAdicComplete (IsLocalRing.maximalIdeal R) R where
  prec' f hf := by
    obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal R).mp inferInstance
    use f n; intro m
    by_cases h : m ≤ n
    · exact hf h
    specialize hf (show n ≤ m by lia)
    rw [hn, zero_smul, Ideal.zero_eq_bot, SModEq.bot] at hf
    rw [hf]

--------------------------------------------------------------------------------

lemma Order.krullDim_le_of_orderEmbedding {α β : Type*} [Preorder α] [PartialOrder β] (e : α ↪o β) :
    Order.krullDim α ≤ Order.krullDim β := by
  have (b : β) : Subsingleton (e ⁻¹' {b}) := Set.Subsingleton.coe_sort <|
    Set.Subsingleton.preimage Set.subsingleton_singleton e.injective
  simpa using Order.krullDim_le_of_krullDim_preimage_le' e e.monotone fun _ ↦
    Order.krullDim_nonpos_of_subsingleton

theorem Submodule.length_le_length_restrictScalar (A R M : Type*) [Ring A] [Ring R] [SMul A R]
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower A R M] (p : Submodule R M) :
    Module.length R p ≤ Module.length A (p.restrictScalars A) := by
  rw [← WithBot.coe_le_coe, Module.coe_length, Module.coe_length]
  exact Order.krullDim_le_of_orderEmbedding (restrictScalarsEmbedding A R p)

lemma ENat.lt_add_left {n k : ℕ∞} (h : n ≠ ⊤) (h' : 0 < k) : n < k + n := by
  nth_rw 1 [← zero_add n, ENat.add_lt_add_iff_right h]
  exact h'

theorem Submodule.length_quotient_lt {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [IsArtinian R M] [IsNoetherian R M] (p : Submodule R M) (h : p ≠ ⊥) :
    Module.length R (M ⧸ p) < Module.length R M := by
  rw [Module.length_eq_add_of_exact p.subtype p.mkQ p.subtype_injective p.mkQ_surjective
    (LinearMap.exact_subtype_mkQ p)]
  exact ENat.lt_add_left Module.length_ne_top
    (Module.length_pos_iff.mpr (nontrivial_iff_ne_bot.mpr h))

--------------------------------------------------------------------------------

-- goes to `Mathlib.RingTheory.Ideal.Maps`

open Submodule in
theorem Ideal.annihilator_inf_ne_bot {R : Type*} [CommSemiring R] {I J : Ideal R}
    (hI : IsNilpotent I) (hJ : J ≠ ⊥) : I.annihilator ⊓ J ≠ ⊥ := by
  rcases hI with ⟨n, hn⟩
  have h_ex : ∃ t : ℕ, J • I ^ t = ⊥ := ⟨n, by simp [hn]⟩
  let t := Nat.find h_ex
  have ht : J • I ^ t = ⊥ := Nat.find_spec h_ex
  by_cases t = 0; · simp_all
  obtain ⟨s, hs⟩ := Nat.exists_add_one_eq.mpr (show 0 < t by lia)
  obtain ⟨x, x_in, x_ne⟩ := (Submodule.ne_bot_iff _).mp (Nat.find_min h_ex (show s < t by lia))
  refine (Submodule.ne_bot_iff _).mpr ⟨x, mem_inf.mpr ⟨mem_annihilator.mpr fun r r_in ↦ ?_, ?_⟩,
    x_ne⟩
  · rw [smul_eq_mul, ← mem_bot, ← ht, ← hs, pow_succ, ← smul_eq_mul, ← smul_assoc]
    exact smul_mem_smul x_in r_in
  · rw [smul_eq_mul, mul_comm, ← smul_eq_mul] at x_in
    exact smul_le_right x_in

--------------------------------------------------------------------------------

-- `Subring/Basic.lean` `LocalRing/LocalSubring.lean` `Subalgebra/Basic.lean`

namespace RingHom

theorem isUnit_eqLocus_mk_iff {R S : Type*} [Ring R] [Semiring S] (f g : R →+* S) {r : R}
    (r_in : r ∈ f.eqLocus g) : IsUnit (⟨r, r_in⟩ : f.eqLocus g) ↔ IsUnit r := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp [isUnit_iff_exists, ← Subtype.val_inj] at h ⊢
    grind
  rw [mem_eqLocus] at r_in
  obtain ⟨s, hs⟩ := isUnit_iff_exists.mp h
  simp only [isUnit_iff_exists, ← Subtype.val_inj, Subring.coe_mul, OneMemClass.coe_one,
    Subtype.exists, mem_eqLocus, exists_and_left, exists_prop]
  refine ⟨s, hs.left, ?_, hs.right⟩
  rw [← mul_one (f s), ← map_one g, ← hs.left, map_mul, ← mul_assoc, ← r_in, ← map_mul, hs.right,
    map_one, one_mul]

theorem isLocalRing_eqLocus {R S : Type*} [Ring R] [Semiring S] [IsLocalRing R] (f g : R →+* S) :
    IsLocalRing (f.eqLocus g) :=
  Subring.isLocalRing_of_unit _ fun _ h ↦ (RingHom.isUnit_eqLocus_mk_iff f g h).mpr

section pullback

variable {R S T : Type*} [Ring R] [Ring S] [Semiring T]

/-- The subring of pairs `(r, s) : R × S` such that `f r = g s`, i.e.,
  the pullback of f and g as a subring of R × S. -/
abbrev pullback (f : R →+* T) (g : S →+* T) : Subring (R × S) :=
  (f.comp (RingHom.fst R S)).eqLocus <| g.comp (RingHom.snd R S)

/-- The first projection from the pullback of `f` and `g` to `A`. -/
abbrev pullbackFst (f : R →+* T) (g : S →+* T) : f.pullback g →+* R :=
  (RingHom.fst R S).comp (RingHom.pullback f g).subtype

/-- The second projection from the pullback of `f` and `g` to `B`. -/
abbrev pullbackSnd (f : R →+* T) (g : S →+* T) : f.pullback g →+* S :=
  (RingHom.snd R S).comp (f.pullback g).subtype

theorem isUnit_pullback_mk_iff (f : R →+* T) (g : S →+* T) {a : R × S} (a_in : a ∈ f.pullback g) :
    IsUnit (⟨a, a_in⟩ : f.pullback g) ↔ IsUnit a.1 ∧ IsUnit a.2 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← Prod.isUnit_iff]
    simp [isUnit_iff_exists, ← Subtype.val_inj] at h ⊢
    grind
  simp only [mem_eqLocus, coe_comp, coe_fst, Function.comp_apply, coe_snd] at a_in
  obtain ⟨s, hs⟩ := isUnit_iff_exists.mp h.left
  obtain ⟨t, ht⟩ := isUnit_iff_exists.mp h.right
  simp only [isUnit_iff_exists, ← Subtype.val_inj, Subring.coe_mul, Prod.mul_def,
    OneMemClass.coe_one, Prod.mk_eq_one, Subtype.exists, mem_eqLocus, coe_comp, coe_fst,
    Function.comp_apply, coe_snd, exists_and_left, exists_prop, Prod.exists]
  refine ⟨s, t, ⟨⟨hs.left, ht.left⟩, hs.right, ?_, ht.right⟩⟩
  rw [← mul_one (f s), ← map_one g, ← ht.left, map_mul, ← mul_assoc, ← a_in, ← map_mul,
    hs.right, map_one, one_mul]

open Function in
theorem surjective_pullbackFst_of_surjective (f : R →+* T) (g : S →+* T) (h : Surjective g) :
    Surjective (f.pullbackFst g) := fun r ↦ by simpa [eq_comm] using h (f r)

open Function in
theorem surjective_pullbackSnd_of_surjective (f : R →+* T) (g : S →+* T) (h : Surjective f) :
    Surjective (f.pullbackSnd g) := fun s ↦ by simpa [eq_comm] using h (g s)

end pullback

end RingHom

open RingHom in
theorem isLocalRing_ringHomPullback {R S T F G : Type*} [Ring R] [Ring S] [Semiring T]
    [IsLocalRing R] [FunLike F R T] [RingHomClass F R T] [FunLike G S T] [RingHomClass G S T]
    (f : F) (g : G) (hg : IsLocalHom g) :
    IsLocalRing (RingHom.pullback (f : R →+* T) (g : S →+* T)) where
  isUnit_or_isUnit_of_add_one {a b} h := by
    rcases a with ⟨⟨u, v⟩, huv⟩; rcases b with ⟨⟨s, t⟩, hst⟩
    simp only [AddMemClass.mk_add_mk, Prod.mk_add_mk, ← Subtype.val_inj, OneMemClass.coe_one,
      Prod.mk_eq_one] at h
    simp only [RingHom.mem_eqLocus, RingHom.coe_comp, RingHom.coe_coe, RingHom.coe_fst,
      Function.comp_apply, RingHom.coe_snd] at huv hst
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one h.left with hu | hs
    · have : IsUnit (g v) := by rw [← huv]; exact IsUnit.map f hu
      apply IsLocalHom.map_nonunit at this
      left; simpa [isUnit_pullback_mk_iff] using ⟨hu, this⟩
    have : IsUnit (g t) := by rw [← hst]; exact IsUnit.map f hs
    apply IsLocalHom.map_nonunit at this
    right; simpa [isUnit_pullback_mk_iff] using ⟨hs, this⟩

namespace RingEquiv

abbrev pullbackProdComm {R S T : Type*} [Ring R] [Ring S] [Semiring T] (f : R →+* T)
    (g : S →+* T) : f.pullback g ≃+* g.pullback f :=
  (RingEquiv.prodComm (R := R) (S := S)).restrict (f.pullback g) (g.pullback f) (by simp [eq_comm])

end RingEquiv

namespace AlgHom

variable {R A B C : Type*} [CommSemiring R]

section Semiring

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

/-- The subalgebra of pairs `(a, b) : A × B` such that `f a = g b`, i.e.,
  the pullback of f and g as a subalgebra of A × B. -/
abbrev pullback (f : A →ₐ[R] C) (g : B →ₐ[R] C) : Subalgebra R (A × B) := equalizer
  (f.comp (fst R A B)) (g.comp (snd R A B))

/-- The first projection from the pullback of `f` and `g` to `A`. -/
abbrev pullbackFst (f : A →ₐ[R] C) (g : B →ₐ[R] C) : pullback f g →ₐ[R] A :=
  (fst R A B).comp (pullback f g).val

/-- The second projection from the pullback of `f` and `g` to `B`. -/
abbrev pullbackSnd (f : A →ₐ[R] C) (g : B →ₐ[R] C) : pullback f g →ₐ[R] B :=
  (snd R A B).comp (pullback f g).val

end Semiring

section Ring

variable [Ring A] [Algebra R A] [Ring B] [Algebra R B] [Semiring C] [Algebra R C]

theorem isUnit_pullback_mk_iff (f : A →ₐ[R] C) (g : B →ₐ[R] C) {a : A × B}
    (a_in : a ∈ f.pullback g) : IsUnit (⟨a, a_in⟩ : f.pullback g) ↔
      IsUnit a.1 ∧ IsUnit a.2 :=
  RingHom.isUnit_pullback_mk_iff (f : A →+* C) (g : B →+* C) a_in

theorem surjective_pullbackFst_of_surjective (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (h : Function.Surjective g) : Function.Surjective (pullbackFst f g) :=
  RingHom.surjective_pullbackFst_of_surjective (f : A →+* C) (g : B →+* C) h

theorem surjective_pullbackSnd_of_surjective (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (h : Function.Surjective f) : Function.Surjective (pullbackSnd f g) :=
  RingHom.surjective_pullbackSnd_of_surjective (f : A →+* C) (g : B →+* C) h

end Ring

end AlgHom

theorem isLocalRing_algHomPullback {R S T A : Type*} [CommSemiring R] [Ring S] [Algebra R S]
    [IsLocalRing S] [Ring T] [Algebra R T] [Semiring A] [Algebra R A] (f : S →ₐ[R] A)
    (g : T →ₐ[R] A) (hg : IsLocalHom g) : IsLocalRing (AlgHom.pullback f g) :=
  isLocalRing_ringHomPullback (f : S →+* A) (g : T →+* A) ⟨hg.map_nonunit⟩

--------------------------------------------------------------------------------

-- goes to `Algebra/Polynomial/Taylor.lean`
theorem Polynomial.exists_mul_sq_add_linear_part_eq_eval_add {R : Type*} [CommSemiring R]
    (p : Polynomial R) (x y : R) : ∃ c : R, c * y ^ 2 + p.derivative.eval x * y + p.eval x =
      p.eval (x + y) := by
  rw [add_comm, ← p.taylor_eval x y, ((taylor x) p).eval_eq_sum_range'
    ((Nat.lt_succ_self _).trans (Nat.lt_succ_self _)), Finset.sum_range_succ',
    Finset.sum_range_succ']
  use ∑ x_1 ∈ Finset.range p.natDegree, ((taylor x) p).coeff (x_1 + 1 + 1) * y ^ x_1
  simp [pow_succ, mul_assoc, Finset.sum_mul]

-- goes to `RingTheory/Henselian.lean`
open Polynomial in
@[stacks 06RR]
theorem IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub {R : Type*} [CommRing R] [IsLocalRing R]
    {f : Polynomial R} {a b : R} (ha : f.eval a = 0) (hb : f.eval b = 0) (h : ¬ IsUnit (a - b))
    (h' : IsUnit (f.derivative.eval a)) : a = b := by
  obtain ⟨c, hc⟩ := exists_mul_sq_add_linear_part_eq_eval_add f a (b - a)
  rw [add_sub_cancel, ha, hb, add_zero, pow_two, ← mul_assoc, ← add_mul] at hc
  suffices IsUnit (c * (b - a) + eval a (derivative f)) by
    rw [isUnit_iff_exists] at this
    rcases this with ⟨u, _, hu⟩
    apply mul_eq_zero_of_right u at hc
    rwa [← mul_assoc, hu, one_mul, sub_eq_zero, eq_comm] at hc
  by_contra
  rw [← notMem_maximalIdeal, not_not] at h this
  replace this := (maximalIdeal R).add_mem this ((maximalIdeal R).mul_mem_left c h)
  ring_nf at this
  contradiction

--------------------------------------------------------------------------------

namespace Ideal

open Submodule

variable {A : Type*} [CommRing A]

/-- The canonical surjective map from `I` to the cotangent space of its image in `A / J`. -/
def toCotangentMapMk (I J : Ideal A) : I →ₗ[A] (I.map (Ideal.Quotient.mk J)).Cotangent where
  toFun x := (I.map (Ideal.Quotient.mk J)).toCotangent ⟨Ideal.Quotient.mk J x,
    Ideal.mem_map_of_mem _ x.prop⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma surjective_toCotangentMapMk (I J : Ideal A) :
    Function.Surjective (I.toCotangentMapMk J) := fun x ↦ by
  rcases toCotangent_surjective _ x with ⟨⟨x, h⟩, rfl⟩
  rw [mem_map_iff_of_surjective _ Quotient.mk_surjective] at h
  obtain ⟨x, x_in, rfl⟩ := h
  exact ⟨⟨x, x_in⟩, rfl⟩

lemma ker_toCotangentMapMk (I J : Ideal A) :
    LinearMap.ker (I.toCotangentMapMk J) = (Submodule.comap I.subtype J) ⊔ I • ⊤ := by
  ext x
  suffices (Quotient.mk J) x ∈ map (Quotient.mk J) I ^ 2 ↔ ∃ a ∈ J, a ∈ I ∧
    ∃ a_1 ∈ I * I, a_1 ∈ I ∧ a + a_1 = x by simpa [mem_sup, mem_smul_top_iff, toCotangentMapMk,
      toCotangent_eq_zero, ← Subtype.val_inj]
  simp_rw [← Ideal.map_pow, ← mem_comap, comap_map_of_surjective' _ Quotient.mk_surjective, mk_ker,
    mem_sup, ← pow_two]
  have pow_le : I ^ 2 ≤ I := pow_le_self (by simp)
  refine ⟨fun ⟨y, y_in, z, z_in, hyz⟩ ↦ ⟨z, z_in, ?_, y, y_in, pow_le y_in, by rwa [add_comm]⟩,
    fun _ ↦ by grind⟩
  rw [eq_comm, ← sub_eq_iff_eq_add'] at hyz
  rw [← hyz]
  exact Ideal.sub_mem _ x.prop (pow_le y_in)

/-- The linear equivalence between the cotangent space of the image of `I` in `A / J` and
`I / ((I ∩ J) + I^2)`. -/
noncomputable def cotangentMapMkEquiv (I J : Ideal A) :
    (I.map (Ideal.Quotient.mk J)).Cotangent ≃ₗ[A] I ⧸ (Submodule.comap I.subtype J) ⊔ I • ⊤ :=
  ((I.toCotangentMapMk J).quotKerEquivOfSurjective (surjective_toCotangentMapMk I J)).symm.trans
    (Submodule.quotEquivOfEq _ _ (ker_toCotangentMapMk I J))

@[simp]
lemma cotangentMapMkEquiv_symm_mk (I J : Ideal A) (x : I) :
    (cotangentMapMkEquiv I J).symm (Submodule.Quotient.mk x) = I.toCotangentMapMk J x :=
  rfl

@[simp]
lemma cotangentMapMkEquiv_toCotangentMapMk (I J : Ideal A) (x : I) :
    cotangentMapMkEquiv I J (I.toCotangentMapMk J x) = Submodule.Quotient.mk x := by
  rw [← cotangentMapMkEquiv_symm_mk, LinearEquiv.apply_symm_apply]

end Ideal

--------------------------------------------------------------------------------

/-! # some `ULift` instances.
goes to where `RingEquiv` API locates. -/

instance {R : Type*} [Semiring R] [IsNoetherianRing R] : IsNoetherianRing (ULift R) :=
  isNoetherianRing_of_ringEquiv R (ULift.ringEquiv.symm)

instance {R : Type*} [Semiring R] [IsArtinianRing R] : IsArtinianRing (ULift R) :=
  RingEquiv.isArtinianRing (ULift.ringEquiv.symm)

instance {R : Type*} [CommSemiring R] [IsLocalRing R] : IsLocalRing (ULift R) :=
  RingEquiv.isLocalRing (ULift.ringEquiv.symm)

open IsLocalRing in
instance {R : Type*} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] :
    IsAdicComplete (maximalIdeal (ULift.{u} R)) (ULift.{u} R) := by
  rwa [← IsAdicComplete.congr_ringEquiv _ ULift.ringEquiv, IsLocalRing.eq_maximalIdeal
    (Ideal.map_isMaximal_of_equiv ULift.ringEquiv)]

@[to_additive (attr := simp)]
theorem ULift.isUnit_up {M : Type*} [Monoid M] {a : M} : IsUnit (ULift.up a) ↔ IsUnit a :=
  ⟨IsUnit.map MulEquiv.ulift, IsUnit.map MulEquiv.ulift.symm⟩

@[to_additive (attr := simp)]
theorem ULift.isUnit_down {M : Type*} [Monoid M] {a : ULift M} : IsUnit a.down ↔ IsUnit a :=
  ULift.isUnit_up.symm

--------------------------------------------------------------------------------

/-! # The Category of Local Algebras with a Fixed Residue Field

* `LocAlgCat` : The type of objects in the category of local `Λ`-algebras
  with residue field `k`. An object of `LocAlgCat` consists of a local `Λ`-algebra `A` equipped
  with a surjective residue map to `k`.

* `LocAlgCat.Hom` : The type of morphisms between objects in `LocAlgCat Λ k`.
  A morphism `f : A ⟶ B` is a local `Λ`-algebra homomorphism compatible with the residue maps.

-/

open IsLocalRing CategoryTheory Function

variable {Λ : Type u} [CommRing Λ]
variable {k : Type v} [Field k] [Algebra Λ k]

/-- The category of local `Λ`-algebras with residue field `k` and their morphisms. An object of
`LocAlgCat` consists of a local `Λ`-algebra `A` equipped with a surjective map to `k`. -/
structure LocAlgCat (Λ : Type u) (k : Type v) [CommRing Λ] [Field k] [Algebra Λ k] where
  private mk ::
  /-- The underlying type of the local `Λ`-algebras. -/
  carrier : Type w
  [commRing : CommRing carrier]
  [localRing : IsLocalRing carrier]
  [baseAlgebra : Algebra Λ carrier]
  [residueAlgebra : Algebra carrier k]
  [scalarTower : IsScalarTower Λ carrier k]
  surj : Surjective (algebraMap carrier k)

namespace LocAlgCat

variable {A B C : LocAlgCat.{w} Λ k} {X Y Z : Type w}
variable [CommRing X] [IsLocalRing X] [Algebra Λ X] [Algebra X k] [IsScalarTower Λ X k]
variable [CommRing Y] [IsLocalRing Y] [Algebra Λ Y] [Algebra Y k] [IsScalarTower Λ Y k]
variable [CommRing Z] [IsLocalRing Z] [Algebra Λ Z] [Algebra Z k] [IsScalarTower Λ Z k]
variable {hX : Surjective (algebraMap X k)} {hY : Surjective (algebraMap Y k)}
  {hZ : Surjective (algebraMap Z k)}

attribute [instance] localRing commRing baseAlgebra scalarTower residueAlgebra

initialize_simps_projections LocAlgCat (-localRing, -commRing, -baseAlgebra, -residueAlgebra,
-scalarTower)

instance : CoeSort (LocAlgCat Λ k) (Type w) := ⟨carrier⟩

attribute [coe] carrier

/-- The canonical residue map from an object `A` to `k`.
This is a prefered way to apply residue maps in `LocAlgCat`. -/
def residue (A : LocAlgCat Λ k) : A →ₐ[Λ] k :=
  IsScalarTower.toAlgHom Λ A k

lemma residue_toRingHom : A.residue = algebraMap A k := rfl

lemma residue_apply {a : A} : A.residue a = algebraMap A k a := rfl

lemma ker_residue : RingHom.ker (residue A) = maximalIdeal A :=
  eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ A.surj)

lemma residue_surjective : Surjective (residue A) := A.surj

lemma residue_eq_zero_iff {x : A} : residue A x = 0 ↔ x ∈ maximalIdeal A := by
  rw [← RingHom.mem_ker, ker_residue]

variable (Λ k) in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The object in the category of local `Λ`-algebras associated to a type equipped with
the appropriate typeclasses. This is a preferred way to construct a term of `LocAlgCat`. -/
abbrev of (X : Type w) [CommRing X] [IsLocalRing X] [Algebra Λ X] [Algebra X k]
    [IsScalarTower Λ X k] (h : Surjective (algebraMap X k)) : LocAlgCat Λ k :=
  ⟨X, h⟩

@[simp]
lemma coe_of : (of Λ k X hX : Type w) = X := rfl

@[simp]
lemma residue_of_apply {x : (of Λ k X hX)} : (of Λ k X hX).residue x = algebraMap X k x := rfl

/-- The canonical equivalence between the residue field of an object and `k`. -/
noncomputable def residueEquiv (A : LocAlgCat Λ k) : ResidueField A ≃ₐ[Λ] k where
  __ := (Ideal.quotEquivOfEq (ker_residue (A := A)).symm).trans
    (RingHom.quotientKerEquivOfSurjective A.residue_surjective)
  commutes' r := (IsScalarTower.algebraMap_apply Λ A k r).symm

@[simp]
lemma residueEquiv_residue_apply {x : A} :
    A.residueEquiv (IsLocalRing.residue A x) = A.residue x := rfl

/-- The type of morphisms in `LocAlgCat`. A morphism consists of a local algebra map
compatible with the residue maps. -/
@[ext]
structure Hom (A B : LocAlgCat.{w} Λ k) where
  /-- The underlying algebra map. -/
  toAlgHom : A →ₐ[Λ] B
  -- We do not use `IsLocalHom` to avoid introducing `IsLocalHom` instances for `AlgHom`.
  comap_maximalIdeal_eq : (maximalIdeal B).comap toAlgHom = maximalIdeal A
  residue_comp : B.residue.comp toAlgHom = A.residue

instance : Category (LocAlgCat.{w} Λ k) where
  Hom A B := Hom A B
  id A := ⟨AlgHom.id Λ A, by simp, by simp⟩
  comp {A B C} f g := ⟨g.toAlgHom.comp f.toAlgHom, by
    rw [← Ideal.comap_comapₐ, g.comap_maximalIdeal_eq, f.comap_maximalIdeal_eq] , by
    rw [← AlgHom.comp_assoc, g.residue_comp, f.residue_comp]⟩

lemma Hom.isLocalHom_toAlgHom (f : A ⟶ B) : IsLocalHom f.toAlgHom := by
  have := (((local_hom_TFAE (f.toAlgHom : A →+* B)).out 0 4).mpr (by
    rw [Ideal.comap_coe, f.comap_maximalIdeal_eq]))
  exact ⟨this.map_nonunit⟩

lemma Hom.map_maximalIdeal_le (f : A ⟶ B) :
    (maximalIdeal A).map f.toAlgHom ≤ maximalIdeal B := by
  have := (local_hom_TFAE f.toAlgHom.toRingHom).out 4 2
  rw [AlgHom.toRingHom_eq_coe, Ideal.comap_coe, Ideal.map_coe] at this
  rw [← this]; exact f.comap_maximalIdeal_eq

/-- Typecheck an `AlgHom` compatible with residue maps as a morphism in `LocAlgCat`. -/
abbrev ofHom (f : X →ₐ[Λ] Y) (h : (maximalIdeal Y).comap f = maximalIdeal X)
    (h' : (of Λ k Y hY).residue.comp f = (of Λ k X hX).residue) : of Λ k X hX ⟶ of Λ k Y hY :=
  ⟨f, h, h'⟩

@[simp]
lemma ofhom_toAlgHom (f : A ⟶ B) : ofHom f.toAlgHom f.comap_maximalIdeal_eq f.residue_comp = f :=
  rfl

@[simp]
lemma hom_id : (𝟙 A : A ⟶ A).toAlgHom = AlgHom.id Λ A := rfl

@[simp]
lemma toAlgHom_comp (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).toAlgHom = g.toAlgHom.comp f.toAlgHom :=
  rfl

@[simp]
lemma ofHom_id : ofHom (.id Λ X) (by simp) (by simp) = 𝟙 (of Λ k X hX) := rfl

@[simp]
lemma ofHom_comp (f : X →ₐ[Λ] Y) (hf : (maximalIdeal Y).comap f = maximalIdeal X)
    (hf' : (of Λ k Y hY).residue.comp f = (of Λ k X hX).residue) (g : Y →ₐ[Λ] Z)
    (hg : (maximalIdeal Z).comap g = maximalIdeal Y)
    (hg' : (of Λ k Z hZ).residue.comp g = (of Λ k Y hY).residue) : ofHom (g.comp f)
      (by rw [← Ideal.comap_comapₐ, hg, hf] ) (by rw [← AlgHom.comp_assoc, hg', hf']) =
        ofHom f hf hf' ≫ ofHom g hg hg' := rfl

lemma ofHom_toAlgHom_apply (f : X →ₐ[Λ] Y) (h : (maximalIdeal Y).comap f = maximalIdeal X)
    (h' : (of Λ k Y hY).residue.comp f = (of Λ k X hX).residue) (x : X) :
    (ofHom f h h').toAlgHom x = f x := rfl

@[simp]
lemma inv_hom_apply (e : A ≅ B) (x : A) : e.inv.toAlgHom (e.hom.toAlgHom x) = x := by
  simp [← AlgHom.comp_apply, ← toAlgHom_comp]

@[simp]
lemma hom_inv_apply (e : A ≅ B) (x : B) : e.hom.toAlgHom (e.inv.toAlgHom x) = x := by
  simp [← AlgHom.comp_apply, ← toAlgHom_comp]

/-- Build an isomorphism in the category `LocAlgCat` from an `AlgEquiv` between `Λ`-algebras. -/
@[simps]
def isoMk {X Y : Type w} {_ : CommRing X} {_ : IsLocalRing X} {_ : Algebra Λ X} {_ : CommRing Y}
    {_ : IsLocalRing Y} {_ : Algebra Λ Y} {_ : Algebra X k} {_ : Algebra Y k}
    {_ : IsScalarTower Λ X k} {_ : IsScalarTower Λ Y k} {hX : Surjective (algebraMap X k)}
    {hY : Surjective (algebraMap Y k)} (e : X ≃ₐ[Λ] Y) (he : (of Λ k Y hY).residue.comp e =
      (of Λ k X hX).residue) : of Λ k X hX ≅ of Λ k Y hY where
  hom := ofHom (e : X →ₐ[Λ] Y) (by ext; simp) (by rw [← he])
  inv := ofHom (e.symm : Y →ₐ[Λ] X) (by ext; simp) (by ext; simp [← he])
  inv_hom_id := by simp [← ofHom_comp]
  hom_inv_id := by simp [← ofHom_comp]

/-- Build an `AlgEquiv` from an isomorphism in the category `LocAlgCat Λ k`. -/
@[simps]
def ofIso (i : A ≅ B) : A ≃ₐ[Λ] B where
  __ := i.hom.toAlgHom
  toFun := i.hom.toAlgHom
  invFun := i.inv.toAlgHom
  left_inv x := by simp
  right_inv x := by simp

@[simp]
lemma residue_comp_coe_ofIso (i : A ≅ B) : B.residue.comp (ofIso i) = A.residue := by
  ext
  simpa using DFunLike.congr_fun i.hom.residue_comp _

/-- Algebra equivalences compatible with residue maps are the same as
isomorphisms in `LocAlgCat`. -/
@[simps]
def isoEquivSubtypeAlgEquiv : (of Λ k X hX ≅ of Λ k Y hY) ≃
    { e : X ≃ₐ[Λ] Y // (of Λ k Y hY).residue.comp e = (of Λ k X hX).residue } where
  toFun i := ⟨ofIso i, residue_comp_coe_ofIso i⟩
  invFun f := isoMk f.val f.prop

variable (Λ k) in
/-- Universe lift functor for `LocAlgCat`. -/
def uliftFunctor : LocAlgCat.{w} Λ k ⥤ LocAlgCat.{max w w'} Λ k where
  obj A :=
    letI : Algebra (ULift.{w'} A) k := ULift.algebra' ..
    haveI : IsScalarTower Λ (ULift.{w'} A) k := ULift.isScalarTower' ..
    of Λ k (ULift.{w'} A) (fun r ↦ by simpa using A.surj r)
  map {A B} f :=
    letI : Algebra (ULift.{w'} A) k := ULift.algebra' ..
    haveI : IsScalarTower Λ (ULift.{w'} A) k := ULift.isScalarTower' ..
    letI : Algebra (ULift.{w'} B) k := ULift.algebra' ..
    haveI : IsScalarTower Λ (ULift.{w'} B) k := ULift.isScalarTower' ..
    ofHom (ULift.algEquiv.symm.toAlgHom.comp <| f.toAlgHom.comp ULift.algEquiv.toAlgHom) (by
      have := f.isLocalHom_toAlgHom
      ext; simp) (by ext x; simpa using DFunLike.congr_fun f.residue_comp x.down)

variable (Λ k) in
/-- The universe lift functor for `LocAlgCat` is fully faithful. -/
def fullyFaithfulUliftFunctor : (uliftFunctor Λ k).FullyFaithful where
  preimage {A B} f :=
    letI : Algebra (ULift.{w'} A) k := ULift.algebra' ..
    haveI : IsScalarTower Λ (ULift.{w'} A) k := ULift.isScalarTower' ..
    letI : Algebra (ULift.{w'} B) k := ULift.algebra' ..
    haveI : IsScalarTower Λ (ULift.{w'} B) k := ULift.isScalarTower' ..
    letI F : ULift A →ₐ[Λ] ULift B := f.toAlgHom
    ofHom (ULift.algEquiv.toAlgHom.comp <| F.comp ULift.algEquiv.symm.toAlgHom) (by
      have : IsLocalHom F := f.isLocalHom_toAlgHom
      ext; simp) (AlgHom.ext fun x ↦ by
        have := DFunLike.congr_fun f.residue_comp
        simp only [uliftFunctor, AlgEquiv.toAlgHom_eq_coe, coe_of, ULift.forall] at this
        exact this x)

instance : (uliftFunctor Λ k).Full := (fullyFaithfulUliftFunctor Λ k).full

instance : (uliftFunctor Λ k).Faithful := (fullyFaithfulUliftFunctor Λ k).faithful

----------------------------------------------------------------------------------------------

lemma exists_mem_maximalIdeal_toAlgHom_apply_add_eq (f : A ⟶ C) (g : B ⟶ C) (a : A)
    (hf : Surjective f.toAlgHom) : ∃ (b : B) (m : A), m ∈ maximalIdeal A ∧
      f.toAlgHom (a + m) = g.toAlgHom b := by
  rcases B.residue_surjective (residue A a) with ⟨b, hb⟩
  rw [← g.residue_comp, ← f.residue_comp, AlgHom.comp_apply, AlgHom.comp_apply, ← sub_eq_zero,
    ← map_sub, residue_eq_zero_iff, ← map_maximalIdeal_of_surjective (f.toAlgHom : A →+* C) hf,
    Ideal.mem_map_iff_of_surjective (f.toAlgHom : A →+* C) hf] at hb
  rcases hb with ⟨m, hm⟩
  simp only [RingHom.coe_coe, eq_sub_iff_add_eq', ← map_add] at hm
  exact ⟨b, m, hm⟩

instance [IsLocalHom (algebraMap Λ k)] : IsLocalHom (algebraMap Λ A) :=
  haveI : IsLocalHom ((algebraMap A k).comp (algebraMap Λ A)) := by
    rwa [← IsScalarTower.algebraMap_eq]
  isLocalHom_of_comp _ (algebraMap A k)

lemma comap_algebraMap_maximalIdeal [IsLocalRing Λ] [IsLocalHom (algebraMap Λ k)] :
    (maximalIdeal A).comap (algebraMap Λ A) = maximalIdeal Λ := by
  have := ((local_hom_TFAE (algebraMap Λ k)).out 0 4).mp ‹_›
  rw [eq_comm, ← this, IsScalarTower.algebraMap_eq Λ A, ← Ideal.comap_comap,
    eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ A.surj)]

lemma map_algebraMap_maximalIdeal_ne_top [IsLocalRing Λ] [IsLocalHom (algebraMap Λ k)] :
    (maximalIdeal Λ).map (algebraMap Λ A) ≠ ⊤ := ne_top_of_le_ne_top
  (maximalIdeal.isMaximal A).ne_top <| ((local_hom_TFAE (algebraMap Λ A)).out 0 2).mp
    (by infer_instance)

section ofQuot

variable {I : Ideal A}

/-- The residue algebra structure on `ofQuot`. -/
instance ofQuotResidueAlgebra (A : LocAlgCat.{w} Λ k) {I : Ideal A} [Nontrivial (A ⧸ I)] :
    Algebra (A ⧸ I) k := (Ideal.Quotient.lift I (algebraMap A k) fun a a_in ↦ by
  rw [← residue_apply, residue_eq_zero_iff]
  exact le_maximalIdeal (by rwa [← Ideal.Quotient.nontrivial_iff]) a_in).toAlgebra

instance isScalarTower_ofQuotResidueAlgebra [Nontrivial (A ⧸ I)] : IsScalarTower Λ (A ⧸ I) k :=
  .of_algebraMap_eq fun r ↦ by rw [IsScalarTower.algebraMap_apply Λ A (A ⧸ I),
    Ideal.Quotient.algebraMap_eq, RingHom.algebraMap_toAlgebra, Ideal.Quotient.lift_mk,
    IsScalarTower.algebraMap_apply Λ A]

instance isScalarTower_ofQuotResidueAlgebra' [Nontrivial (A ⧸ I)] : IsScalarTower A (A ⧸ I) k :=
  .of_algebraMap_eq fun _ ↦ by rw [RingHom.algebraMap_toAlgebra, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.lift_mk]

/-- The quotient of an object `A` in `LocAlgCat` by a proper ideal `I`. -/
def ofQuot (A : LocAlgCat.{w} Λ k) (I : Ideal A) [Nontrivial (A ⧸ I)] : LocAlgCat.{w} Λ k :=
  letI : IsLocalRing (A ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  of Λ k (A ⧸ I) (Surjective.of_comp (g := Ideal.Quotient.mk _) (by
    rw [← RingHom.coe_comp, RingHom.algebraMap_toAlgebra, Ideal.Quotient.lift_comp_mk]
    exact A.surj))

@[simp]
lemma residue_ofQuot_mk_apply [Nontrivial (A ⧸ I)] (a : A) :
    (A.ofQuot I).residue (Ideal.Quotient.mk I a) = A.residue a := rfl

instance algebraOfQuot (A : LocAlgCat.{w} Λ k) {I : Ideal A} [Nontrivial (A ⧸ I)] :
    Algebra A (A.ofQuot I) := Ideal.Quotient.algebra _

instance isScalarTower_algebraOfQuot (A : LocAlgCat.{w} Λ k) {I : Ideal A} [Nontrivial (A ⧸ I)] :
    IsScalarTower Λ A (A.ofQuot I) := .of_algebraMap_eq fun _ ↦ rfl

/-- Upgrades the canonical quotient map from `A` to `A ⧸ I` to a morphism in `LocAlgCat`. -/
def toOfQuot (A : LocAlgCat.{w} Λ k) (I : Ideal A) [Nontrivial (A ⧸ I)] : A ⟶ A.ofQuot I :=
  letI : IsLocalRing (A ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  ofHom (IsScalarTower.toAlgHom Λ A (A ⧸ I)) (eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective
    _ Ideal.Quotient.mk_surjective)) (by ext; simpa [residue] using residue_ofQuot_mk_apply ..)

@[simp]
lemma toAlgHom_toOfQuot_apply [Nontrivial (A ⧸ I)] (a : A) :
    (A.toOfQuot I).toAlgHom a = Ideal.Quotient.mk I a := rfl

@[simp]
lemma ker_toAlgHom_toOfQuot [Nontrivial (A ⧸ I)] : RingHom.ker (A.toOfQuot I).toAlgHom = I :=
  Ideal.mk_ker

lemma surjective_toAlgHom_toOfQuot [Nontrivial (A ⧸ I)] : Surjective (A.toOfQuot I).toAlgHom :=
  Ideal.Quotient.mk_surjective

theorem map_toAlgHom_toOfQuot_maximalIdeal_eq [Nontrivial (A ⧸ I)] :
    (maximalIdeal A).map (A.toOfQuot I).toAlgHom = maximalIdeal (A.ofQuot I) := eq_maximalIdeal (by
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective _ (surjective_toAlgHom_toOfQuot (I := I))
    (maximalIdeal.isMaximal A) with h' | _
  · rw [← (Ideal.comap_injective_of_surjective _ surjective_toAlgHom_toOfQuot).eq_iff,
      Ideal.comap_top, Ideal.comap_map_of_surjective' _ surjective_toAlgHom_toOfQuot,
      ker_toAlgHom_toOfQuot, sup_eq_left.mpr (le_maximalIdeal
        (by rwa [← Ideal.Quotient.nontrivial_iff]))] at h'
    have := (maximalIdeal.isMaximal A).ne_top
    contradiction
  · assumption)

/-- The morphism between quotient objects in `LocAlgCat` induced by a morphism `f : A ⟶ B`.
This is the categorical counterpart to `Ideal.quotientMapₐ`. -/
def mapOfQuot (f : A ⟶ B) {J : Ideal B} [Nontrivial (A ⧸ I)] [Nontrivial (B ⧸ J)]
    (hf : I ≤ J.comap f.toAlgHom) : A.ofQuot I ⟶ B.ofQuot J :=
  haveI : IsLocalRing (A ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  haveI : IsLocalRing (B ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective
  ofHom (Ideal.quotientMapₐ J f.toAlgHom hf) (by
    rw [← (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective).eq_iff,
      ← Ideal.comap_coe (Ideal.quotientMapₐ J f.toAlgHom hf), Ideal.comap_comap]
    change Ideal.comap (((Ideal.quotientMap J f.toAlgHom hf)).comp (Ideal.Quotient.mk I))
      (maximalIdeal (B ⧸ J)) = _
    rw [Ideal.quotientMap_comp_mk, ← Ideal.comap_comap, Ideal.comap_coe, eq_maximalIdeal
      (Ideal.comap_isMaximal_of_surjective ((Ideal.Quotient.mk J)) Ideal.Quotient.mk_surjective),
        f.comap_maximalIdeal_eq, eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective
          (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective)] ) (AlgHom.ext fun x ↦ by
    rcases Ideal.Quotient.mk_surjective x with ⟨x, rfl⟩
    exact DFunLike.congr_fun f.residue_comp x )

@[simp, reassoc]
theorem toOfQuot_comp_mapOfQuot (f : A ⟶ B) {J : Ideal B} [Nontrivial (A ⧸ I)] [Nontrivial (B ⧸ J)]
    (hf : I ≤ J.comap f.toAlgHom) : A.toOfQuot I ≫ mapOfQuot f hf = f ≫ B.toOfQuot J := rfl

@[simp]
lemma toAlgHom_mapOfQuot_apply (f : A ⟶ B) {J : Ideal B} [Nontrivial (A ⧸ I)] [Nontrivial (B ⧸ J)]
    (hf : I ≤ J.comap f.toAlgHom) (a : A) : (mapOfQuot f hf).toAlgHom (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk J (f.toAlgHom a) := rfl

/-- The quotient of a local algebra by the `n`-th power of its maximal ideal.
Geometrically, this represents an infinitesimal neighborhood of the closed point. -/
abbrev infinitesimalNeighborhood {n : ℕ} (hn : n ≠ 0) (A : LocAlgCat.{w} Λ k) : LocAlgCat Λ k :=
  letI : Nontrivial (A ⧸ (maximalIdeal A) ^ n) := by
    rw [Ideal.Quotient.nontrivial_iff, Ideal.ne_top_iff_exists_maximal]
    exact ⟨maximalIdeal A, maximalIdeal.isMaximal A, Ideal.pow_le_self hn⟩
  A.ofQuot (maximalIdeal A ^ n)

/-- The canonical quotient morphism from `A` to its infinitesimal neighborhood. -/
abbrev toInfinitesimalNeighborhood {n : ℕ} (hn : n ≠ 0) (A : LocAlgCat.{w} Λ k) :
    A ⟶ A.infinitesimalNeighborhood hn :=
  letI : Nontrivial (A ⧸ (maximalIdeal A) ^ n) := by
    rw [Ideal.Quotient.nontrivial_iff, Ideal.ne_top_iff_exists_maximal]
    exact ⟨maximalIdeal A, maximalIdeal.isMaximal A, Ideal.pow_le_self hn⟩
  toOfQuot ..

/-- The morphism between infinitesimal neighborhoods induced by a morphism in `LocAlgCat`. -/
abbrev mapInfinitesimalNeighborhood {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hmn : n ≤ m) (f : A ⟶ B) :
    A.infinitesimalNeighborhood hm ⟶ B.infinitesimalNeighborhood hn :=
  letI : Nontrivial (A ⧸ (maximalIdeal A) ^ m) := by
    rw [Ideal.Quotient.nontrivial_iff, Ideal.ne_top_iff_exists_maximal]
    exact ⟨maximalIdeal A, maximalIdeal.isMaximal A, Ideal.pow_le_self hm⟩
  letI : Nontrivial (B ⧸ (maximalIdeal B) ^ n) := by
    rw [Ideal.Quotient.nontrivial_iff, Ideal.ne_top_iff_exists_maximal]
    exact ⟨maximalIdeal B, maximalIdeal.isMaximal B, Ideal.pow_le_self hn⟩
  mapOfQuot f (le_trans (Ideal.pow_le_pow_right hmn) (f.comap_maximalIdeal_eq ▸
      Ideal.le_comap_pow f.toAlgHom n))

/-- The special fiber of `A` over `Λ` when `Λ` is a local ring, defined as the quotient by
the extended maximal ideal of `Λ`, viewed as an object in `LocAlgCat`. -/
abbrev specialFiber [IsLocalRing Λ] [IsLocalHom (algebraMap Λ k)]
    (A : LocAlgCat.{w} Λ k) : LocAlgCat.{w} Λ k :=
  letI : Nontrivial (A ⧸ (maximalIdeal Λ).map (algebraMap Λ A)) :=
    Ideal.Quotient.nontrivial_iff.mpr map_algebraMap_maximalIdeal_ne_top
  A.ofQuot ((maximalIdeal Λ).map (algebraMap Λ A))

/-- The canonical morphism from `A` to its special fiber. -/
abbrev toSpecialFiber [IsLocalRing Λ] [IsLocalHom (algebraMap Λ k)]
    (A : LocAlgCat.{w} Λ k) : A ⟶ A.specialFiber :=
  letI : Nontrivial (A ⧸ (maximalIdeal Λ).map (algebraMap Λ A)) :=
    Ideal.Quotient.nontrivial_iff.mpr map_algebraMap_maximalIdeal_ne_top
  toOfQuot ..

/-- The morphism between special fibers induced by a morphism between two objects. -/
abbrev mapSpecialFiber [IsLocalRing Λ] [IsLocalHom (algebraMap Λ k)]
    (f : A ⟶ B) : A.specialFiber ⟶ B.specialFiber :=
  letI : Nontrivial (A ⧸ (maximalIdeal Λ).map (algebraMap Λ A)) :=
    Ideal.Quotient.nontrivial_iff.mpr map_algebraMap_maximalIdeal_ne_top
  letI : Nontrivial (B ⧸ (maximalIdeal Λ).map (algebraMap Λ B)) :=
    Ideal.Quotient.nontrivial_iff.mpr map_algebraMap_maximalIdeal_ne_top
  mapOfQuot f (by rw [Ideal.map_le_iff_le_comap, ← Ideal.comap_coe f.toAlgHom,
    Ideal.comap_comap, AlgHom.comp_algebraMap, ← Ideal.map_le_iff_le_comap])

@[simp]
lemma algebraMap_specialFiber_apply_eq_zero [IsLocalRing Λ] [IsLocalHom (algebraMap Λ k)]
    (A : LocAlgCat.{w} Λ k) {y : Λ} (y_in : y ∈ maximalIdeal Λ) :
    algebraMap Λ A.specialFiber y = 0 := by
  rw [IsScalarTower.algebraMap_apply Λ A A.specialFiber]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ y_in)

end ofQuot

section ofPullback

/-- Given morphisms `f : A ⟶ C` and `g : B ⟶ C` in `LocAlgCat`
where `g.toAlgHom` is surjective, `ofPullback f g h` constructs the pullback
`AlgHom.pullback f.toAlgHom g.toAlgHom` as an object in `LocAlgCat`. -/
abbrev ofPullback (f : A ⟶ C) (g : B ⟶ C) (h : Surjective g.toAlgHom) : LocAlgCat.{w} Λ k :=
  letI : Algebra (f.toAlgHom.pullback g.toAlgHom) k :=
    (A.residue.comp (f.toAlgHom.pullbackFst g.toAlgHom)).toAlgebra
  letI : IsScalarTower Λ (f.toAlgHom.pullback g.toAlgHom) k := .of_algebraMap_eq (by
    simp [RingHom.algebraMap_toAlgebra])
  letI : IsLocalRing ↥(f.toAlgHom.pullback g.toAlgHom) :=
    isLocalRing_algHomPullback f.toAlgHom g.toAlgHom ⟨h.isLocalHom.map_nonunit⟩
  of Λ k (f.toAlgHom.pullback g.toAlgHom) (by
    simpa [RingHom.algebraMap_toAlgebra] using Surjective.comp A.surj
      (AlgHom.surjective_pullbackFst_of_surjective _ _ h))

@[simp]
lemma residue_ofPullback (f : A ⟶ C) (g : B ⟶ C) (h : Surjective g.toAlgHom)
    (u : f.toAlgHom.pullback g.toAlgHom) : (ofPullback f g h).residue u = A.residue u.val.1 := by
  simp [residue, RingHom.algebraMap_toAlgebra]

/-- Upgrades the first projection map from the pullback algebra to a morphism in `LocAlgCat`. -/
abbrev fromOfPullback (f : A ⟶ C) (g : B ⟶ C) (h : Surjective g.toAlgHom) :
    ofPullback f g h ⟶ A :=
  letI : IsLocalRing ↥(f.toAlgHom.pullback g.toAlgHom) :=
    isLocalRing_algHomPullback f.toAlgHom g.toAlgHom ⟨h.isLocalHom.map_nonunit⟩
  .mk (f.toAlgHom.pullbackFst g.toAlgHom) (eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _
    (AlgHom.surjective_pullbackFst_of_surjective f.toAlgHom g.toAlgHom h))) rfl

open Polynomial in
private lemma not_isUnit_aeval_of_aeval_eq_zero [IsLocalRing Λ] [Algebra.IsIntegral Λ k] (x : k)
    {a : A} {p : (ResidueField Λ)[X]} {q : Λ[X]} (hp : aeval x p = 0)
    (hq : q.map (IsLocalRing.residue Λ) = p) (ha : algebraMap A k a = x) :
    ¬ IsUnit (aeval a q) := fun h ↦ by
  replace h := IsUnit.map (algebraMap A k) h
  have : algebraMap A k (aeval a q) = 0 := by
    rw [← aeval_algebraMap_apply, ha, ← Polynomial.aeval_map_algebraMap (ResidueField Λ),
    ResidueField.algebraMap_eq, hq, hp]
  simp [this] at h

open Polynomial in
private lemma isUnit_aeval_derivative_of_isSeparable [IsLocalRing Λ] [Algebra.IsIntegral Λ k]
    {x : k} {a : A} {q : Λ[X]} (hx : IsSeparable (ResidueField Λ) x)
    (hq : q.map (IsLocalRing.residue Λ) = minpoly (ResidueField Λ) x) (ha : residue A a = x) :
    IsUnit (aeval a (derivative q)) := by
  rw [← notMem_maximalIdeal, ← ker_residue, RingHom.mem_ker, ← RingHom.coe_coe, aeval_def,
    hom_eval₂, AlgHom.comp_algebraMap_of_tower, RingHom.coe_coe, ← Polynomial.eval_map,
    IsScalarTower.algebraMap_eq Λ (ResidueField Λ) k, ← map_map, ResidueField.algebraMap_eq,
    ← derivative_map, hq, Polynomial.eval_map, ← aeval_def, ha]
  exact hx.aeval_derivative_ne_zero (minpoly.aeval (ResidueField Λ) x)

open Polynomial in
@[stacks 06GH "(3)"]
theorem surjective_residue_comp_pullbackFst_of_isSeparable [IsLocalRing Λ] [Module.Finite Λ k]
    [HenselianRing A (maximalIdeal A)] [HenselianRing B (maximalIdeal B)]
    [Algebra.IsSeparable (ResidueField Λ) k] (f : A ⟶ C) (g : B ⟶ C) :
    Surjective (A.residue.comp (f.toAlgHom.pullbackFst g.toAlgHom)) := by
  obtain ⟨x, hx⟩ := Field.exists_primitive_element (ResidueField Λ) k
  let p := minpoly (ResidueField Λ) x
  obtain ⟨q, map_q, deg_q, monic_q⟩ := lifts_and_natDegree_eq_and_monic
    (show p ∈ lifts (IsLocalRing.residue Λ) by
      rw [lifts_iff_coeff_lifts]; intro; exact IsLocalRing.residue_surjective _)
    (minpoly.monic (Algebra.IsIntegral.isIntegral x))
  obtain ⟨a', ha⟩ := A.residue_surjective x
  obtain ⟨a, a_rt, a_sub⟩ := HenselianRing.is_henselian (R := A) (I := maximalIdeal A)
    (q.map (algebraMap Λ A)) (Monic.map _ monic_q) a' (by
      simpa using LocAlgCat.not_isUnit_aeval_of_aeval_eq_zero x (minpoly.aeval (ResidueField Λ) x)
        map_q ha)
    (by change IsUnit ((IsLocalRing.residue A) _); simpa using
        LocAlgCat.isUnit_aeval_derivative_of_isSeparable (Algebra.IsSeparable.isSeparable
          (ResidueField Λ) x) map_q ha)
  replace ha : A.residue a = x := by
    rw [← sub_add_cancel a a', map_add, ha, LocAlgCat.residue_eq_zero_iff.mpr a_sub, zero_add]
  obtain ⟨b', hb⟩ := B.residue_surjective x
  obtain ⟨b, b_rt, b_sub⟩ := HenselianRing.is_henselian (R := B) (I := maximalIdeal B)
    (q.map (algebraMap Λ B)) (Monic.map _ monic_q) b' (by
      simpa using LocAlgCat.not_isUnit_aeval_of_aeval_eq_zero x (minpoly.aeval (ResidueField Λ) x)
        map_q hb)
    (by change IsUnit ((IsLocalRing.residue B) _); simpa using
        LocAlgCat.isUnit_aeval_derivative_of_isSeparable
          (Algebra.IsSeparable.isSeparable (ResidueField Λ) x) map_q hb)
  replace hb : B.residue b = x := by
    rw [← sub_add_cancel b b', map_add, hb, LocAlgCat.residue_eq_zero_iff.mpr b_sub, zero_add]
  clear a' a_sub b' b_sub
  have hab : f.toAlgHom a = g.toAlgHom b := by
    simp only [IsRoot.def, eval_map_algebraMap, aeval_def] at a_rt b_rt
    apply DFunLike.congr_arg f.toAlgHom at a_rt
    apply DFunLike.congr_arg g.toAlgHom at b_rt
    rw [algHom_eval₂_algebraMap, map_zero, eval₂_eq_eval_map] at a_rt b_rt
    refine eq_of_eval_eq_zero_of_not_isUnit_sub a_rt b_rt ?_ ?_
    · rw [← notMem_maximalIdeal, not_not, ← LocAlgCat.residue_eq_zero_iff, map_sub, sub_eq_zero,
        ← AlgHom.comp_apply, ← AlgHom.comp_apply, f.residue_comp, g.residue_comp, ha, hb]
    · rw [derivative_map, eval_map_algebraMap]
      exact LocAlgCat.isUnit_aeval_derivative_of_isSeparable
        (Algebra.IsSeparable.isSeparable (ResidueField Λ) x) map_q (by
          rwa [← AlgHom.comp_apply, f.residue_comp])
  apply Algebra.adjoin_eq_top_of_primitive_element (Algebra.IsAlgebraic.isAlgebraic x) at hx
  simp only [SetLike.ext_iff, Algebra.mem_top, iff_true] at hx
  intro y
  simp only [AlgHom.coe_comp, Subalgebra.coe_val, Function.comp_apply, AlgHom.fst_apply,
    Subtype.exists, AlgHom.mem_equalizer, AlgHom.snd_apply, exists_prop, Prod.exists,
    exists_and_right]
  obtain ⟨r, hr⟩ := Algebra.adjoin_eq_exists_aeval (ResidueField Λ) x ⟨y, hx y⟩
  obtain ⟨r, rfl⟩ :=
    map_surjective (algebraMap Λ (ResidueField Λ)) IsLocalRing.residue_surjective r
  rw [aeval_map_algebraMap] at hr
  exact ⟨aeval a r, ⟨aeval b r, by simp [aeval_def, hab]⟩, by simpa [aeval_def, ha]⟩

end ofPullback

section ArtinianRing

variable [IsLocalRing Λ] [Module.Finite Λ k]

open Module in
@[stacks 06GG]
theorem finrank_mul_length {M : Type*} [AddCommGroup M] [Module A M] [Module Λ M]
    [IsScalarTower Λ A M] : finrank (ResidueField Λ) k * length A M = length Λ M := by
  have : (finrank (ResidueField Λ) k : ENat) ≠ 0 := by
    rw [ne_eq, ← Nat.cast_zero (R := ENat), ENat.coe_inj, finrank_eq_zero_iff_of_free,
      not_subsingleton_iff_nontrivial]
    infer_instance
  by_cases h : length A M = ⊤
  · rw [h, ENat.mul_top this, eq_comm, eq_top_iff, ← h]
    have := Submodule.length_le_length_restrictScalar Λ A M ⊤
    rwa [length_top, Submodule.restrictScalars_top, length_top] at this
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = length A M := ENat.ne_top_iff_exists.mp h
  revert M; induction n using Nat.strong_induction_on with
  | h n ih =>
    intro M _ _ _ _ ne_top hn
    by_cases h : n = 0
    · rw [h, Nat.cast_zero, eq_comm] at hn
      rw [hn, mul_zero, eq_comm, Module.length_eq_zero_iff]
      rwa [length_eq_zero_iff] at hn
    have : Nontrivial M := by
      rwa [← ENat.coe_inj, hn, Nat.cast_zero, length_eq_zero_iff,
        not_subsingleton_iff_nontrivial] at h
    by_cases h' : ∃ (x : M), x ≠ 0 ∧ ¬ Function.Surjective (LinearMap.toSpanSingleton A M x)
    · rcases h' with ⟨x, x_ne, hx⟩
      rw [← LinearMap.range_eq_top, LinearMap.range_toSpanSingleton] at hx
      let N := Submodule.span A {x}
      let Q := M ⧸ N
      have eq_add := Module.length_eq_add_of_exact N.subtype N.mkQ N.subtype_injective
        N.mkQ_surjective (LinearMap.exact_subtype_mkQ N)
      have eq_add' := Module.length_eq_add_of_exact (N.restrictScalars Λ).subtype
        (N.restrictScalars Λ).mkQ N.subtype_injective N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N)
      rw [← ne_eq, ← lt_top_iff_ne_top, eq_add, ENat.add_lt_top, lt_top_iff_ne_top,
        lt_top_iff_ne_top] at ne_top
      obtain ⟨m, hm⟩ : ∃ m : ℕ, m = length A N := ENat.ne_top_iff_exists.mp ne_top.left
      obtain ⟨l, hl⟩ : ∃ l : ℕ, l = length A Q := ENat.ne_top_iff_exists.mp ne_top.right
      have m_ne : m ≠ 0 := by
        rw [ne_eq, ← ENat.coe_inj, Nat.cast_zero, hm, length_eq_zero_iff,
          Submodule.subsingleton_iff_eq_bot, Submodule.span_eq_bot]
        simpa
      rw [eq_add, ← hm, ← hl] at hn; norm_cast at hn
      have ih_l := ih l (by lia) (by rw [← hl]; simp) hl
      have l_ne : l ≠ 0 := by
        rwa [ne_eq, ← ENat.coe_inj, Nat.cast_zero, hl, length_eq_zero_iff,
          Submodule.Quotient.subsingleton_iff]
      have ih_m := ih m (by lia) (by rw [← hm]; simp) hm
      rw [eq_add, eq_add', ← hl, ← hm]; norm_cast
      rw [Nat.mul_add]; push_cast
      rw [hl, hm, ih_m, ih_l]; congr
    replace h' : IsSimpleModule A M := by
      rw [isSimpleModule_iff_toSpanSingleton_surjective]
      push Not at h'; exact ⟨this, h'⟩
    rw [length_eq_one, mul_one]
    rw [isSimpleModule_iff_quot_maximal] at h'
    rcases h' with ⟨I, hI, h'⟩
    replace h' : Nonempty (M ≃ₗ[Λ] k) := by
      rcases h' with ⟨e⟩
      replace hI := (isMaximal_iff A).mp hI
      let f : (A ⧸ I) ≃ₐ[Λ] ResidueField A :=
        Ideal.quotientEquivAlg I (maximalIdeal A) (AlgEquiv.refl (R := Λ)) (by simp [hI])
      exact ⟨(e.restrictScalars Λ).trans <| f.toLinearEquiv.trans A.residueEquiv.toLinearEquiv⟩
    rcases h' with ⟨e⟩
    rw [e.length_eq, ← Module.length_eq_finrank, eq_comm]
    exact Module.length_eq_of_surjective IsLocalRing.residue_surjective

variable (A) in
theorem isFiniteLength_of_isArtinianRing [IsArtinianRing A] : IsFiniteLength Λ A := by
  rw [← Module.length_ne_top_iff, ← finrank_mul_length (A := A)]
  have (n : ℕ) (s : ENat) (hs : s ≠ ⊤) : n * s ≠ ⊤ := by
    lift s to ℕ using hs
    exact WithTop.coe_ne_top
  exact this _ _ Module.length_ne_top

instance [IsArtinianRing A] : IsNoetherian Λ A :=
  (isFiniteLength_iff_isNoetherian_isArtinian.mp (isFiniteLength_of_isArtinianRing A)).left

instance [IsArtinianRing A] : IsArtinian Λ A :=
  (isFiniteLength_iff_isNoetherian_isArtinian.mp (isFiniteLength_of_isArtinianRing A)).right

instance isArtinianRing_pullback [IsArtinianRing A] [IsArtinianRing B] (f : A ⟶ C) (g : B ⟶ C) :
    IsArtinianRing (f.toAlgHom.pullback g.toAlgHom) := by
  set PB := f.toAlgHom.pullback g.toAlgHom
  rw [isArtinianRing_iff_isFiniteLength, ← Module.length_ne_top_iff]
  refine ne_top_of_le_ne_top (b := Module.length Λ PB) ?_ ?_
  · refine ne_top_of_le_ne_top (b := Module.length Λ (A × B)) ?_ ?_
    · rw [Module.length_prod]
      exact WithTop.add_ne_top.mpr ⟨Module.length_ne_top, Module.length_ne_top⟩
    · exact Module.length_le_of_injective (Submodule.subtype PB.toSubmodule)
        (Submodule.subtype_injective _)
  have := Submodule.length_le_length_restrictScalar Λ PB PB ⊤
  rwa [Module.length_top, Submodule.restrictScalars_top, Module.length_top] at this

end ArtinianRing

---------------------------------------------------------------------------------

noncomputable section Cotangent

open scoped TensorProduct

instance : Module k (CotangentSpace A) := .compHom _ (A.residueEquiv.symm : k →+* ResidueField A)

lemma smul_cotangent_def (r : k) (x : CotangentSpace A) : r • x = (A.residueEquiv.symm r) • x :=
  rfl

lemma residue_smul_cotangent (a : A) (x : CotangentSpace A) : A.residue a • x = a • x := by
  rw [← residueEquiv_residue_apply, smul_cotangent_def, AlgEquiv.symm_apply_apply,
    ← IsLocalRing.ResidueField.algebraMap_eq, IsScalarTower.algebraMap_smul]

instance : IsScalarTower A k (CotangentSpace A) := .of_algebraMap_smul residue_smul_cotangent

instance : IsScalarTower Λ (ResidueField A) (CotangentSpace A) := .of_algebraMap_smul fun r x ↦ by
  rw [IsScalarTower.algebraMap_apply Λ A, IsScalarTower.algebraMap_smul,
    IsScalarTower.algebraMap_smul]

instance : IsScalarTower Λ k (CotangentSpace A) := .of_algebraMap_smul fun r x ↦ by
  rw [smul_cotangent_def, IsScalarTower.algebraMap_eq Λ A, RingHom.comp_apply]
  have := residueEquiv_residue_apply (x := algebraMap Λ A r)
  rw [← AlgEquiv.eq_symm_apply, residue_apply] at this
  rw [← this, ← ResidueField.algebraMap_eq, IsScalarTower.algebraMap_smul,
    IsScalarTower.algebraMap_smul]

/-- The canonical `k`-linear map between cotangent spaces induced by a morphism in `LocAlgCat`. -/
def mapCotangent (f : A ⟶ B) : CotangentSpace A →ₗ[k] CotangentSpace B where
  toFun x := (maximalIdeal A).mapCotangent (maximalIdeal B) f.toAlgHom
    (by rw [f.comap_maximalIdeal_eq]) x
  map_add' := by simp
  map_smul' r x := by
    obtain ⟨s, hs⟩ := A.residue_surjective r
    obtain ⟨t, ht⟩ := B.residue_surjective r
    obtain ⟨x, rfl⟩ := (maximalIdeal A).toCotangent_surjective x
    nth_rw 1 [← hs, ← ht]
    simp only [residue_smul_cotangent, RingHom.id_apply, Ideal.mapCotangent_toCotangent,
      ← map_smul, Ideal.toCotangent_eq]
    simp only [SetLike.val_smul, smul_eq_mul, map_mul, ← sub_mul, pow_two]
    refine Ideal.mul_mem_mul ?_ ?_
    · rwa [← residue_eq_zero_iff, map_sub, sub_eq_zero, ← AlgHom.comp_apply, f.residue_comp, ht]
    · rw [← Ideal.mem_comap]; convert x.prop
      exact f.comap_maximalIdeal_eq

@[simp]
lemma mapCotangent_toCotangent (f : A ⟶ B) (a : maximalIdeal A) :
    mapCotangent f ((maximalIdeal A).toCotangent a) = (maximalIdeal B).toCotangent ⟨f.toAlgHom a,
      by rw [← Ideal.mem_comap, f.comap_maximalIdeal_eq]; exact a.prop⟩ := by simp [mapCotangent]

@[stacks 06S3 "(1) => (2)"]
theorem surjective_mapCotangent_toOfQuot {I : Ideal A} [Nontrivial (A ⧸ I)] :
    Surjective (mapCotangent (A.toOfQuot I)) := by
  have : RingHom.ker (algebraMap A (A.ofQuot I)) ≤ maximalIdeal A := le_maximalIdeal (by
    change RingHom.ker (A.toOfQuot I).toAlgHom ≠ _
    rwa [ker_toAlgHom_toOfQuot, ← Ideal.Quotient.nontrivial_iff])
  refine Ideal.mapCotangent_surjective_of_comap_eq (fun _ ↦ Ideal.Quotient.mk_surjective _) ?_
  rw [sup_eq_right.mpr this]
  exact (A.toOfQuot I).comap_maximalIdeal_eq

section IsLocalRing

variable [IsLocalRing Λ]

instance [Algebra.IsIntegral Λ k] : Module (ResidueField Λ) (CotangentSpace A) :=
  .restrictScalars (ResidueField Λ) k (CotangentSpace A)

lemma residueField_smul_cotangent [Algebra.IsIntegral Λ k] (r : ResidueField Λ)
    (x : CotangentSpace A) : r • x = (algebraMap (ResidueField Λ) k r) • x := rfl

instance [Algebra.IsIntegral Λ k] : IsScalarTower (ResidueField Λ) k (CotangentSpace A) :=
  .restrictScalars ..

instance [Algebra.IsIntegral Λ k] : IsScalarTower Λ (ResidueField Λ) (CotangentSpace A) :=
  .of_algebraMap_smul fun _ _ ↦ by rw [residueField_smul_cotangent,
    ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_smul]

theorem surjective_mapCotangent_toSpecialFiber [IsLocalHom (algebraMap Λ k)] :
    Surjective (mapCotangent A.toSpecialFiber) :=
  letI : Nontrivial (A ⧸ (maximalIdeal Λ).map (algebraMap Λ A)) :=
    Ideal.Quotient.nontrivial_iff.mpr map_algebraMap_maximalIdeal_ne_top
  surjective_mapCotangent_toOfQuot

/-- The canonical `k`-linear map from the base-changed cotangent space of `Λ`
to the cotangent space of `A`, induced by the algebra structure map. -/
def baseCotangentMap [Algebra.IsIntegral Λ k] [IsLocalHom (algebraMap Λ k)]
    (A : LocAlgCat.{w} Λ k) : k ⊗[ResidueField Λ] CotangentSpace Λ →ₗ[k] CotangentSpace A :=
  letI baseMap : CotangentSpace Λ →ₗ[ResidueField Λ] CotangentSpace A :=
    ((maximalIdeal Λ).mapCotangent (maximalIdeal A) (Algebra.ofId Λ A) (by
      change _ ≤ Ideal.comap (algebraMap Λ A) _
      rw [comap_algebraMap_maximalIdeal])).extendScalarsOfSurjective
    IsLocalRing.residue_surjective
  TensorProduct.AlgebraTensorModule.lift (LinearMap.toSpanSingleton k _ baseMap)

@[simp]
lemma baseCotangentMap_tmul [Algebra.IsIntegral Λ k] [IsLocalHom (algebraMap Λ k)]
    (r : k) (a : CotangentSpace Λ) : A.baseCotangentMap (r ⊗ₜ a) =
      r • ((maximalIdeal Λ).mapCotangent (maximalIdeal A) (Algebra.ofId Λ A) (by
        change _ ≤ Ideal.comap (algebraMap Λ A) _
        rw [comap_algebraMap_maximalIdeal]) a) := rfl

open Submodule in
theorem range_baseCotangentMap [Algebra.IsIntegral Λ k] [IsLocalHom (algebraMap Λ k)] :
    A.baseCotangentMap.range = (mapCotangent A.toSpecialFiber).ker := ext fun x ↦ by
  rcases (maximalIdeal A).toCotangent_surjective x with ⟨x, rfl⟩
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  refine ⟨fun ⟨y, hy⟩ ↦ ?_, fun hx ↦ ?_⟩
  · rw [← hy]; clear * -
    induction y with
    | zero => simp
    | tmul x y =>
      rcases (maximalIdeal Λ).toCotangent_surjective y with ⟨y, rfl⟩
      simp [mapCotangent_toCotangent, Ideal.toCotangent_eq_zero]
    | add x y hx hy => simp [hx, hy]
  · rcases x with ⟨x, x_in⟩
    simp only [mapCotangent_toCotangent, toAlgHom_toOfQuot_apply, Ideal.toCotangent_eq_zero] at hx
    have : Nontrivial (A ⧸ (maximalIdeal Λ).map (algebraMap Λ A)) :=
      Ideal.Quotient.nontrivial_iff.mpr map_algebraMap_maximalIdeal_ne_top
    rw [← toAlgHom_toOfQuot_apply, ← map_toAlgHom_toOfQuot_maximalIdeal_eq, ← Ideal.map_pow,
      ← Ideal.mem_comap, Ideal.comap_map_of_surjective' _ surjective_toAlgHom_toOfQuot,
      ker_toAlgHom_toOfQuot, mem_sup] at hx
    rcases hx with ⟨u, u_in, v, v_in, huv⟩
    simp_rw [← LinearMap.mem_range, ← huv]
    have pow_le : maximalIdeal A ^ 2 ≤ maximalIdeal A := Ideal.pow_le_self (by simp)
    change (maximalIdeal A).toCotangent ⟨u, pow_le u_in⟩ + (maximalIdeal A).toCotangent
      ⟨v, map_maximalIdeal_le _ v_in⟩ ∈ _
    rw [(Ideal.toCotangent_eq_zero ..).mpr ‹_›, zero_add]
    clear * -; rw [Ideal.map, Ideal.span] at v_in
    induction v_in using span_induction with
    | mem _ hx =>
      obtain ⟨x, x_in, rfl⟩ := hx
      exact ⟨1 ⊗ₜ (maximalIdeal Λ).toCotangent ⟨x, x_in⟩, by simp⟩
    | zero =>
      use 0; simp [show (⟨0, _⟩ : maximalIdeal A) = 0 by rfl]
    | add z w hz hw ihz ihw =>
      change _ ∈ (maximalIdeal Λ).map (algebraMap Λ A) at hz hw
      rw [show (⟨z + w, _⟩ : maximalIdeal A) = ⟨z, map_maximalIdeal_le _ hz⟩ +
        ⟨w, map_maximalIdeal_le _ hw⟩ by simp, map_add]
      exact add_mem (ihz hz) (ihw hw)
    | smul a x hx ihx =>
      change _ ∈ (maximalIdeal Λ).map (algebraMap Λ A) at hx
      rw [show (⟨a • x, _⟩ : maximalIdeal A) = a • ⟨x, map_maximalIdeal_le _ hx⟩ by simp, map_smul,
        ← residue_smul_cotangent]
      exact smul_mem _ _ (ihx hx)

theorem exact_baseCotangentMap_mapCotangent_toSpecialFiber [Algebra.IsIntegral Λ k]
    [IsLocalHom (algebraMap Λ k)] : Exact A.baseCotangentMap (mapCotangent A.toSpecialFiber) :=
  LinearMap.exact_iff.mpr A.range_baseCotangentMap.symm

end IsLocalRing

/-

open KaehlerDifferential

/-- The relative cotangent space for an object in `LocAlgCat`. -/
@[stacks 06GY]
abbrev RelCotangent (A : LocAlgCat.{w} Λ k) : Type _ := k ⊗[A] Ω[A⁄Λ]

/-- The canonical `k`-linear map from cotangent space to relative cotangent space. -/
def cotangentToRelCotangent (A : LocAlgCat.{w} Λ k) : CotangentSpace A →ₗ[k] RelCotangent A where
  toFun x := kerCotangentToTensor Λ A k <| ((maximalIdeal A).mapCotangent
    (RingHom.ker (algebraMap A k)) (AlgHom.id Λ A) (by rw [← ker_residue, Ideal.comap_idₐ,
      ← RingHom.ker_coe_toRingHom, residue_toRingHom]) x)
  map_add' := by simp
  map_smul' r x := by
    obtain ⟨r, rfl⟩ := A.residue_surjective r
    obtain ⟨x, rfl⟩ := (maximalIdeal A).toCotangent_surjective x
    simp only [residue_smul_cotangent, RingHom.id_apply, Ideal.mapCotangent_toCotangent,
      AlgHom.coe_id, id_eq, kerCotangentToTensor_toCotangent]
    rw [← map_smul, Ideal.mapCotangent_toCotangent]
    simp only [SetLike.val_smul, smul_eq_mul, AlgHom.coe_id, id_eq,
      kerCotangentToTensor_toCotangent, Derivation.leibniz]
    rw [TensorProduct.tmul_add, ← RingHom.coe_coe A.residue, residue_toRingHom,
      IsScalarTower.algebraMap_smul, TensorProduct.tmul_smul, add_eq_left,
      ← TensorProduct.smul_tmul, Algebra.smul_def, ← residue_toRingHom, RingHom.coe_coe,
      residue_eq_zero_iff.mpr x.prop, zero_mul, TensorProduct.zero_tmul]

lemma cotangentToRelCotangent_toCotangent (A : LocAlgCat.{w} Λ k) (a : maximalIdeal A) :
    A.cotangentToRelCotangent ((maximalIdeal A).toCotangent a) = 1 ⊗ₜ (D Λ A) a := rfl

/-- The canonical `k`-linear map between relative cotangent spaces
induced by a morphism in `LocAlgCat`. -/
abbrev mapRelCotangent (f : A ⟶ B) : A.RelCotangent →ₗ[k] B.RelCotangent :=
  letI : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower A B k := .of_algebraMap_eq fun a ↦ by
    rw [RingHom.algebraMap_toAlgebra, eq_comm, ← RingHom.comp_apply]
    exact DFunLike.congr_fun f.residue_comp a
  letI baseMap : Ω[A⁄Λ] →ₗ[A] B.RelCotangent := {
    toFun := fun ω ↦ 1 ⊗ₜ[B] KaehlerDifferential.map Λ Λ A B ω
    map_add' := fun _ _ ↦ by rw [map_add, TensorProduct.tmul_add]
    map_smul' := fun _ _ ↦ by rw [RingHom.id_apply, map_smul, TensorProduct.tmul_smul] }
  TensorProduct.AlgebraTensorModule.lift (LinearMap.toSpanSingleton k _ baseMap)

section IsLocalRing

variable [IsLocalRing Λ]

theorem exact_baseCotangentMap_cotangentToMaximalIdealQuotSup [Algebra.IsIntegral Λ k]
    [IsLocalHom (algebraMap Λ k)] : Exact A.baseCotangentMap A.cotangentToMaximalIdealQuotSup :=
  LinearMap.exact_iff.mpr ker_cotangentToMaximalIdealQuotSup_eq

theorem range_baseCotangentMap_le [Algebra.IsIntegral Λ k] [IsLocalHom (algebraMap Λ k)] :
    A.baseCotangentMap.range ≤ A.cotangentToRelCotangent.ker := by
  rintro _ ⟨y, rfl⟩; induction y with
  | zero => simp
  | tmul _ x =>
    obtain ⟨x, rfl⟩ := (maximalIdeal Λ).toCotangent_surjective x
    rw [baseCotangentMap_tmul]
    simp [cotangentToRelCotangent_toCotangent]
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

set_option backward.isDefEq.respectTransparency false in
open Submodule in
/-- The canonical `k`-linear map between cotangent spaces of special fibers
induced by a morphism in `LocAlgCat` -/
def mapMaximalIdealQuotSup (f : A ⟶ B) :
    A.MaximalIdealQuotSup →ₗ[k] B.MaximalIdealQuotSup := by
  algebraize [f.toAlgHom.toRingHom]
  have smul (r : A) (x : B) : r • x = f.toAlgHom r * x := rfl
  have : IsScalarTower A k B.MaximalIdealQuotSup := .of_algebraMap_smul fun r x ↦ by
    change _ = f.toAlgHom r • x
    rw [← algebraMap_smul k (f.toAlgHom r), ← residue_apply (A := B), ← AlgHom.comp_apply,
      f.residue_comp, residue_apply]
  refine LinearMap.extendScalarsOfSurjective A.surj (mapQ
    ((comap (maximalIdeal A).subtype ((maximalIdeal Λ).map (algebraMap Λ A))) ⊔
      (maximalIdeal A) • ⊤ : Submodule A (maximalIdeal A)) (((comap (maximalIdeal B).subtype
    ((maximalIdeal Λ).map (algebraMap Λ B))) ⊔ (maximalIdeal B) • ⊤ :
      Submodule B (maximalIdeal B)).restrictScalars A) ?_ ?_)
  · exact {
      toFun x := ⟨f.toAlgHom x.val, f.map_maximalIdeal_le
        ((maximalIdeal A).mem_map_of_mem _ x.prop)⟩
      map_add' := by simp
      map_smul' r x := by simp [smul]}
  · rintro ⟨x, x_in⟩
    simp only [mem_sup, mem_comap, subtype_apply, Subtype.exists, AddMemClass.mk_add_mk,
      Subtype.mk.injEq, exists_and_right, exists_prop, restrictScalars_sup, LinearMap.coe_mk,
      AddHom.coe_mk, restrictScalars_mem, forall_exists_index, and_imp]
    intro y y_in_max y_in_map z z_in_max z_in_submodule hx
    refine ⟨f.toAlgHom y, ⟨?_, ?_⟩, ⟨f.toAlgHom z, ⟨?_, ?_⟩, ?_⟩⟩
    · rwa [← Ideal.mem_comap, f.comap_maximalIdeal_eq]
    · change algebraMap A B y ∈ _
      rw [IsScalarTower.algebraMap_eq Λ A B, ← Ideal.map_map]
      exact Ideal.mem_map_of_mem _ y_in_map
    · rwa [← Ideal.mem_comap, f.comap_maximalIdeal_eq]
    · simp only [mem_smul_top_iff, smul_eq_mul, ← pow_two] at ⊢ z_in_submodule
      rw [← Ideal.mem_comap]
      apply Ideal.le_comap_pow
      rwa [f.comap_maximalIdeal_eq]
    · rw [← hx, map_add]

theorem mapCotangent_comp_baseCotangentMap {f : A ⟶ B} [Algebra.IsIntegral Λ k]
    [IsLocalHom (algebraMap Λ k)] : (mapCotangent f).comp A.baseCotangentMap =
      B.baseCotangentMap := by
  sorry

theorem mapRelCotangent_comp_cotangentToRelCotangent {f : A ⟶ B} :
    (mapRelCotangent f).comp A.cotangentToRelCotangent =
      B.cotangentToRelCotangent.comp (mapCotangent f) := by sorry

@[stacks 06S3 "(2) => (3)"]
theorem surjective_mapRelCotangent_of_surjective_mapCotangent {f : A ⟶ B}
    (hf : Surjective (mapCotangent f)) : Surjective (mapRelCotangent f) := by sorry

end IsLocalRing
-/
end Cotangent

end LocAlgCat

/-- The complete base category for deformation theory over `Λ`. This is the full subcategory of
`LocAlgCat Λ k` consisting of complete Noetherian local `Λ`-algebras with residue field `k`. -/
abbrev CBaseCat (Λ : Type u) [CommRing Λ] (k : Type v) [Field k] [Algebra Λ k] :=
  ObjectProperty.FullSubcategory fun A : LocAlgCat.{w} Λ k ↦
    IsNoetherianRing A ∧ IsAdicComplete (maximalIdeal A) A

namespace CBaseCat

instance {A : CBaseCat Λ k} : IsNoetherianRing A.obj := A.property.left

instance {A : CBaseCat Λ k} : IsAdicComplete (maximalIdeal A.obj) A.obj := A.property.right

end CBaseCat

/-- The base category for deformation theory over `Λ`. This is the full subcategory of
`LocAlgCat Λ k` consisting of Artinian local `Λ`-algebras with residue field `k`. -/
@[stacks 06GC]
abbrev BaseCat (Λ : Type u) [CommRing Λ] (k : Type v) [Field k] [Algebra Λ k] :=
  ObjectProperty.FullSubcategory fun A : LocAlgCat.{w} Λ k ↦ IsArtinianRing A

namespace BaseCat

instance (A : BaseCat Λ k) : IsArtinianRing A.obj := A.property

/-- The natural inclusion functor from the base category to the complete base category. -/
abbrev ιToCBaseCat (Λ : Type u) [CommRing Λ] (k : Type v) [Field k] [Algebra Λ k] :
    BaseCat.{w} Λ k ⥤ CBaseCat.{w} Λ k :=
  ObjectProperty.ιOfLE fun _ _ ↦ ⟨inferInstance, inferInstance⟩

variable {A B C : BaseCat.{w} Λ k} {f : A ⟶ B}

variable (Λ k) in
/-- The object in the base category associated to a type equipped with appropriate typeclasses.
This is a preferred way to construct a term of `BaseCat`. -/
abbrev of (X : Type w) [CommRing X] [IsLocalRing X] [Algebra Λ X] [Algebra X k]
    [IsScalarTower Λ X k] [IsArtinianRing X] (hX : Surjective (algebraMap X k)) :
    BaseCat Λ k := ⟨.of Λ k X hX, inferInstance⟩

/-- The quotient of an object `A` in `BaseCat` by a proper ideal `I`. -/
def ofQuot (A : BaseCat.{w} Λ k) (I : Ideal A.obj) [Nontrivial (A.obj ⧸ I)] : BaseCat Λ k :=
  ⟨A.obj.ofQuot I, Ideal.Quotient.mk_surjective.isArtinianRing⟩

/-- Upgrades the canonical quotient map from `A` to `A ⧸ I` to a morphism in `BaseCat`. -/
def toOfQuot (A : BaseCat.{w} Λ k) (I : Ideal A.obj) [Nontrivial (A.obj ⧸ I)] :
    A ⟶ A.ofQuot I := ObjectProperty.homMk (A.obj.toOfQuot I)

/-- A morphism `f : A ⟶ B` in `BaseCat` is a small extension if it is a surjective map
whose kernel is a principal ideal annihilated by the maximal ideal of `A`. -/
@[stacks 06GD]
class IsSmallExtension (f : A ⟶ B) : Prop where
  private mk ::
  surjective (f) : Function.Surjective f.hom.toAlgHom
  isPrincipal_ker (f) : (RingHom.ker f.hom.toAlgHom).IsPrincipal
  le_annihilator_ker (f) : maximalIdeal A.obj ≤ (RingHom.ker f.hom.toAlgHom).annihilator

theorem isSmallExtenstion_iff : IsSmallExtension f ↔ Function.Surjective f.hom.toAlgHom ∧
    ∃ x : A.obj, Ideal.span {x} = RingHom.ker f.hom.toAlgHom ∧
      ∀ y ∈ maximalIdeal A.obj, x * y = 0 := by
  refine ⟨fun ⟨_, ⟨x, hx⟩, h⟩ ↦ ⟨IsSmallExtension.surjective f, x, ?_, fun y y_in ↦ ?_⟩,
    fun ⟨h, x, x_span, hx⟩ ↦ ⟨h, ⟨x, ?_⟩, ?_⟩⟩
  · simp [hx]
  · rw [mul_comm, ← smul_eq_mul, ← Submodule.mem_annihilator_span_singleton, ← hx]
    exact h y_in
  · simp [← x_span]
  · intro y y_in
    rw [← x_span, Ideal.span, Submodule.mem_annihilator_span_singleton, smul_eq_mul, mul_comm]
    exact hx y y_in

theorem isSmallExtension_of_bijective (h : Bijective f.hom.toAlgHom) : IsSmallExtension f :=
  (isSmallExtenstion_iff).mpr ⟨h.surjective, 0, by
    have := h.injective
    rw [RingHom.injective_iff_ker_eq_bot] at this
    simp [this]⟩

theorem IsSmallExtension.toOfQuot_span_singleton (A : BaseCat.{w} Λ k) (x : A.obj)
    [Nontrivial (A.obj ⧸ (Ideal.span {x}))] (h : ∀ y ∈ maximalIdeal A.obj, x * y = 0) :
    IsSmallExtension (A.toOfQuot (Ideal.span {x})) := by
  rw [isSmallExtenstion_iff]
  refine ⟨Ideal.Quotient.mk_surjective, x, ?_, h⟩
  ext; rw [← Submodule.Quotient.mk_eq_zero]
  exact Iff.rfl

open Submodule in
@[elab_as_elim, stacks 06GE]
theorem induction_on_isSmallExtension (hf : Surjective f.hom.toAlgHom)
    {P : ∀ {A B : BaseCat.{w} Λ k} (f : A ⟶ B), Surjective f.hom.toAlgHom → Prop}
    (small_ext : ∀ {X Y : BaseCat.{w} Λ k} (f : X ⟶ Y) [IsSmallExtension f],
      P f (IsSmallExtension.surjective f))
    (comp : ∀ {A B C : BaseCat.{w} Λ k} (f : A ⟶ B) (g : B ⟶ C) [IsSmallExtension f]
      (hg : Surjective g.hom.toAlgHom), P g hg →
    P (f ≫ g) (hg.comp (IsSmallExtension.surjective f))) : P f hf := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = Module.length A.obj A.obj :=
    ENat.ne_top_iff_exists.mp Module.length_ne_top
  symm at hn; revert A
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A f hf hlen
    have hn : n ≠ 0 := by
      intro hn; revert hlen
      have : Nontrivial A.obj := inferInstance
      simpa [hn, Module.length_eq_zero_iff, ← not_nontrivial_iff_subsingleton]
    let I := RingHom.ker f.hom.toAlgHom
    by_cases hI : I = ⊥
    · rw [← RingHom.injective_iff_ker_eq_bot] at hI
      have : IsSmallExtension f := isSmallExtension_of_bijective ⟨hI, hf⟩
      exact small_ext f
    obtain ⟨x, hx, x_ne⟩ := (Submodule.ne_bot_iff _).mp (Ideal.annihilator_inf_ne_bot
      ((isArtinianRing_iff_isNilpotent_maximalIdeal A.obj).mp inferInstance) hI)
    have x_in : x ∈ I := (mem_inf.mp hx).right
    replace hx : ∀ y ∈ maximalIdeal A.obj, x * y = 0 := mem_annihilator.mp (mem_inf.mp hx).left
    have span_ne_top : Ideal.span {x} ≠ ⊤ := by
      refine Ideal.span_singleton_ne_top (le_maximalIdeal ?_ x_in)
      rw [Ideal.ne_top_iff_exists_maximal]
      exact ⟨maximalIdeal A.obj, maximalIdeal.isMaximal A.obj, le_maximalIdeal
        (RingHom.ker_ne_top f.hom.toAlgHom)⟩
    have : Nontrivial (A.obj ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr span_ne_top
    have : IsLocalRing (A.obj ⧸ Ideal.span {x}) := .of_surjective' _ Ideal.Quotient.mk_surjective
    have aux : ∀ a ∈ Ideal.span {x}, (LocAlgCat.Hom.toAlgHom f.hom) a = 0 := by
      intro _ h; rw [Ideal.mem_span_singleton'] at h
      rcases h with ⟨_, rfl⟩; rw [← RingHom.mem_ker]
      exact Ideal.mul_mem_left _ _ x_in
    let C := A.ofQuot (Ideal.span {x})
    let g : A ⟶ C := A.toOfQuot (Ideal.span {x})
    have hg : IsSmallExtension g := IsSmallExtension.toOfQuot_span_singleton A x hx
    let u : C.obj →ₐ[Λ] B.obj := Ideal.Quotient.liftₐ (Ideal.span {x}) f.hom.toAlgHom aux
    have u_surj : Surjective u :=
      Ideal.Quotient.lift_surjective_of_surjective (Ideal.span {x}) aux hf
    let f' : C ⟶ B := ObjectProperty.homMk (LocAlgCat.ofHom u (eq_maximalIdeal
      (Ideal.comap_isMaximal_of_surjective _ ‹_›)) (AlgHom.ext fun t ↦ by
        induction t using Quotient.induction_on with
        | H t =>
          simp [← AlgHom.comp_apply, f.hom.residue_comp, u]
          simpa [LocAlgCat.residue, ← Ideal.Quotient.algebraMap_eq] using
            IsScalarTower.algebraMap_apply ..))
    obtain ⟨m, hm⟩ : ∃ n : ℕ, n = Module.length C.obj C.obj :=
      ENat.ne_top_iff_exists.mp Module.length_ne_top
    symm at hm; suffices h : m < n by
      change P (g ≫ f') _; apply comp
      · apply ih m h; exact hm
      · exact u_surj
    change Module.length (A.obj ⧸ Ideal.span {x}) (A.obj ⧸ Ideal.span {x}) = m at hm
    have := Submodule.length_le_length_restrictScalar A.obj (A.obj ⧸ Ideal.span {x})
      (A.obj ⧸ Ideal.span {x}) ⊤
    rw [Module.length_top, restrictScalars_top, Module.length_top] at this
    rw [← ENat.coe_lt_coe, ← hlen, ← hm]
    exact lt_of_le_of_lt this (length_quotient_lt (Ideal.span {x}) (by simpa))

section

variable [IsLocalRing Λ] [Module.Finite Λ k]

/-- xxxx -/
@[stacks 06GH "(1)" ]
abbrev ofPullback (f : A ⟶ C) (g : B ⟶ C) (hg : Surjective g.hom.toAlgHom) : BaseCat.{w} Λ k :=
  ⟨.ofPullback f.hom g.hom hg, inferInstance⟩

/-- xxxx -/
abbrev fromOfPullback (f : A ⟶ C) (g : B ⟶ C) (hg : Surjective g.hom.toAlgHom) :
    ofPullback f g hg ⟶ A := ObjectProperty.homMk (LocAlgCat.fromOfPullback f.hom g.hom hg)

@[stacks 06GH "(2)"]
instance fromOfPullback_isSmallExtension (f : A ⟶ C) (g : B ⟶ C) [IsSmallExtension g] :
    IsSmallExtension (fromOfPullback f g (IsSmallExtension.surjective g)) := by
  obtain ⟨x, x_span, hx⟩ := ((isSmallExtenstion_iff (f := g)).mp ‹_›).right
  rw [isSmallExtenstion_iff]
  constructor
  · exact f.hom.toAlgHom.surjective_pullbackFst_of_surjective g.hom.toAlgHom
      (IsSmallExtension.surjective g)
  · have : (0, x) ∈ f.hom.toAlgHom.pullback g.hom.toAlgHom := by
      simp only [AlgHom.mem_equalizer, AlgHom.coe_comp, Function.comp_apply, AlgHom.fst_apply,
        map_zero, AlgHom.snd_apply]
      rw [eq_comm, ← RingHom.mem_ker, ← x_span]
      exact Ideal.mem_span_singleton_self x
    refine ⟨⟨(0, x), this⟩, ?_, fun ⟨⟨a, b⟩, hab⟩ h ↦ ?_⟩
    · change _ = RingHom.ker (AlgHom.pullbackFst ..)
      ext ⟨⟨u, v⟩, h⟩
      simp only [LocAlgCat.coe_of, Ideal.mem_span_singleton', eq_comm, Subtype.exists,
        MulMemClass.mk_mul_mk, Subtype.mk.injEq, AlgHom.mem_equalizer, AlgHom.coe_comp,
        Function.comp_apply, AlgHom.fst_apply, AlgHom.snd_apply, exists_prop, Prod.exists,
        Prod.mk_mul_mk, mul_zero, Prod.mk.injEq, and_left_comm, exists_and_left, RingHom.mem_ker,
        Subalgebra.coe_val, and_iff_left_iff_imp]
      intro u_eq
      simp only [u_eq, AlgHom.mem_equalizer, AlgHom.coe_comp, Function.comp_apply,
        AlgHom.fst_apply, map_zero, AlgHom.snd_apply] at h
      rw [eq_comm, ← RingHom.mem_ker, ← x_span, Ideal.mem_span_singleton'] at h
      rcases h with ⟨w, hw⟩
      rcases LocAlgCat.exists_mem_maximalIdeal_toAlgHom_apply_add_eq g.hom f.hom
        w (IsSmallExtension.surjective g) with ⟨z, m, m_in, hm⟩
      exact ⟨z, w + m, hm.symm, by rw [add_mul, hw, mul_comm, hx m m_in, add_zero]⟩
    · suffices ¬ IsUnit b by simpa [← Subtype.val_inj] using hx b this
      intro hb
      simp only [AlgHom.mem_equalizer, AlgHom.coe_comp, Function.comp_apply, AlgHom.fst_apply,
        AlgHom.snd_apply] at hab
      have : IsUnit ((LocAlgCat.Hom.toAlgHom f.hom) a) := by
        rw [hab]; exact IsUnit.map g.hom.toAlgHom hb
      apply f.hom.isLocalHom_toAlgHom.map_nonunit at this
      simp only [LocAlgCat.coe_of, mem_maximalIdeal, mem_nonunits_iff,
        AlgHom.isUnit_pullback_mk_iff, not_and] at h
      exact (iff_false_intro (h this)).mp hb

/-- xxxx -/
abbrev ofPullbackOfIsSeparable [Algebra.IsSeparable (ResidueField Λ) k] (f : A ⟶ C) (g : B ⟶ C) :
    BaseCat Λ k :=
  letI : Algebra (f.hom.toAlgHom.pullback g.hom.toAlgHom) k :=
    (A.obj.residue.comp (f.hom.toAlgHom.pullbackFst g.hom.toAlgHom)).toAlgebra
  letI : IsScalarTower Λ (f.hom.toAlgHom.pullback g.hom.toAlgHom) k := .of_algebraMap_eq (by
    simp [RingHom.algebraMap_toAlgebra])
  haveI : IsLocalRing ↥(f.hom.toAlgHom.pullback g.hom.toAlgHom) :=
    isLocalRing_algHomPullback _ _ g.hom.isLocalHom_toAlgHom
  ⟨.of Λ k (f.hom.toAlgHom.pullback g.hom.toAlgHom)
    (LocAlgCat.surjective_residue_comp_pullbackFst_of_isSeparable f.hom g.hom), inferInstance⟩

end

end BaseCat

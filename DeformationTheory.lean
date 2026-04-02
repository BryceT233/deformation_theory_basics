/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import Mathlib

@[expose] public section

noncomputable section

universe w v u

/-! # `IsLocalHom` instances for `AlgHom`
goes to `RingTheory/LocalRing/RingHom/Basic.lean`-/

section AlgHom

variable {R S T : Type*} [Semiring R] [Semiring S] [Semiring T]
variable {A : Type*} [CommSemiring A] [Algebra A R] [Algebra A S] [Algebra A T]

variable (A) in
instance isLocalHom_algHomId : IsLocalHom (AlgHom.id A R) := ⟨fun _ ↦ id⟩

instance AlgHom.isLocalHom_comp (f : R →ₐ[A] S) (g : S →ₐ[A] T) [IsLocalHom f] [IsLocalHom g] :
    IsLocalHom (g.comp f) where
  map_nonunit a := IsLocalHom.map_nonunit a ∘ IsLocalHom.map_nonunit (f := g) (f a)

end AlgHom

--------------------------------------------------------------------------------

/-! # some `ULift` instances.
goes to where `RingEquiv` API locates. -/
/-
instance {R : Type*} [Semiring R] [IsNoetherianRing R] : IsNoetherianRing (ULift R) :=
  isNoetherianRing_of_ringEquiv R (ULift.ringEquiv.symm)

instance {R : Type*} [Semiring R] [IsArtinianRing R] : IsArtinianRing (ULift R) :=
  RingEquiv.isArtinianRing (ULift.ringEquiv.symm)

instance {R : Type*} [CommSemiring R] [IsLocalRing R] : IsLocalRing (ULift R) :=
  RingEquiv.isLocalRing (ULift.ringEquiv.symm)

instance {R : Type*} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] :
    IsAdicComplete (maximalIdeal (ULift.{u} R)) (ULift.{u} R) := by
  rw [← IsAdicComplete.congr_ringEquiv _ ULift.ringEquiv,
    IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv ULift.ringEquiv)]
  infer_instance -/

--------------------------------------------------------------------------------

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

theorem Submodule.length_le_restrictScalar (A R M : Type*) [CommRing A] [Ring R] [Algebra A R]
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower A R M] (p : Submodule R M) :
    Module.length R p ≤ Module.length A (p.restrictScalars A) := by
  rw [← WithBot.coe_le_coe, Module.coe_length, Module.coe_length]
  let e : Submodule R ↥p ↪o Submodule A ↥(restrictScalars A p) := restrictScalarsEmbedding A R p
  have (q : Submodule A ↥(restrictScalars A p)) : Subsingleton (e ⁻¹' {q}) :=
    Set.Subsingleton.coe_sort <| Set.Subsingleton.preimage Set.subsingleton_singleton e.injective
  simpa using Order.krullDim_le_of_krullDim_preimage_le' e e.monotone fun _ ↦
    Order.krullDim_nonpos_of_subsingleton

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
  classical
  rcases hI with ⟨n, hn⟩
  have h_ex : ∃ t : ℕ, J • I ^ t = ⊥ := ⟨n, by simp [hn]⟩
  let t := Nat.find h_ex
  have ht : J • I ^ t = ⊥ := Nat.find_spec h_ex
  by_cases t = 0; · simp_all
  obtain ⟨s, hs⟩ := Nat.exists_add_one_eq.mpr (show 0 < t by lia)
  obtain ⟨x, x_in, x_ne⟩ := (Submodule.ne_bot_iff _).mp (Nat.find_min h_ex (show s < t by lia))
  refine (Submodule.ne_bot_iff _).mpr
    ⟨x, mem_inf.mpr ⟨mem_annihilator.mpr fun r r_in ↦ ?_, ?_⟩, x_ne⟩
  · rw [smul_eq_mul, ← mem_bot, ← ht, ← hs, pow_succ, ← smul_eq_mul, ← smul_assoc]
    exact smul_mem_smul x_in r_in
  · rw [smul_eq_mul, mul_comm, ← smul_eq_mul] at x_in
    exact smul_le_right x_in

--------------------------------------------------------------------------------

-- goes to Ideal.Cotangent.lean

open Function in
@[stacks 06S3 "(1)=>(2)"]
theorem IsLocalRing.surjective_mapCotangent_of_surjective {R S A : Type*} [CommRing R]
    [IsLocalRing R] [CommRing S] [IsLocalRing S] [CommRing A] [Algebra A R] [Algebra A S]
    {f : R →ₐ[A] S} (h : Surjective f) : Surjective ((maximalIdeal R).mapCotangent
      (maximalIdeal S) f (((local_hom_TFAE f).out 0 3).mp h.isLocalHom)) := by
  have : IsLocalHom (f : R →+* S) := h.isLocalHom
  intro b; induction b using Submodule.Quotient.induction_on with
  | H z =>
    rcases z with ⟨z, hz⟩; rcases h z with ⟨z, rfl⟩
    suffices z ∈ maximalIdeal R by
      use (maximalIdeal R).toCotangent ⟨z, this⟩
      simp only [Ideal.mapCotangent_toCotangent]
      congr
    rw [← residue_eq_zero_iff] at hz
    nth_rw 2 [← RingHom.coe_coe] at hz
    rwa [← ResidueField.map_residue, ← RingHom.mem_ker, (RingHom.injective_iff_ker_eq_bot _).mp
      (show Injective (ResidueField.map (f : R →+* S)) from RingHom.injective _),
      Submodule.mem_bot, residue_eq_zero_iff] at hz
/-
open Function in
theorem IsLocalRing.tmp {R S A : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    [IsAdicComplete (maximalIdeal S) S] [CommRing A] [Algebra A R] [Algebra A S]
    {f : R →ₐ[A] S} :-/

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

instance isLocalHom_eqLocus_subtype {R S : Type*} [Ring R] [Semiring S] (f g : R →+* S) :
    IsLocalHom (f.eqLocus g).subtype where
  map_nonunit := by rintro ⟨_, h⟩; simpa using (RingHom.isUnit_eqLocus_mk_iff f g h).mpr

instance isLocalRing_eqLocus {R S : Type*} [Ring R] [Semiring S] [IsLocalRing R] (f g : R →+* S) :
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

instance isLocalHom_pullbackFst {F G : Type*} [FunLike F R T] [RingHomClass F R T] [FunLike G S T]
    [RingHomClass G S T] (f : F) (g : G) [IsLocalHom g] :
      IsLocalHom ((f : R →+* T).pullbackFst (g : S →+* T)) where
  map_nonunit := by
    rintro ⟨x, x_in⟩
    simp only [coe_comp, coe_fst, Subring.coe_subtype, Function.comp_apply, isUnit_pullback_mk_iff,
      imp_and, imp_self, true_and]
    simp only [mem_eqLocus, coe_comp, coe_coe, coe_fst, Function.comp_apply, coe_snd] at x_in
    intro ha
    suffices IsUnit (g x.2) from IsLocalHom.map_nonunit x.2 this
    rw [← x_in]; exact IsUnit.map f ha

instance isLocalHom_pullbackSnd {F G : Type*} [FunLike F R T] [RingHomClass F R T] [FunLike G S T]
    [RingHomClass G S T] (f : F) (g : G) [IsLocalHom f] :
      IsLocalHom ((f : R →+* T).pullbackSnd (g : S →+* T)) where
  map_nonunit := by
    rintro ⟨x, x_in⟩
    simp only [coe_comp, coe_snd, Subring.coe_subtype, Function.comp_apply, isUnit_pullback_mk_iff,
      imp_and, imp_self, and_true]
    simp only [mem_eqLocus, coe_comp, coe_coe, coe_fst, Function.comp_apply, coe_snd] at x_in
    intro ha
    suffices IsUnit (f x.1) from IsLocalHom.map_nonunit x.1 this
    rw [x_in]; exact IsUnit.map g ha

instance isLocalRing_ringHomPullback {R S T F G : Type*} [Ring R] [Ring S] [Semiring T]
    [IsLocalRing R] [FunLike F R T] [RingHomClass F R T] [FunLike G S T] [RingHomClass G S T]
    (f : F) (g : G) [IsLocalHom g] :
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

end pullback

end RingHom

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

instance isLocalHom_pullbackFst (f : A →ₐ[R] C) (g : B →ₐ[R] C) [IsLocalHom g] :
    IsLocalHom (pullbackFst f g) := ⟨(RingHom.isLocalHom_pullbackFst f g).map_nonunit⟩

instance isLocalHom_pullbackSnd (f : A →ₐ[R] C) (g : B →ₐ[R] C) [IsLocalHom f] :
    IsLocalHom (pullbackSnd f g) := ⟨(RingHom.isLocalHom_pullbackSnd f g).map_nonunit⟩

theorem surjective_pullbackFst_of_surjective (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (h : Function.Surjective g) : Function.Surjective (pullbackFst f g) :=
  RingHom.surjective_pullbackFst_of_surjective (f : A →+* C) (g : B →+* C) h

theorem surjective_pullbackSnd_of_surjective (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (h : Function.Surjective f) : Function.Surjective (pullbackSnd f g) :=
  RingHom.surjective_pullbackSnd_of_surjective (f : A →+* C) (g : B →+* C) h

end Ring

end AlgHom

instance isLocalRing_algHomPullback {R S T A : Type*} [CommSemiring R] [Ring S] [Algebra R S]
    [IsLocalRing S] [Ring T] [Algebra R T] [Semiring A] [Algebra R A] (f : S →ₐ[R] A)
    (g : T →ₐ[R] A) [IsLocalHom g] : IsLocalRing (AlgHom.pullback f g) :=
  inferInstanceAs <| IsLocalRing (RingHom.pullback (f : S →+* A) (g : T →+* A))

--------------------------------------------------------------------------------
/-
theorem AlgEquiv.subsingleton_of_surjective {A R S : Type*} [CommSemiring A] [Semiring R]
    [Semiring S] [Algebra A R] [Algebra A S] (h : Function.Surjective (algebraMap A S)) :
    Subsingleton (R ≃ₐ[A] S) where
  allEq e f := AlgEquiv.ext fun s ↦ by
    obtain ⟨a, ha⟩ := h (e s)
    have hs : s = algebraMap A R a := by
      apply e.injective
      simp [← ha]
    simp [hs]
-/
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
lemma of_coe (A : LocAlgCat.{w} Λ k) : of Λ k A A.surj = A := rfl

@[simp]
lemma residue_of_apply {x : (of Λ k X hX)} : (of Λ k X hX).residue x = algebraMap X k x := rfl

/-- The canonical equivalence between the residue field of an object and `k`. -/
def residueEquiv (A : LocAlgCat Λ k) : ResidueField A ≃ₐ[Λ] k where
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
  [localhom : IsLocalHom toAlgHom]
  residue_comp : B.residue.comp toAlgHom = A.residue

attribute [instance] Hom.localhom

initialize_simps_projections Hom (-localhom)

instance : Category (LocAlgCat.{w} Λ k) where
  Hom A B := Hom A B
  id A := ⟨AlgHom.id Λ A, by simp⟩
  comp {A B C} f g := ⟨g.toAlgHom.comp f.toAlgHom, by
    rw [← AlgHom.comp_assoc, g.residue_comp, f.residue_comp]⟩

instance : FunLike (Hom A B) A B where
  coe f := f.toAlgHom
  coe_injective' _ _ := by simpa using Hom.ext

instance : ConcreteCategory (LocAlgCat.{w} Λ k) Hom where
  hom := id
  ofHom := id

/-- Typecheck an `AlgHom` compatible with residue maps as a morphism in `LocAlgCat`. -/
abbrev ofHom (f : X →ₐ[Λ] Y) [IsLocalHom f] (hf : (of Λ k Y hY).residue.comp f =
    (of Λ k X hX).residue) : of Λ k X hX ⟶ of Λ k Y hY := ⟨f, hf⟩

@[simp]
lemma toAlgHom_ofHom (f : X →ₐ[Λ] Y) [IsLocalHom f] (hf : (of Λ k Y hY).residue.comp f =
    (of Λ k X hX).residue) : (ofHom f hf).toAlgHom = f := rfl

@[simp]
lemma ofhom_toAlgHom (f : A ⟶ B) : ofHom f.toAlgHom f.residue_comp = f := rfl

@[simp]
lemma hom_id : (𝟙 A : A ⟶ A).toAlgHom = AlgHom.id Λ A := rfl

@[simp]
lemma id_apply (a : A) : (𝟙 A : A ⟶ A) a = a := by simp

@[simp]
lemma hom_comp (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).toAlgHom = g.toAlgHom.comp f.toAlgHom := rfl

@[simp]
lemma comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a) := by simp

@[simp]
lemma ofHom_id : ofHom (.id Λ X) (by simp) = 𝟙 (of Λ k X hX) := rfl

@[simp]
lemma ofHom_comp (f : X →ₐ[Λ] Y) [IsLocalHom f] (g : Y →ₐ[Λ] Z) [IsLocalHom g]
    (hf : (of Λ k Y hY).residue.comp f = (of Λ k X hX).residue)
    (hg : (of Λ k Z hZ).residue.comp g = (of Λ k Y hY).residue) :
    ofHom (g.comp f) (by rw [← AlgHom.comp_assoc, hg, hf]) = ofHom f hf ≫ ofHom g hg := rfl

lemma ofHom_apply (f : X →ₐ[Λ] Y) [IsLocalHom f] (x : X)
    (hf : (of Λ k Y hY).residue.comp f = (of Λ k X hX).residue) : ofHom f hf x = f x := rfl

lemma inv_hom_apply (e : A ≅ B) (x : A) : e.inv (e.hom x) = x := by simp

lemma hom_inv_apply (e : A ≅ B) (x : B) : e.hom (e.inv x) = x := by simp

/-
variable (A) in
lemma forget_obj : (forget (LocAlgCat.{w} Λ k)).obj A = A := rfl

instance : CommRing ((forget (LocAlgCat.{w} Λ k)).obj A) := inferInstanceAs <| CommRing A

instance : Algebra Λ ((forget (LocAlgCat.{w} Λ k)).obj A) := inferInstanceAs <| Algebra Λ A

instance : IsLocalRing ((forget (LocAlgCat.{w} Λ k)).obj A) := inferInstanceAs <| IsLocalRing A

instance (f : A ⟶ B) : IsLocalHom ((forget (LocAlgCat.{w} Λ k)).map f) := ⟨f.localhom.map_nonunit⟩

instance hasForgetToCommAlgCat : HasForget₂ (LocAlgCat.{w} Λ k) (CommAlgCat.{w} Λ) where
  forget₂.obj A := .of Λ A
  forget₂.map f := CommAlgCat.ofHom f.toAlgHom

@[simp] lemma forget₂_commAlgCat_obj (A : LocAlgCat.{w} Λ k) :
    (forget₂ (LocAlgCat.{w} Λ k) (CommAlgCat.{w} Λ)).obj A = .of Λ A := rfl

@[simp] lemma forget₂_commAlgCat_map (f : A ⟶ B) :
    (forget₂ (LocAlgCat.{w} Λ k) (CommAlgCat.{w} Λ)).map f = CommAlgCat.ofHom f.toAlgHom := rfl

/-- Build an isomorphism in the category `LocAlgCat Λ k` from
an `AlgEquiv` between `Λ`-algebras. -/

@[simps]
def isoMk {X Y : Type w} {_ : CommRing X} {_ : IsLocalRing X} {_ : Algebra Λ X} {_ : CommRing Y}
    {_ : IsLocalRing Y} {_ : Algebra Λ Y} {_ : Algebra X k} {_ : Algebra Y k}
    {_ : IsScalarTower Λ X k} {_ : IsScalarTower Λ Y k} {hX : Surjective (algebraMap X k)}
    {hY : Surjective (algebraMap Y k)} (e : X ≃ₐ[Λ] Y) (he : (of Λ k Y hY).residue.comp e =
      (of Λ k X hX).residue) : of Λ k X hX ≅ of Λ k Y hY where
  hom := ofHom (e : X →ₐ[Λ] Y) (by rw [← he])
  inv := ofHom (e.symm : Y →ₐ[Λ] X) (by ext; simp [← he])
  inv_hom_id := by simp [← ofHom_comp]
  hom_inv_id := by simp [← ofHom_comp]

/-- Build an `AlgEquiv` from an isomorphism in the category `LocAlgCat Λ k`. -/
@[simps]
def ofIso (i : A ≅ B) : A ≃ₐ[Λ] B where
  __ := i.hom.toAlgHom
  toFun := i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv x := by simp

@[simp]
lemma residue_comp_coe_ofIso (i : A ≅ B) : B.residue.comp (ofIso i) = A.residue := by
  ext
  simpa using DFunLike.congr_fun i.hom.residue_comp _

/-- Algebra equivalences between `Algebra`s compatible with residue isomorphisms are
the same as isomorphisms in `LocAlgCat`. -/
@[simps]
def isoEquivSubtypeAlgEquiv : (of Λ k X hX ≅ of Λ k Y hY) ≃
    { e : X ≃ₐ[Λ] Y // (of Λ k Y hY).residue.comp e = (of Λ k X hX).residue } where
  toFun i := ⟨ofIso i, residue_comp_coe_ofIso i⟩
  invFun f := isoMk f.val f.prop
-/

----------------------------------------------------------------------------------------------

/-- Given an object `A : LocAlgCat` and a nontrivial `A`-algebra `X` with
a surjective structure map, `LocAlgCat.ofSurj` constructs an induced object of `LocAlgCat`. -/
noncomputable abbrev ofSurj (A : LocAlgCat.{w} Λ k) (X : Type w) [CommRing X] [Nontrivial X]
    [Algebra A X] [Algebra Λ X] [IsScalarTower Λ A X] (h : Surjective (algebraMap A X)) :
    LocAlgCat.{w} Λ k :=
  letI : IsLocalRing X := .of_surjective' _ h
  letI : Algebra X k := ((algebraMap A X).liftOfSurjective h ⟨algebraMap A k, by
    rw [ker_eq_maximalIdeal _ A.surj]
    exact le_maximalIdeal (RingHom.ker_ne_top (algebraMap A X))⟩).toAlgebra
  letI : IsScalarTower Λ X k := .of_algebraMap_eq fun r ↦ by
    rw [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply Λ A X,
      RingHom.liftOfSurjective_comp_apply]
    simp [IsScalarTower.algebraMap_apply Λ A k]
  of Λ k X (Surjective.of_comp (g := (algebraMap A X)) (by
    rw [← RingHom.coe_comp, RingHom.algebraMap_toAlgebra, RingHom.liftOfSurjective_comp]
    exact A.surj))

@[simp]
lemma residue_ofSurj_algebraMap_apply (X : Type w) [CommRing X] [Nontrivial X] [Algebra A X]
    [Algebra Λ X] [IsScalarTower Λ A X] (h : Surjective (algebraMap A X)) (a : A) :
    (ofSurj A X h).residue (algebraMap A X a) = A.residue a := by
  let : Algebra X k := ((algebraMap A X).liftOfSurjective h ⟨algebraMap A k, by
    rw [ker_eq_maximalIdeal _ A.surj]
    exact le_maximalIdeal (RingHom.ker_ne_top (algebraMap A X))⟩).toAlgebra
  have : IsScalarTower A X k := .of_algebraMap_eq fun a ↦ by
    rw [RingHom.algebraMap_toAlgebra, RingHom.liftOfSurjective_comp_apply]
  simp [residue, IsScalarTower.algebraMap_eq A X k]

/-- Given an object `A : LocAlgCat` and a nontrivial `A`-algebra `X` with
a surjective structure map, `LocAlgCat.toOfSurj` upgrades the algebra to a morphism in
`LocAlgCat` from `A` to the induced object `LocAlgCat.ofSurj`. -/
noncomputable abbrev toOfSurj (A : LocAlgCat.{w} Λ k) (X : Type w) [CommRing X] [Nontrivial X]
    [Algebra A X] [Algebra Λ X] [IsScalarTower Λ A X] (h : Surjective (algebraMap A X)) :
    A ⟶ ofSurj A X h :=
  letI : IsLocalRing X := .of_surjective' _ h
  letI : Algebra X k := ((algebraMap A X).liftOfSurjective h ⟨algebraMap A k, by
    rw [ker_eq_maximalIdeal _ A.surj]
    exact le_maximalIdeal (RingHom.ker_ne_top (algebraMap A X))⟩).toAlgebra
  letI : IsScalarTower Λ X k := .of_algebraMap_eq fun r ↦ by
    rw [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply Λ A X,
      RingHom.liftOfSurjective_comp_apply]
    simp [IsScalarTower.algebraMap_apply Λ A k]
  letI : IsLocalHom (IsScalarTower.toAlgHom Λ A X) := ⟨h.isLocalHom.map_nonunit⟩
  ofHom (IsScalarTower.toAlgHom Λ A X)
    (by ext; simpa [residue] using residue_ofSurj_algebraMap_apply ..)

@[simp]
lemma toAlgHom_toOfSurj (X : Type w) [CommRing X] [Nontrivial X] [Algebra A X] [Algebra Λ X]
    [IsScalarTower Λ A X] (h : Surjective (algebraMap A X)) :
    (toOfSurj A X h).toAlgHom = algebraMap A X :=
  rfl

/-- Given morphisms `f : A ⟶ C` and `g : B ⟶ C` in `LocAlgCat`
where `g.toAlgHom` is surjective, `ofPullback f g h` constructs the pullback
`AlgHom.pullback f.toAlgHom g.toAlgHom` as an object in `LocAlgCat`. -/
abbrev ofPullback (f : A ⟶ C) (g : B ⟶ C) (h : Surjective g.toAlgHom) : LocAlgCat.{w} Λ k :=
  letI : Algebra (f.toAlgHom.pullback g.toAlgHom) k :=
    (A.residue.comp (f.toAlgHom.pullbackFst g.toAlgHom)).toAlgebra
  letI : IsScalarTower Λ (f.toAlgHom.pullback g.toAlgHom) k := .of_algebraMap_eq (by
    simp [RingHom.algebraMap_toAlgebra])
  of Λ k (f.toAlgHom.pullback g.toAlgHom) (by
    simpa [RingHom.algebraMap_toAlgebra] using Surjective.comp A.surj
      (AlgHom.surjective_pullbackFst_of_surjective _ _ h))

@[simp]
lemma residue_ofPullback (f : A ⟶ C) (g : B ⟶ C) (h : Surjective g.toAlgHom)
    (u : f.toAlgHom.pullback g.toAlgHom) : (ofPullback f g h).residue u = A.residue u.val.1 := by
  simp [residue, RingHom.algebraMap_toAlgebra]

/-- Upgrades the first projection map from the pullback algebra to a morphism in `LocAlgCat`. -/
abbrev fromOfPullback (f : A ⟶ C) (g : B ⟶ C) (hg : Surjective g.toAlgHom) :
    ofPullback f g hg ⟶ A := .mk (f.toAlgHom.pullbackFst g.toAlgHom) rfl

lemma exists_mem_maximalIdeal_toAlgHom_add_eq (f : A ⟶ C) (g : B ⟶ C) (hf : Surjective f.toAlgHom)
    (a : A) : ∃ (b : B) (m : A), m ∈ maximalIdeal A ∧ f.toAlgHom (a + m) = g.toAlgHom b := by
  rcases B.residue_surjective (residue A a) with ⟨b, hb⟩
  rw [← g.residue_comp, ← f.residue_comp, AlgHom.comp_apply, AlgHom.comp_apply, ← sub_eq_zero,
    ← map_sub, residue_eq_zero_iff, ← map_maximalIdeal_of_surjective (f.toAlgHom : A →+* C) hf,
    Ideal.mem_map_iff_of_surjective (f.toAlgHom : A →+* C) hf] at hb
  rcases hb with ⟨m, hm⟩
  simp only [RingHom.coe_coe, eq_sub_iff_add_eq', ← map_add] at hm
  exact ⟨b, m, hm⟩

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
        LocAlgCat.isUnit_aeval_derivative_of_isSeparable
          (Algebra.IsSeparable.isSeparable (ResidueField Λ) x) map_q ha)
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

section Cotangent

open KaehlerDifferential
open scoped TensorProduct

variable {f : A ⟶ B}

instance [IsLocalHom (algebraMap Λ k)] : IsLocalHom (algebraMap Λ A) where
  map_nonunit r hr := by
    apply IsUnit.map (algebraMap A k) at hr
    rwa [← IsScalarTower.algebraMap_apply Λ A k r, isUnit_map_iff] at hr

instance : IsScalarTower Λ (ResidueField A) (CotangentSpace A) := .of_algebraMap_smul fun r x ↦ by
  rw [IsScalarTower.algebraMap_apply Λ A, IsScalarTower.algebraMap_smul,
    IsScalarTower.algebraMap_smul]

instance : Module k (CotangentSpace A) := .compHom _ (A.residueEquiv.symm : k →+* ResidueField A)

lemma smul_cotangent_def (r : k) (x : CotangentSpace A) : r • x = (A.residueEquiv.symm r) • x :=
  rfl

instance : IsScalarTower Λ k (CotangentSpace A) := .of_algebraMap_smul fun r x ↦ by
  rw [smul_cotangent_def, IsScalarTower.algebraMap_eq Λ A, RingHom.comp_apply]
  have := residueEquiv_residue_apply (x := algebraMap Λ A r)
  rw [← AlgEquiv.eq_symm_apply, residue_apply] at this
  rw [← this, ← ResidueField.algebraMap_eq, IsScalarTower.algebraMap_smul,
    IsScalarTower.algebraMap_smul]

instance [IsLocalRing Λ] [Algebra.IsIntegral Λ k] : Module (ResidueField Λ) (CotangentSpace A) :=
  .compHom _ (algebraMap (ResidueField Λ) k)

lemma residueField_smul_cotangent [IsLocalRing Λ] [Algebra.IsIntegral Λ k] (r : ResidueField Λ)
    (x : CotangentSpace A) : r • x = (algebraMap (ResidueField Λ) k r) • x := rfl

instance [IsLocalRing Λ] [Algebra.IsIntegral Λ k] :
    IsScalarTower (ResidueField Λ) k (CotangentSpace A) := .of_compHom ..

instance [IsLocalRing Λ] [Algebra.IsIntegral Λ k] :
    IsScalarTower Λ (ResidueField Λ) (CotangentSpace A) := .of_algebraMap_smul fun r x ↦ by
  rw [residueField_smul_cotangent, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_smul]

@[simp]
lemma residue_smul_cotangent (a : A) (x : CotangentSpace A) : A.residue a • x = a • x := by
  rw [← residueEquiv_residue_apply, smul_cotangent_def, AlgEquiv.symm_apply_apply,
    ← IsLocalRing.ResidueField.algebraMap_eq, IsScalarTower.algebraMap_smul]

/-- The canonical `k`-linear map between cotangent spaces. -/
def mapCotangent (f : A ⟶ B) : CotangentSpace A →ₗ[k] CotangentSpace B where
  toFun x := (maximalIdeal A).mapCotangent (maximalIdeal B) f.toAlgHom
    (((local_hom_TFAE (f.toAlgHom : A →+* B)).out 0 3).mp (isLocalHom_toRingHom f.toAlgHom)) x
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
      exact ((local_hom_TFAE (f.toAlgHom : A →+* B)).out 0 4).mp
        (isLocalHom_toRingHom (Hom.toAlgHom f))

/-- The relative cotangent space for an object in `LocAlgCat`. -/
@[stacks 06GY]
abbrev relCotangent (A : LocAlgCat.{w} Λ k) : Type _ := k ⊗[A] Ω[A⁄Λ]

/-- The canonical `k`-linear map from cotangent space to relative cotangent space. -/
def toRelCotangent (A : LocAlgCat.{w} Λ k) : CotangentSpace A →ₗ[k] relCotangent A where
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

/-- The canonical `k`-linear map from the base-changed cotangent space of `Λ`
to the cotangent space of `A`, induced by the algebra structure map. -/
abbrev baseCotangentMap [IsLocalRing Λ] [IsLocalHom (algebraMap Λ k)] [Module.Finite Λ k]
    (A : LocAlgCat.{w} Λ k) : k ⊗[ResidueField Λ] CotangentSpace Λ →ₗ[k] CotangentSpace A :=
  letI F : Λ →ₐ[Λ] A := Algebra.ofId Λ A
  haveI : IsLocalHom (F : Λ →+* A) := inferInstanceAs <| IsLocalHom (algebraMap Λ A)
  letI baseMap : CotangentSpace Λ →ₗ[ResidueField Λ] CotangentSpace A :=
    ((maximalIdeal Λ).mapCotangent (maximalIdeal A) F
      (((IsLocalRing.local_hom_TFAE (F : Λ →+* A)).out 0 3).mp ‹_›)).extendScalarsOfSurjective
        (show Surjective (algebraMap Λ (ResidueField Λ)) from IsLocalRing.residue_surjective)
  TensorProduct.AlgebraTensorModule.lift (LinearMap.toSpanSingleton k _ baseMap)

/-- The canonical `k`-linear map between relative cotangent spaces. -/
def mapRelCotangent (f : A ⟶ B) : A.relCotangent →ₗ[k] B.relCotangent :=
  letI : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower A B k := .of_algebraMap_eq fun a ↦ by
    rw [RingHom.algebraMap_toAlgebra, eq_comm, ← RingHom.comp_apply]
    exact DFunLike.congr_fun f.residue_comp a
  letI baseMap : Ω[A⁄Λ] →ₗ[A] B.relCotangent := {
    toFun := fun ω ↦ 1 ⊗ₜ[B] KaehlerDifferential.map Λ Λ A B ω
    map_add' := fun _ _ ↦ by rw [map_add, TensorProduct.tmul_add]
    map_smul' := fun a ω ↦ by rw [RingHom.id_apply, map_smul, TensorProduct.tmul_smul] }
  TensorProduct.AlgebraTensorModule.lift (LinearMap.toSpanSingleton k _ baseMap)

@[stacks 06S3 "(2)=>(3)"]
theorem surjective_mapRelCotangent_of_surjective_mapCotangent (hf : Surjective (mapCotangent f)) :
    Surjective (mapRelCotangent f) := by sorry

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
    BaseCat Λ k :=
  ⟨.of Λ k X hX, inferInstance⟩

/-- Given an object `A : BaseCat` and a nontrivial `A`-algebra with
a surjective structure map, `BaseCat.ofSurj` constructs an induced object in `BaseCat`. -/
noncomputable abbrev ofSurj (A : BaseCat.{w} Λ k) (X : Type w) [CommRing X] [Nontrivial X]
    [Algebra Λ X] [Algebra A.obj X] [IsScalarTower Λ A.obj X]
    (h : Surjective (algebraMap A.obj X)) : BaseCat Λ k :=
  ⟨.ofSurj A.obj X h, h.isArtinianRing⟩

/-- Given an object `A : BaseCat` and a nontrivial `A`-algebra `X` with
a surjective structure map, `BaseCat.toOfSurj` upgrades the algebra to a morphism in
`BaseCat` from `A` to the induced object `BaseCat.ofSurj`. -/
noncomputable abbrev toOfSurj (A : BaseCat.{w} Λ k) (X : Type w) [CommRing X] [Nontrivial X]
    [Algebra Λ X] [Algebra A.obj X] [IsScalarTower Λ A.obj X]
    (h : Surjective (algebraMap A.obj X)) : A ⟶ ofSurj A X h :=
  ObjectProperty.homMk (LocAlgCat.toOfSurj A.obj X h)

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

theorem isSmallExtension_of_bijective (h : Function.Bijective f.hom.toAlgHom) :
    IsSmallExtension f := (isSmallExtenstion_iff).mpr ⟨h.surjective, 0, by
  have := h.injective
  rw [RingHom.injective_iff_ker_eq_bot] at this
  simp [this]⟩

theorem IsSmallExtension.toOfSurj_quotient_span_singleton (A : BaseCat.{w} Λ k) {x : A.obj}
    [Nontrivial (A.obj ⧸ Ideal.span {x})] (hx : ∀ y ∈ maximalIdeal A.obj, x * y = 0) :
    IsSmallExtension (A.toOfSurj (A.obj ⧸ Ideal.span {x}) Ideal.Quotient.mk_surjective) := by
  rw [isSmallExtenstion_iff]
  refine ⟨Ideal.Quotient.mk_surjective, x, ?_, hx⟩
  ext; rw [← Submodule.Quotient.mk_eq_zero]
  simp

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
    have : Nontrivial (A.obj ⧸ Ideal.span {x}) := by
      refine Ideal.Quotient.nontrivial_iff.mpr (Ideal.span_singleton_ne_top
        (le_maximalIdeal ?_ x_in))
      rw [Ideal.ne_top_iff_exists_maximal]
      exact ⟨maximalIdeal A.obj, maximalIdeal.isMaximal A.obj,
        le_maximalIdeal (RingHom.ker_ne_top f.hom.toAlgHom)⟩
    have : IsLocalRing (A.obj ⧸ Ideal.span {x}) := .of_surjective' _ Ideal.Quotient.mk_surjective
    let : Algebra (A.obj ⧸ Ideal.span {x}) k :=
      ((algebraMap A.obj (A.obj ⧸ Ideal.span {x})).liftOfSurjective Ideal.Quotient.mk_surjective
        ⟨algebraMap A.obj k, by
          rw [ker_eq_maximalIdeal _ A.obj.surj]
          exact le_maximalIdeal (RingHom.ker_ne_top
            (algebraMap A.obj (A.obj ⧸ Ideal.span {x})))⟩).toAlgebra
    have : IsScalarTower Λ (A.obj ⧸ Ideal.span {x}) k := .of_algebraMap_eq fun r ↦ by
      rw [RingHom.algebraMap_toAlgebra,
        IsScalarTower.algebraMap_apply Λ A.obj (A.obj ⧸ Ideal.span {x}),
        RingHom.liftOfSurjective_comp_apply]
      simp [IsScalarTower.algebraMap_apply Λ A.obj k]
    have : IsScalarTower A.obj (A.obj ⧸ Ideal.span {x}) k := .of_algebraMap_eq fun a ↦ by
      rw [RingHom.algebraMap_toAlgebra, RingHom.liftOfSurjective_comp_apply]
    have aux : ∀ a ∈ Ideal.span {x}, (LocAlgCat.Hom.toAlgHom f.hom) a = 0 := by
      intro _ h; rw [Ideal.mem_span_singleton'] at h
      rcases h with ⟨_, rfl⟩; rw [← RingHom.mem_ker]
      exact Ideal.mul_mem_left _ _ x_in
    let C := ofSurj A (A.obj ⧸ Ideal.span {x}) Ideal.Quotient.mk_surjective
    let g : A ⟶ C := toOfSurj A (A.obj ⧸ Ideal.span {x}) Ideal.Quotient.mk_surjective
    have hg : IsSmallExtension g := IsSmallExtension.toOfSurj_quotient_span_singleton A hx
    let u : C.obj →ₐ[Λ] B.obj := Ideal.Quotient.liftₐ (Ideal.span {x}) f.hom.toAlgHom aux
    have u_surj : Surjective u :=
      Ideal.Quotient.lift_surjective_of_surjective (Ideal.span {x}) aux hf
    have : IsLocalHom u := ⟨u_surj.isLocalHom.map_nonunit⟩
    let f' : C ⟶ B := ObjectProperty.homMk (LocAlgCat.ofHom u (AlgHom.ext fun t ↦ by
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
    have := Submodule.length_le_restrictScalar A.obj (A.obj ⧸ Ideal.span {x})
      (A.obj ⧸ Ideal.span {x}) ⊤
    rw [Module.length_top, restrictScalars_top, Module.length_top] at this
    rw [← ENat.coe_lt_coe, ← hlen, ← hm]
    exact lt_of_le_of_lt this (length_quotient_lt (Ideal.span {x}) (by simpa))

section

variable [IsLocalRing Λ] [Module.Finite Λ k]

open Module in
@[stacks 06GG]
theorem finrank_mul_length {M : Type*} [AddCommGroup M] [Module A.obj M] [Module Λ M]
    [IsScalarTower Λ A.obj M] : finrank (ResidueField Λ) k * length A.obj M = length Λ M := by
  have : (finrank (ResidueField Λ) k : ENat) ≠ 0 := by
    rw [ne_eq, ← Nat.cast_zero (R := ENat), ENat.coe_inj, finrank_eq_zero_iff_of_free,
      not_subsingleton_iff_nontrivial]
    infer_instance
  by_cases h : length A.obj M = ⊤
  · rw [h, ENat.mul_top this, eq_comm, eq_top_iff, ← h]
    have := Submodule.length_le_restrictScalar Λ A.obj M ⊤
    rwa [length_top, Submodule.restrictScalars_top, length_top] at this
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = length A.obj M := ENat.ne_top_iff_exists.mp h
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
    by_cases h' : ∃ (x : M), x ≠ 0 ∧ ¬ Function.Surjective (LinearMap.toSpanSingleton A.obj M x)
    · rcases h' with ⟨x, x_ne, hx⟩
      rw [← LinearMap.range_eq_top, LinearMap.range_toSpanSingleton] at hx
      let N := Submodule.span A.obj {x}
      let Q := M ⧸ N
      have eq_add := Module.length_eq_add_of_exact N.subtype N.mkQ N.subtype_injective
        N.mkQ_surjective (LinearMap.exact_subtype_mkQ N)
      have eq_add' := Module.length_eq_add_of_exact (N.restrictScalars Λ).subtype
        (N.restrictScalars Λ).mkQ N.subtype_injective N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N)
      rw [← ne_eq, ← lt_top_iff_ne_top, eq_add, ENat.add_lt_top, lt_top_iff_ne_top,
        lt_top_iff_ne_top] at ne_top
      obtain ⟨m, hm⟩ : ∃ m : ℕ, m = length A.obj N := ENat.ne_top_iff_exists.mp ne_top.left
      obtain ⟨l, hl⟩ : ∃ l : ℕ, l = length A.obj Q := ENat.ne_top_iff_exists.mp ne_top.right
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
    replace h' : IsSimpleModule A.obj M := by
      rw [isSimpleModule_iff_toSpanSingleton_surjective]
      push Not at h'; exact ⟨this, h'⟩
    rw [length_eq_one, mul_one]
    rw [isSimpleModule_iff_quot_maximal] at h'
    rcases h' with ⟨I, hI, h'⟩
    replace h' : Nonempty (M ≃ₗ[Λ] k) := by
      rcases h' with ⟨e⟩
      replace hI := (isMaximal_iff A.obj).mp hI
      let f : (A.obj ⧸ I) ≃ₐ[Λ] ResidueField A.obj :=
        Ideal.quotientEquivAlg I (maximalIdeal A.obj) (AlgEquiv.refl (R := Λ)) (by simp [hI])
      exact ⟨(e.restrictScalars Λ).trans <| f.toLinearEquiv.trans A.obj.residueEquiv.toLinearEquiv⟩
    rcases h' with ⟨e⟩
    rw [e.length_eq, ← Module.length_eq_finrank, eq_comm]
    exact Module.length_eq_of_surjective (R := ResidueField Λ) (S := Λ) (M := k) residue_surjective

variable (A) in
theorem isFiniteLength : IsFiniteLength Λ A.obj := by
  rw [← Module.length_ne_top_iff, ← finrank_mul_length (A := A)]
  have (n : ℕ) (s : ENat) (hs : s ≠ ⊤) : n * s ≠ ⊤ := by
    lift s to ℕ using hs
    exact WithTop.coe_ne_top
  exact this _ _ Module.length_ne_top

instance : IsNoetherian Λ A.obj :=
  (isFiniteLength_iff_isNoetherian_isArtinian.mp (isFiniteLength A)).left

instance : IsArtinian Λ A.obj :=
  (isFiniteLength_iff_isNoetherian_isArtinian.mp (isFiniteLength A)).right

instance isArtinianRing_pullback (f : A ⟶ C) (g : B ⟶ C) :
    IsArtinianRing (f.hom.toAlgHom.pullback g.hom.toAlgHom) := by
  set PB := f.hom.toAlgHom.pullback g.hom.toAlgHom
  rw [isArtinianRing_iff_isFiniteLength, ← Module.length_ne_top_iff]
  refine ne_top_of_le_ne_top (b := Module.length Λ PB) ?_ ?_
  · refine ne_top_of_le_ne_top (b := Module.length Λ (A.obj × B.obj)) ?_ ?_
    · rw [Module.length_prod]
      exact WithTop.add_ne_top.mpr ⟨Module.length_ne_top, Module.length_ne_top⟩
    · exact Module.length_le_of_injective (Submodule.subtype PB.toSubmodule)
        (Submodule.subtype_injective _)
  have := Submodule.length_le_restrictScalar Λ PB PB ⊤
  rwa [Module.length_top, Submodule.restrictScalars_top, Module.length_top] at this

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
      rcases LocAlgCat.exists_mem_maximalIdeal_toAlgHom_add_eq g.hom f.hom
        (IsSmallExtension.surjective g) w with ⟨z, m, m_in, hm⟩
      exact ⟨z, w + m, hm.symm, by rw [add_mul, hw, mul_comm, hx m m_in, add_zero]⟩
    · suffices ¬ IsUnit b by simpa [← Subtype.val_inj] using hx b this
      intro hb
      simp only [AlgHom.mem_equalizer, AlgHom.coe_comp, Function.comp_apply, AlgHom.fst_apply,
        AlgHom.snd_apply] at hab
      have : IsUnit ((LocAlgCat.Hom.toAlgHom f.hom) a) := by
        rwa [hab, isUnit_map_iff]
      apply IsLocalHom.map_nonunit at this
      simp [AlgHom.isUnit_pullback_mk_iff] at h
      grind

/-- xxxx -/
abbrev ofPullbackOfIsSeparable [Algebra.IsSeparable (ResidueField Λ) k] (f : A ⟶ C) (g : B ⟶ C) :
    BaseCat Λ k :=
  letI : Algebra (f.hom.toAlgHom.pullback g.hom.toAlgHom) k :=
    (A.obj.residue.comp (f.hom.toAlgHom.pullbackFst g.hom.toAlgHom)).toAlgebra
  letI : IsScalarTower Λ (f.hom.toAlgHom.pullback g.hom.toAlgHom) k := .of_algebraMap_eq (by
    simp [RingHom.algebraMap_toAlgebra])
  ⟨.of Λ k (f.hom.toAlgHom.pullback g.hom.toAlgHom)
    (LocAlgCat.surjective_residue_comp_pullbackFst_of_isSeparable f.hom g.hom), inferInstance⟩

end

end BaseCat

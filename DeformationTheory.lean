/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import Mathlib

@[expose] public section

noncomputable section

local notation "𝓀" => IsLocalRing.ResidueField
local notation "𝔪" => IsLocalRing.maximalIdeal

universe w w' v u

/-! # `IsLocalHom` instances for `AlgHom`
goes to `RingTheory/LocalRing/RingHom/Basic.lean`-/

section AlgHom

variable {R S T : Type*} [Semiring R] [Semiring S] [Semiring T]
variable {A : Type*} [CommSemiring A] [Algebra A R] [Algebra A S] [Algebra A T]

variable (A) in
@[instance]
theorem isLocalHom_algHomId : IsLocalHom (AlgHom.id A R) := ⟨fun _ ↦ id⟩

@[instance]
theorem AlgHom.isLocalHom_comp (f : R →ₐ[A] S) (g : S →ₐ[A] T) [IsLocalHom f] [IsLocalHom g] :
    IsLocalHom (g.comp f) where
  map_nonunit a := IsLocalHom.map_nonunit a ∘ IsLocalHom.map_nonunit (f := g) (f a)

-- see note [lower instance priority]
@[instance 100]
theorem isLocalHom_toAlgHom {F : Type*} [FunLike F R S]
    [AlgHomClass F A R S] (f : F) [IsLocalHom f] : IsLocalHom (f : R →ₐ[A] S) :=
  ⟨IsLocalHom.map_nonunit (f := f)⟩

end AlgHom

-------------------------------------------------------------------------------------

/-! # introduce `IsLocalRing.ResidueField.mapₐ`
goes to `RingTheory/LocalRing/ResidueField/Basic.lean`-/

namespace IsLocalRing.ResidueField

variable {R : Type*} {S : Type*} {T : Type*} [CommRing R] [IsLocalRing R]
  [CommRing S] [IsLocalRing S] [CommRing T] [IsLocalRing T]

section equivOfSurj

theorem map_surjective {f : R →+* S} (h : Function.Surjective f) :
    letI := h.isLocalHom
    Function.Surjective (map f) := fun y ↦ by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨r, rfl⟩ := h s
  exact ⟨Ideal.Quotient.mk _ r, rfl⟩

/-- A surjective ring homomorphism between local rings induces an equivalence of residue fields. -/
noncomputable def equivOfSurj {f : R →+* S} (h : Function.Surjective f) : 𝓀 R ≃+* 𝓀 S :=
  letI := h.isLocalHom
  .ofBijective (map f) ⟨RingHom.injective (map f), map_surjective h⟩

@[simp]
lemma equivOfSurj_apply {f : R →+* S} (h : Function.Surjective f) (x : 𝓀 R) :
    letI := h.isLocalHom; equivOfSurj h x = map f x := rfl

lemma equivOfSurj_eq_mapEquiv (e : R ≃+* S) : equivOfSurj (e : R →+* S).surjective =
    mapEquiv e := by ext; rfl

end equivOfSurj

section algMap

variable {A : Type*} [CommRing A] [Algebra A R] [Algebra A S] [Algebra A T]

/-- The algebra map version of `IsLocalRing.ResidueField.map`. -/
noncomputable def mapₐ (f : R →ₐ[A] S) [IsLocalHom f] :
    ResidueField R →ₐ[A] ResidueField S where
  __ := map f
  commutes' r := by
    rw [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe, IsScalarTower.algebraMap_apply A R (ResidueField R) r, algebraMap_eq,
      ← RingHom.comp_apply, map_comp_residue, RingHom.coe_comp, RingHom.coe_coe,
      Function.comp_apply, AlgHom.commutes, IsScalarTower.algebraMap_apply A S (ResidueField S) r,
      algebraMap_eq]

lemma mapₐ_apply (f : R →ₐ[A] S) [IsLocalHom f] (x : ResidueField R) : mapₐ f x = map f x := rfl

@[simp]
lemma mapₐ_id : mapₐ (AlgHom.id A R) = AlgHom.id A (ResidueField R) := by ext; simp [mapₐ_apply]

theorem mapₐ_comp (f : R →ₐ[A] S) (g : S →ₐ[A] T) [IsLocalHom f] [IsLocalHom g] :
    mapₐ (g.comp f) = (mapₐ g).comp (mapₐ f) := by ext; simp [AlgHom.comp_toRingHom, mapₐ_apply]

/-- An algebra isomorphism defines an algebra isomorphism between residue fields. -/
noncomputable def mapAlgEquiv (f : R ≃ₐ[A] S) : ResidueField R ≃ₐ[A] ResidueField S :=
  .ofRingEquiv (f := mapEquiv f.toRingEquiv) fun r ↦ by
    simp_rw [AlgEquiv.toRingEquiv_eq_coe, mapEquiv_apply, ← AlgEquiv.coe_ringHom_commutes,
      ← mapₐ_apply, AlgHom.commutes]

@[simp]
lemma mapAlgEquiv_apply (f : R ≃ₐ[A] S) (x : ResidueField R) :
    mapAlgEquiv f x = mapₐ (f : R →ₐ[A] S) x := rfl

/-- `AlgEquiv` version of `IsLocalRing.ResidueField.equivOfSurj`. -/
noncomputable def algEquivOfSurj {f : R →ₐ[A] S} (h : Function.Surjective f) :
    𝓀 R ≃ₐ[A] 𝓀 S :=
  letI : IsLocalHom f := ⟨h.isLocalHom.map_nonunit⟩
  .ofBijective (mapₐ f) ⟨RingHom.injective (map (f : R →+* S)), map_surjective h⟩

@[simp]
lemma algEquivOfSurj_apply {f : R →ₐ[A] S} (h : Function.Surjective f) (x : 𝓀 R) :
    letI : IsLocalHom f := ⟨h.isLocalHom.map_nonunit⟩
    algEquivOfSurj h x = mapₐ f x := rfl

lemma algEquivOfSurj_eq_mapAlgEquiv (e : R ≃ₐ[A] S) :
    algEquivOfSurj (show Function.Surjective (e : R →ₐ[A] S) from fun r ↦ e.surjective r) =
      mapAlgEquiv e := by ext; rfl

end algMap

end IsLocalRing.ResidueField
--------------------------------------------------------------------------------

namespace IsLocalRing

open Function

variable {R S A : Type*}  [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    [CommRing A] [Algebra A R] [Algebra A S]

theorem surjective_mapCotangent_of_surjective {f : R →ₐ[A] S} (h : Surjective f) :
    Surjective ((maximalIdeal R).mapCotangent (maximalIdeal S) f
      (((local_hom_TFAE f).out 0 3).mp h.isLocalHom)) := by
  have : IsLocalHom (f : R →+* S) := h.isLocalHom
  intro b; induction b using Submodule.Quotient.induction_on with
  | H z =>
    rcases z with ⟨z, hz⟩
    rcases h z with ⟨y, hy⟩
    suffices y ∈ maximalIdeal R by
      use (maximalIdeal R).toCotangent ⟨y, this⟩
      simp_rw [← hy]; rfl
    rw [← residue_eq_zero_iff, ← hy] at hz
    change residue S ((f : R →+* S) y) = 0 at hz
    rwa [← ResidueField.map_residue (f : R →+* S), ← RingHom.mem_ker,
      (RingHom.injective_iff_ker_eq_bot _).mp (show Injective (ResidueField.map (f : R →+* S)) from
        RingHom.injective _), Submodule.mem_bot, residue_eq_zero_iff] at hz

end IsLocalRing

--------------------------------------------------------------------------------

/-! # from PR -/

theorem Ideal.isLinearTopology {R : Type*} [CommRing R] (I : Ideal R) :
    @IsLinearTopology R R _ _ _ I.adicTopology :=
  letI := I.adicTopology
  IsLinearTopology.mk_of_hasBasis _ I.hasBasis_nhds_zero_adic

namespace WithIdeal

variable {R : Type*} [CommRing R] [WithIdeal R]

instance (priority := 100) : IsLinearTopology R R := i.isLinearTopology

theorem uniformContinuous_of_map_le {S : Type*} [CommRing S] [WithIdeal S] {f : R →+* S}
    (hf : i.map f ≤ i) : UniformContinuous f := uniformContinuous_of_continuousAt_zero f (by
  rw [ContinuousAt, map_zero, i.hasBasis_nhds_zero_adic.tendsto_iff i.hasBasis_nhds_zero_adic]
  refine fun n _ ↦ ⟨n, trivial, Ideal.map_le_iff_le_comap.mp ?_⟩
  simpa [Ideal.map_pow] using Ideal.pow_right_mono hf n)

/-- A ring equivalence induces a uniform equivalence with respect to the adic topologies,
provided it preserves the defining ideals. -/
def uniformEquiv {S : Type*} [CommRing S] [WithIdeal S] (e : R ≃+* S)
    (h : i.map e.toRingHom = i) : UniformEquiv R S where
  __ := e
  uniformContinuous_toFun := uniformContinuous_of_map_le (f := e.toRingHom) (by rw [h])
  uniformContinuous_invFun := uniformContinuous_of_map_le (f := e.symm.toRingHom) (by simp [← h])

lemma isTopologicallyNilpotent_of_mem {a : R} (ha : a ∈ i) : IsTopologicallyNilpotent a := by
  suffices ∀ m : ℕ, ∃ n₀, ∀ n, n₀ ≤ n → a ^ n ∈ i ^ m by
    simpa [IsTopologicallyNilpotent, i.hasBasis_nhds_zero_adic.tendsto_right_iff]
  exact fun m ↦ ⟨m, fun n hn ↦ Ideal.pow_le_pow_right hn (Ideal.pow_mem_pow ha _)⟩

end WithIdeal

section congrRingEquiv

variable {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (e : R ≃+* S)

theorem IsPrecomplete.congr_ringEquiv : IsPrecomplete (I.map e) S ↔ IsPrecomplete I R := by
  let : WithIdeal R := ⟨I⟩
  let : WithIdeal S := ⟨I.map e⟩
  rw [iff_comm, IsAdic.isPrecomplete_iff (by rfl), IsAdic.isPrecomplete_iff (by rfl)]
  exact completeSpace_congr (e := WithIdeal.uniformEquiv e rfl) (by
    simpa using UniformEquiv.isUniformEmbedding ..)

theorem IsHausdorff.congr_ringEquiv : IsHausdorff (I.map e) S ↔ IsHausdorff I R := by
  let : WithIdeal R := ⟨I⟩
  let : WithIdeal S := ⟨I.map e⟩
  rw [iff_comm, IsAdic.isHausdorff_iff rfl, IsAdic.isHausdorff_iff rfl]
  exact ⟨fun _ ↦ (WithIdeal.uniformEquiv e rfl).toHomeomorph.t2Space, fun _ ↦
    (WithIdeal.uniformEquiv e rfl).toHomeomorph.symm.t2Space⟩

theorem IsAdicComplete.congr_ringEquiv : IsAdicComplete (I.map e) S ↔ IsAdicComplete I R := by
  simp [isAdicComplete_iff, IsHausdorff.congr_ringEquiv, IsPrecomplete.congr_ringEquiv]

end congrRingEquiv

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

instance {R : Type*} [CommRing R] [IsLocalRing R] [IsAdicComplete (𝔪 R) R] :
    IsAdicComplete (𝔪 (ULift.{u} R)) (ULift.{u} R) := by
  rw [← IsAdicComplete.congr_ringEquiv _ ULift.ringEquiv,
    IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv ULift.ringEquiv)]
  infer_instance -/

--------------------------------------------------------------------------------

/-- An Artinian local ring is adic complete with respect to its maximal ideal. -/
instance IsArtinianRing.isAdicComplete {R : Type*} [CommRing R] [IsArtinianRing R]
    [IsLocalRing R] : IsAdicComplete (IsLocalRing.maximalIdeal R) R where
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
  have (q : Submodule A ↥(restrictScalars A p)) : Subsingleton (e ⁻¹' {q}) := ⟨by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    simp only [Subtype.mk.injEq]
    apply e.injective; grind⟩
  have : ∀ q : Submodule A ↥(restrictScalars A p), Order.krullDim (e ⁻¹' {q}) ≤ (0 : ℕ) := by
    intro p; by_cases h : Nonempty (e ⁻¹' {p})
    · simp [Order.krullDim_eq_zero]
    rw [not_nonempty_iff] at h
    simp [Order.krullDim_eq_bot]
  simpa using Order.krullDim_le_of_krullDim_preimage_le' e e.monotone this

theorem Submodule.length_quotient_lt {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [IsArtinian R M] [IsNoetherian R M] (p : Submodule R M) (h : p ≠ ⊥) :
    Module.length R (M ⧸ p) < Module.length R M := by
  rw [Module.length_eq_add_of_exact p.subtype p.mkQ p.subtype_injective p.mkQ_surjective
    (LinearMap.exact_subtype_mkQ p)]
  nth_rw 1 [← zero_add (Module.length R (M ⧸ p)), ENat.add_lt_add_iff_right Module.length_ne_top]
  exact Module.length_pos_iff.mpr (nontrivial_iff_ne_bot.mpr h)

@[to_dual]
theorem WithBot.unbot_inj {α : Type*} {a b : WithBot α} (ha : a ≠ ⊥) (hb : b ≠ ⊥) :
    a.unbot ha = b.unbot hb ↔ a = b := by
  rw [WithBot.unbot_eq_iff, WithBot.coe_unbot]

theorem Module.length_eq_of_surjective {R S M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [CommRing S] [Algebra S R] [Module S M] [IsScalarTower S R M]
    (h : Function.Surjective (algebraMap S R)) : Module.length S M = Module.length R M := by
  have : RingHomSurjective (algebraMap S R) := ⟨h⟩
  let f : M →ₛₗ[algebraMap S R] M := ⟨AddHom.id M, by simp⟩
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f Function.bijective_id)]

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

-- goes to `Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic`

theorem RingHom.ker_isMaximal_of_isIntegral (R k : Type*) [CommRing R] [Field k]
    [Algebra R k] [Algebra.IsIntegral R k] : (RingHom.ker (algebraMap R k)).IsMaximal := by
  have := Ideal.bot_isMaximal (K := k)
  rw [ker, Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  exact isField_of_isIntegral_of_isField Ideal.algebraMap_quotient_injective
    (Ideal.Quotient.field _).toIsField

-- goes to `RingTheory/LocalRing/ResidueField/Instances.lean`
/- add `public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic`
 `public import Mathlib.RingTheory.Finiteness.Quotient` -/

namespace IsLocalRing

instance ResidueField.algebraOfIsIntegral {R k : Type*} [CommRing R] [IsLocalRing R] [Field k]
    [Algebra R k] [Algebra.IsIntegral R k] : Algebra (ResidueField R) k :=
  (Ideal.Quotient.lift (maximalIdeal R) (algebraMap R k)
    (by simp [← eq_maximalIdeal (RingHom.ker_isMaximal_of_isIntegral R k)])).toAlgebra

instance ResidueField.isScalarTowerOfIsIntegral {R k : Type*} [CommRing R] [IsLocalRing R]
    [Field k] [Algebra R k] [Algebra.IsIntegral R k] : IsScalarTower R (ResidueField R) k :=
  .of_algebraMap_eq fun _ ↦ rfl

instance {R k : Type*} [CommRing R] [IsLocalRing R] [Field k] [Algebra R k] [Module.Finite R k] :
    Module.Finite (ResidueField R) k := .of_equiv_equiv
  (Ideal.quotEquivOfEq (show Ideal.comap (algebraMap R k) ⊥ = maximalIdeal R by
    rw [← eq_maximalIdeal (RingHom.ker_isMaximal_of_isIntegral R k), RingHom.ker]))
  (RingEquiv.quotientBot k) (by ext; rfl)

end IsLocalRing
--------------------------------------------------------------------------------

lemma Ideal.Quotient.mk_smul_toCotangent {R : Type*} [CommRing R] (I : Ideal R) (a : R) (b : I) :
    (Ideal.Quotient.mk I a) • (I.toCotangent b) = I.toCotangent (a • b) := rfl

lemma IsLocalRing.residue_smul_toCotangent {R : Type*} [CommRing R] [IsLocalRing R] (r : R)
    (a : maximalIdeal R) : residue R r • ((maximalIdeal R).toCotangent a) =
      (maximalIdeal R).toCotangent (r • a) := rfl

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

theorem AlgEquiv.subsingleton_of_surjective {A R S : Type*} [CommSemiring A] [Semiring R]
    [Semiring S] [Algebra A R] [Algebra A S] (h : Function.Surjective (algebraMap A S)) :
    Subsingleton (R ≃ₐ[A] S) where
  allEq e f := AlgEquiv.ext fun s ↦ by
    obtain ⟨a, ha⟩ := h (e s)
    have hs : s = algebraMap A R a := by
      apply e.injective
      simp [← ha]
    simp [hs]

--------------------------------------------------------------------------------

/-! # The Category of Local Algebras with a Fixed Residue Field

* `DeformationTheory.LocAlgCat` : The type of objects in the category of local `Λ`-algebras
  with residue field `k`. An object consists of a local `Λ`-algebra `A` equipped
  with a specified `Λ`-algebra isomorphism from its residue field to `k`.

* `DeformationTheory.LocAlgCat.Hom` : The type of morphisms between objects in `LocAlgCat Λ k`.
  A morphism `f : A ⟶ B` is a local `Λ`-algebra homomorphism that is compatible with
  the specified residue field isomorphisms.

-/

namespace DeformationTheory

open IsLocalRing CategoryTheory Function

variable {Λ : Type u} [CommRing Λ]
variable {k : Type v} [Field k] [Algebra Λ k]

set_option backward.privateInPublic true in
/-- The category of local `Λ`-algebras with residue field `k` and their morphisms. -/
structure LocAlgCat (Λ : Type u) (k : Type v) [CommRing Λ] [Field k] [Algebra Λ k] where
  private mk ::
  /-- The underlying type of the local `Λ`-algebras. -/
  carrier : Type w
  [commRing : CommRing carrier]
  [localRing : IsLocalRing carrier]
  [algebra : Algebra Λ carrier]
  e : 𝓀 carrier ≃ₐ[Λ] k

namespace LocAlgCat

variable {A B C : LocAlgCat.{w} Λ k} {X Y Z : Type w} [CommRing X] [IsLocalRing X] [Algebra Λ X]
  [CommRing Y] [IsLocalRing Y] [Algebra Λ Y] [CommRing Z] [IsLocalRing Z] [Algebra Λ Z]
  {eX : 𝓀 X ≃ₐ[Λ] k} {eY : 𝓀 Y ≃ₐ[Λ] k} {eZ : 𝓀 Z ≃ₐ[Λ] k}

attribute [instance] localRing commRing algebra

initialize_simps_projections LocAlgCat (-localRing, -commRing, -algebra)

instance : CoeSort (LocAlgCat Λ k) (Type w) := ⟨carrier⟩

attribute [coe] carrier

instance : Algebra A k := ((A.e : 𝓀 A →+* k).comp (residue A)).toAlgebra

instance : IsScalarTower Λ A k where
  smul_assoc r a x := by
    simp only [Algebra.smul_def, map_mul, ← mul_assoc]
    congr; exact AlgEquiv.commutes A.e r

@[simp]
lemma e_residue_apply (a : A) : A.e (residue A a) = algebraMap A k a := rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The object in the category of local `Λ`-algebras associated to a type equipped with
the appropriate typeclasses. This is a preferred way to construct a term of `LocAlgCat Λ k`. -/
abbrev of (X : Type w) [CommRing X] [IsLocalRing X] [Algebra Λ X] (eX : 𝓀 X ≃ₐ[Λ] k) :
    LocAlgCat Λ k := ⟨X, eX⟩

variable (Λ k) in
lemma coe_of (X : Type w) [CommRing X] [IsLocalRing X] [Algebra Λ X] (eX : 𝓀 X ≃ₐ[Λ] k) :
    (of X eX : Type w) = X := rfl

variable (Λ k) in
lemma of_carrier (A : LocAlgCat.{w} Λ k) : of A A.e = A := rfl

/-- Given an object `A : LocAlgCat Λ k` and a surjective map `f : ↑A →ₐ[Λ] X` to a
nontrivial `Λ`-algebra `X`, `LocAlgCat.ofSurj` constructs an induced object of `LocAlgCat Λ k`. -/
noncomputable def ofSurj (A : LocAlgCat.{w} Λ k) (X : Type w) [CommRing X] [Nontrivial X]
    [Algebra Λ X] (f : A →ₐ[Λ] X) (hf : Surjective f) : LocAlgCat.{w} Λ k :=
  letI : IsLocalRing X := IsLocalRing.of_surjective' (f : A →+* X) hf
  letI : IsLocalHom f := ⟨hf.isLocalHom.map_nonunit⟩
  of X ((ResidueField.algEquivOfSurj (f := f) hf).symm.trans A.e)

lemma coe_ofSurj (A : LocAlgCat.{w} Λ k) (X : Type w) [CommRing X] [Nontrivial X] [Algebra Λ X]
    (f : A →ₐ[Λ] X) (hf : Surjective f) : (ofSurj A X f hf : Type w) = X := rfl

lemma e_ofSurj (A : LocAlgCat.{w} Λ k) (X : Type w) [CommRing X] [Nontrivial X]
    [Algebra Λ X] (f : A →ₐ[Λ] X) (hf : Surjective f) :
  letI : IsLocalRing X := IsLocalRing.of_surjective' (f : A →+* X) hf
  letI : IsLocalHom f := ⟨hf.isLocalHom.map_nonunit⟩
  (ofSurj A X f hf).e = (ResidueField.algEquivOfSurj (f := f) hf).symm.trans A.e := rfl

/-- The type of morphisms in `LocAlgCat Λ k`. -/
@[ext]
structure Hom (A B : LocAlgCat.{w} Λ k) where
  /-- The underlying algebra map. -/
  toAlgHom : A →ₐ[Λ] B
  [localhom : IsLocalHom toAlgHom]
  e_comp : (B.e : 𝓀 B →ₐ[Λ] k).comp (ResidueField.mapₐ toAlgHom) = A.e

attribute [instance] Hom.localhom

initialize_simps_projections Hom (-localhom)

/-
instance : FunLike (Hom A B) A B where
  coe f := f.toAlgHom
  coe_injective' f g h := by
    rcases f with ⟨f, _⟩
    rcases g with ⟨g, _⟩
    simpa using h-/

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : Category (LocAlgCat.{w} Λ k) where
  Hom A B := Hom A B
  id A := ⟨AlgHom.id Λ A, by simp⟩
  comp {A B C} f g := ⟨g.toAlgHom.comp f.toAlgHom, by
    rw [ResidueField.mapₐ_comp, ← AlgHom.comp_assoc, g.e_comp, f.e_comp]⟩

/-instance : ConcreteCategory (LocAlgCat.{w} Λ k) Hom where
  hom := id
  ofHom := id-/
/-
/-- Cast a morphism of `LocAlgCat` into an `AlgHom`. -/
abbrev Hom.toAlgHom {A B : LocAlgCat.{w} Λ k} (f : A.Hom B) : A →ₐ[Λ] B :=
  f.toAlgHom

/-- See Note [custom simps projection] -/
def Hom.Simps.toAlgHom {A B : LocAlgCat.{w} Λ k} (f : A.Hom B) : A →ₐ[Λ] B :=
  f.toAlgHom-/

lemma surjective_residueFieldMapₐ (f : A ⟶ B) : Surjective (ResidueField.mapₐ f.toAlgHom) := by
  intro x
  rcases A.e.surjective (B.e x) with ⟨y, hy⟩
  use y; rw [← B.e.injective.eq_iff, ← hy]
  exact DFunLike.congr_fun f.e_comp y

open ResidueField in
lemma exists_mem_maximalIdeal_toAlgHom_add (f : A ⟶ C) (g : B ⟶ C) (hf : Surjective f.toAlgHom)
    (a : A) : ∃ (b : B) (m : A), m ∈ 𝔪 A ∧ f.toAlgHom (a + m) = g.toAlgHom b := by
  rcases surjective_residueFieldMapₐ g (mapₐ f.toAlgHom (residue A a)) with ⟨u, hu⟩
  rcases residue_surjective (R := B) u with ⟨b, rfl⟩
  rw [mapₐ_apply, mapₐ_apply, map_residue, map_residue, ← sub_eq_zero, ← map_sub,
    residue_eq_zero_iff, ← map_maximalIdeal_of_surjective (f.toAlgHom : A →+* C) hf,
    Ideal.mem_map_iff_of_surjective (f.toAlgHom : A →+* C) hf] at hu
  rcases hu with ⟨m, hm⟩
  rw [eq_sub_iff_add_eq', ← map_add] at hm
  exact ⟨b, m, hm⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Typecheck an `AlgHom` compatible with residue maps as a morphism in `LocAlgCat`. -/
abbrev ofHom (f : X →ₐ[Λ] Y) [IsLocalHom f] (hf : (eY : 𝓀 Y →ₐ[Λ] k).comp (ResidueField.mapₐ f) =
    eX) : of X eX ⟶ of Y eY := ⟨f, hf⟩

/-- Given an object `A : LocAlgCat Λ k` and a surjective map `f : ↑A →ₐ[Λ] X` to a
nontrivial `Λ`-algebra `X`, `LocAlgCat.toOfSurj` upgrades `f` to a morphism in `LocAlgCat Λ k`
from `A` to the induced object `LocAlgCat.ofSurj A X f hf`. -/
noncomputable def toOfSurj (A : LocAlgCat.{w} Λ k) (X : Type w) [CommRing X] [Nontrivial X]
    [Algebra Λ X] (f : A →ₐ[Λ] X) (hf : Surjective f) : A ⟶ ofSurj A X f hf :=
  letI : IsLocalRing X := IsLocalRing.of_surjective' (f : A →+* X) hf
  letI : IsLocalHom f := ⟨hf.isLocalHom.map_nonunit⟩
  ofHom f (by ext; simp [ResidueField.mapₐ_apply, AlgEquiv.symm_apply_eq])

@[simp]
lemma toAlgHom_toOfSurj (A : LocAlgCat.{w} Λ k) (X : Type w) [CommRing X] [Nontrivial X]
    [Algebra Λ X] (f : A →ₐ[Λ] X) (hf : Surjective f) : (toOfSurj A X f hf).toAlgHom = f := rfl

/-- Given morphisms `f : A ⟶ C` and `g : B ⟶ C` in `LocAlgCat Λ k`
where `g.toAlgHom` is surjective, `ofPullback f g h` constructs the pullback
`AlgHom.pullback f.toAlgHom g.toAlgHom` as an object in `LocAlgCat Λ k`. -/
abbrev ofPullback (f : A ⟶ C) (g : B ⟶ C) (h : Surjective g.toAlgHom) : LocAlgCat.{w} Λ k :=
  of (AlgHom.pullback f.toAlgHom g.toAlgHom) ((ResidueField.algEquivOfSurj
    (f.toAlgHom.surjective_pullbackFst_of_surjective g.toAlgHom h)).trans A.e)

lemma coe_ofPullback (f : A ⟶ C) (g : B ⟶ C) (hg : Surjective g.toAlgHom) :
    (ofPullback f g hg : Type w) = f.toAlgHom.pullback g.toAlgHom := rfl

/-- Upgrades the first projection map from the pullback algebra to
a morphism in `LocAlgCat Λ k`. -/
abbrev fromOfPullback (f : A ⟶ C) (g : B ⟶ C) (hg : Surjective g.toAlgHom) :
    ofPullback f g hg ⟶ A := .mk (f.toAlgHom.pullbackFst g.toAlgHom) rfl

/-
@[simp] lemma hom_id : (𝟙 A : A ⟶ A).toAlgHom = AlgHom.id Λ A := rfl

@[simp] lemma id_apply (a : A) : (𝟙 A : A ⟶ A) a = a := by simp

@[simp] lemma hom_comp (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).toAlgHom = g.toAlgHom.comp f.toAlgHom := rfl

@[simp] lemma comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a) := by simp

@[ext] lemma hom_ext {f g : A ⟶ B} (hf : f.toAlgHom = g.toAlgHom) : f = g := Hom.ext hf

@[simp] lemma toAlgHom_ofHom (f : X →ₐ[Λ] Y) [IsLocalHom f]
    (hf : (eY : 𝓀 Y →ₐ[Λ] k).comp (ResidueField.mapₐ f) = eX) : (ofHom f hf).toAlgHom = f := rfl

@[simp] lemma ofhom_toAlgHom (f : A ⟶ B) : ofHom f.toAlgHom f.e_comp = f := rfl

@[simp] lemma ofHom_id : ofHom (.id Λ X) (by simp) = 𝟙 (of X eX) := rfl

@[simp] lemma ofHom_comp (f : X →ₐ[Λ] Y) [IsLocalHom f]
    (hf : (eY : 𝓀 Y →ₐ[Λ] k).comp (ResidueField.mapₐ f) = eX) (g : Y →ₐ[Λ] Z) [IsLocalHom g]
      (hg : (eZ : 𝓀 Z →ₐ[Λ] k).comp (ResidueField.mapₐ g) = (eY : 𝓀 Y →ₐ[Λ] k)) :
    ofHom (g.comp f) (by rw [ResidueField.mapₐ_comp, ← AlgHom.comp_assoc, hg, hf]) =
      ofHom f hf ≫ ofHom g hg := rfl

lemma ofHom_apply (f : X →ₐ[Λ] Y) [IsLocalHom f]
    (hf : (eY : 𝓀 Y →ₐ[Λ] k).comp (ResidueField.mapₐ f) = eX) (x : X) : ofHom f hf x = f x := rfl

lemma inv_hom_apply (e : A ≅ B) (x : A) : e.inv (e.hom x) = x := by simp

lemma hom_inv_apply (e : A ≅ B) (x : B) : e.hom (e.inv x) = x := by simp

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
    {_ : IsLocalRing Y} {_ : Algebra Λ Y} {eX : 𝓀 X ≃ₐ[Λ] k} {eY : 𝓀 Y ≃ₐ[Λ] k} (e : X ≃ₐ[Λ] Y)
    (he : (ResidueField.mapAlgEquiv e).trans eY = eX) : of X eX ≅ of Y eY where
  hom := ofHom (e : X →ₐ[Λ] Y) (by rw [← he]; ext; simp)
  inv := ofHom (e.symm : Y →ₐ[Λ] X) (by ext; simp [← he, ← AlgEquiv.toRingHom_trans,
    ResidueField.mapₐ_apply])
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
lemma mapAlgEquiv_ofIso_trans_e (i : A ≅ B) :
    (ResidueField.mapAlgEquiv (ofIso i)).trans B.e = A.e := by
  ext
  simpa using DFunLike.congr_fun i.hom.e_comp _

/-- Algebra equivalences between `Algebra`s compatible with residue isomorphisms are
the same as isomorphisms in `LocAlgCat`. -/
@[simps]
def isoEquivSubtypeAlgEquiv : (of X eX ≅ of Y eY) ≃
    { e : X ≃ₐ[Λ] Y // (ResidueField.mapAlgEquiv e).trans eY = eX } where
  toFun i := ⟨ofIso i, mapAlgEquiv_ofIso_trans_e i⟩
  invFun f := isoMk f.val f.prop
-/

end LocAlgCat

-----------------------------------------------------------------------------------------

/-- The complete base category for deformation theory over `Λ`. This is the full subcategory of
`LocAlgCat Λ k` consisting of complete Noetherian local `Λ`-algebras with residue field `k`. -/
abbrev CBaseCat (Λ : Type u) [CommRing Λ] (k : Type v) [Field k] [Algebra Λ k] :=
  ObjectProperty.FullSubcategory fun A : LocAlgCat.{w} Λ k ↦
    IsNoetherianRing A ∧ IsAdicComplete (𝔪 A) A

instance {A : CBaseCat Λ k} : IsNoetherianRing A.obj := A.property.left

instance {A : CBaseCat Λ k} : IsAdicComplete (𝔪 A.obj) A.obj := A.property.right

/-- The base category for deformation theory over `Λ`. This is the full subcategory of
`LocAlgCat Λ k` consisting of Artinian local `Λ`-algebras with residue field `k`. -/
@[stacks 06GC]
abbrev BaseCat (Λ : Type u) [CommRing Λ] (k : Type v) [Field k] [Algebra Λ k] :=
  ObjectProperty.FullSubcategory fun A : LocAlgCat.{w} Λ k ↦ IsArtinianRing A

instance (A : BaseCat Λ k) : IsArtinianRing A.obj := A.property

namespace BaseCat

/-- The natural inclusion functor from the base category to the complete base category. -/
abbrev ιToCBaseCat (Λ : Type u) [CommRing Λ] (k : Type v) [Field k] [Algebra Λ k] :
    BaseCat.{w} Λ k ⥤ CBaseCat.{w} Λ k :=
  ObjectProperty.ιOfLE fun _ _ ↦ ⟨inferInstance, inferInstance⟩

variable {A B C : BaseCat.{w} Λ k} {f : A ⟶ B}

/-- The object in the base category associated to a type equipped with
the appropriate typeclasses. This is a preferred way to construct a term of `BaseCat Λ k`. -/
abbrev of (X : Type w) [CommRing X] [IsLocalRing X] [Algebra Λ X] [IsArtinianRing X]
    (eX : 𝓀 X ≃ₐ[Λ] k) : BaseCat Λ k := ⟨.of X eX, inferInstance⟩

/-- Given an object `A : BaseCat Λ k` and a surjective `Λ`-algebra homomorphism
`f : A.obj →ₐ[Λ] X` to a nontrivial `Λ`-algebra `X`, `ofSurj` constructs the induced
object in `BaseCat Λ k`. -/
noncomputable abbrev ofSurj (A : BaseCat.{w} Λ k) (X : Type w) [CommRing X] [Nontrivial X]
    [Algebra Λ X] (f : A.obj →ₐ[Λ] X) (hf : Surjective f) : BaseCat Λ k :=
  ⟨.ofSurj A.obj X f hf, hf.isArtinianRing⟩

/-- Upgrades a surjective `Λ`-algebra homomorphism `f : A.obj →ₐ[Λ] X` from
an object `A : BaseCat Λ k` to a nontrivial `Λ`-algebra `X` into a morphism  in `BaseCat Λ k`
from `A` to the induced object `ofSurj A X f hf`. -/
noncomputable abbrev toOfSurj (A : BaseCat.{w} Λ k) (X : Type w) [CommRing X] [Nontrivial X]
    [Algebra Λ X] (f : A.obj →ₐ[Λ] X) (hf : Surjective f) : A ⟶ ofSurj A X f hf :=
  ObjectProperty.homMk (LocAlgCat.toOfSurj A.obj X f hf)

/-- A morphism `f : A ⟶ B` in `BaseCat Λ k` is a **small extension** if it is a surjective map
whose kernel is a principal ideal annihilated by the maximal ideal of `A`. -/
@[stacks 06GD]
class IsSmallExtension (f : A ⟶ B) : Prop where
  private mk ::
  surjective (f) : Function.Surjective f.hom.toAlgHom
  isPrincipal_ker (f) : (RingHom.ker f.hom.toAlgHom).IsPrincipal
  le_annihilator_ker (f) : 𝔪 A.obj ≤ (RingHom.ker f.hom.toAlgHom).annihilator

theorem isSmallExtenstion_iff : IsSmallExtension f ↔ Function.Surjective f.hom.toAlgHom ∧
    ∃ x : A.obj, Ideal.span {x} = RingHom.ker f.hom.toAlgHom ∧ ∀ y ∈ 𝔪 A.obj, x * y = 0 := by
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

theorem IsSmallExtension.of (A : BaseCat.{w} Λ k) {x : A.obj} [Nontrivial (A.obj ⧸ Ideal.span {x})]
    (hx : ∀ y ∈ 𝔪 A.obj, x * y = 0) : IsSmallExtension (A.toOfSurj (A.obj ⧸ Ideal.span {x})
      (Ideal.Quotient.mkₐ Λ (Ideal.span {x})) Ideal.Quotient.mk_surjective) := by
  rw [isSmallExtenstion_iff]
  refine ⟨Ideal.Quotient.mk_surjective, x, ?_, hx⟩
  rw [ObjectProperty.homMk_hom, LocAlgCat.toAlgHom_toOfSurj]
  simp_rw [← Ideal.Quotient.mkₐ_ker Λ (Ideal.span {x})]
  congr

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
    by_cases! hI : I = ⊥
    · rw [← RingHom.injective_iff_ker_eq_bot] at hI
      have : IsSmallExtension f := isSmallExtension_of_bijective ⟨hI, hf⟩
      exact small_ext f
    obtain ⟨x, hx, x_ne⟩ := (Submodule.ne_bot_iff _).mp (Ideal.annihilator_inf_ne_bot
      ((isArtinianRing_iff_isNilpotent_maximalIdeal A.obj).mp inferInstance) hI)
    have x_in : x ∈ I := (mem_inf.mp hx).right
    replace hx : ∀ y ∈ 𝔪 A.obj, x * y = 0 := mem_annihilator.mp (mem_inf.mp hx).left
    have : Nontrivial (A.obj ⧸ Ideal.span {x}) := by
      refine Ideal.Quotient.nontrivial_iff.mpr (Ideal.span_singleton_ne_top
        (le_maximalIdeal ?_ x_in))
      rw [Ideal.ne_top_iff_exists_maximal]
      exact ⟨𝔪 A.obj, maximalIdeal.isMaximal A.obj,
        le_maximalIdeal (RingHom.ker_ne_top f.hom.toAlgHom)⟩
    have aux : ∀ a ∈ Ideal.span {x}, (LocAlgCat.Hom.toAlgHom f.hom) a = 0 := by
      intro _ h; rw [Ideal.mem_span_singleton'] at h
      rcases h with ⟨_, rfl⟩; rw [← RingHom.mem_ker]
      exact Ideal.mul_mem_left _ _ x_in
    let C := ofSurj A (A.obj ⧸ Ideal.span {x}) (Ideal.Quotient.mkₐ ..)
      Ideal.Quotient.mk_surjective
    let g : A ⟶ C := toOfSurj A (A.obj ⧸ Ideal.span {x}) (Ideal.Quotient.mkₐ ..)
      Ideal.Quotient.mk_surjective
    have hg : IsSmallExtension g := IsSmallExtension.of A hx
    let u : C.obj →ₐ[Λ] B.obj := Ideal.Quotient.liftₐ (Ideal.span {x}) f.hom.toAlgHom aux
    let v : A.obj →ₐ[Λ] C.obj := Ideal.Quotient.mkₐ Λ (Ideal.span {x})
    have u_surj : Surjective u :=
      Ideal.Quotient.lift_surjective_of_surjective (Ideal.span {x}) aux hf
    have : IsLocalHom u := ⟨u_surj.isLocalHom.map_nonunit⟩
    have : IsLocalHom v := ⟨Ideal.Quotient.mk_surjective.isLocalHom.map_nonunit⟩
    have aux' : (B.obj.e : 𝓀 B.obj →ₐ[Λ] k).comp (ResidueField.mapₐ u) = C.obj.e := by
      ext y
      let e_v := ResidueField.algEquivOfSurj (f := v) Ideal.Quotient.mk_surjective
      obtain ⟨y, rfl⟩ := e_v.surjective y
      calc
        _ = B.obj.e (ResidueField.mapₐ u (ResidueField.mapₐ v y)) := rfl
        _ = A.obj.e y := by
          rw [← AlgHom.comp_apply, ← ResidueField.mapₐ_comp]
          exact DFunLike.congr_fun f.hom.e_comp y
        _ = _ := by
          change A.obj.e y = A.obj.e (e_v.symm (e_v y))
          rw [AlgEquiv.symm_apply_apply]
    let f' : C ⟶ B := ObjectProperty.homMk (LocAlgCat.ofHom u (eX := C.obj.e) (eY := B.obj.e) aux')
    have : IsArtinianRing C.obj := C.property
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
    [IsScalarTower Λ A.obj M] : finrank (𝓀 Λ) k * length A.obj M = length Λ M := by
  have : (finrank (𝓀 Λ) k : ENat) ≠ 0 := by
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
      rw [ENat.coe_inj] at hn
      have ih_l := ih l (by lia) (by rw [← hl]; simp) hl
      have l_ne : l ≠ 0 := by
        rwa [ne_eq, ← ENat.coe_inj, Nat.cast_zero, hl, length_eq_zero_iff,
          Submodule.Quotient.subsingleton_iff]
      have ih_m := ih m (by lia) (by rw [← hm]; simp) hm
      rw [eq_add, eq_add', ← hl, ← hm]; norm_cast
      rw [Nat.mul_add]; push_cast
      rw [hl, hm, ih_m, ih_l]; congr
    push_neg at h'
    replace h' : IsSimpleModule A.obj M := by
      rw [isSimpleModule_iff_toSpanSingleton_surjective]
      exact ⟨this, h'⟩
    rw [length_eq_one, mul_one]
    rw [isSimpleModule_iff_quot_maximal] at h'
    rcases h' with ⟨I, hI, h'⟩
    replace h' : Nonempty (M ≃ₗ[Λ] k) := by
      rcases h' with ⟨e⟩
      replace hI := (isMaximal_iff A.obj).mp hI
      let f : (A.obj ⧸ I) ≃ₐ[Λ] 𝓀 A.obj :=
        Ideal.quotientEquivAlg I (𝔪 A.obj) (AlgEquiv.refl (R := Λ)) (by simp [hI])
      exact ⟨(e.restrictScalars Λ).trans <| f.toLinearEquiv.trans A.obj.e.toLinearEquiv⟩
    rcases h' with ⟨e⟩
    rw [e.length_eq, ← Module.length_eq_finrank, eq_comm]
    exact Module.length_eq_of_surjective (R := 𝓀 Λ) (S := Λ) (M := k) residue_surjective

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
  set PB := AlgHom.pullback f.hom.toAlgHom g.hom.toAlgHom
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

lemma coe_obj_ofPullback (f : A ⟶ C) (g : B ⟶ C) (hg : Surjective g.hom.toAlgHom) :
    ((ofPullback f g hg).obj : Type w) = f.hom.toAlgHom.pullback g.hom.toAlgHom := rfl

/-- xxxx -/
abbrev fromOfPullback (f : A ⟶ C) (g : B ⟶ C) (hg : Surjective g.hom.toAlgHom) :
    ofPullback f g hg ⟶ A := ObjectProperty.homMk (LocAlgCat.fromOfPullback f.hom g.hom hg)

@[instance, stacks 06GH "(2)"]
theorem fromOfPullback_isSmallExtension (f : A ⟶ C) (g : B ⟶ C) [IsSmallExtension g] :
    IsSmallExtension (fromOfPullback f g (IsSmallExtension.surjective g)) := by
  obtain ⟨x, x_span, hx⟩ := ((isSmallExtenstion_iff (f := g)).mp ‹_›).right
  rw [isSmallExtenstion_iff]; constructor
  · exact f.hom.toAlgHom.surjective_pullbackFst_of_surjective g.hom.toAlgHom
      (IsSmallExtension.surjective g)
  · have : (0, x) ∈ f.hom.toAlgHom.pullback g.hom.toAlgHom := by
      simp only [AlgHom.mem_equalizer, AlgHom.coe_comp, Function.comp_apply, AlgHom.fst_apply,
        map_zero, AlgHom.snd_apply]
      rw [eq_comm, ← RingHom.mem_ker, ← x_span]
      exact Ideal.mem_span_singleton_self x
    use ⟨(0, x), this⟩; constructor
    · change _ = RingHom.ker (AlgHom.pullbackFst ..)
      ext ⟨⟨u, v⟩, h⟩
      simp only [Ideal.mem_span_singleton', eq_comm, Subtype.exists, MulMemClass.mk_mul_mk,
        Subtype.mk.injEq, AlgHom.mem_equalizer, AlgHom.coe_comp, Function.comp_apply,
        AlgHom.fst_apply, AlgHom.snd_apply, exists_prop, Prod.exists, Prod.mk_mul_mk, mul_zero,
        Prod.mk.injEq, and_left_comm, exists_and_left, RingHom.mem_ker, Subalgebra.coe_val,
        and_iff_left_iff_imp]
      intro u_eq
      simp only [u_eq, AlgHom.mem_equalizer, AlgHom.coe_comp, Function.comp_apply,
        AlgHom.fst_apply, map_zero, AlgHom.snd_apply] at h
      rw [eq_comm, ← RingHom.mem_ker, ← x_span, Ideal.mem_span_singleton'] at h
      rcases h with ⟨w, hw⟩
      rcases LocAlgCat.exists_mem_maximalIdeal_toAlgHom_add g.hom f.hom
        (IsSmallExtension.surjective g) w with ⟨z, m, m_in, hm⟩
      exact ⟨z, w + m, hm.symm, by rw [add_mul, hw, mul_comm, hx m m_in, add_zero]⟩
    · rintro ⟨⟨a, b⟩, hab⟩ h
      suffices ¬ IsUnit b by simpa [← Subtype.val_inj] using hx b this
      intro hb
      simp only [AlgHom.mem_equalizer, AlgHom.coe_comp, Function.comp_apply, AlgHom.fst_apply,
        AlgHom.snd_apply] at hab
      have : IsUnit ((LocAlgCat.Hom.toAlgHom f.hom) a) := by
        rwa [hab, isUnit_map_iff]
      apply IsLocalHom.map_nonunit at this
      simp [AlgHom.isUnit_pullback_mk_iff] at h
      grind

end
/--/
end BaseCat

section Cotangent

namespace LocAlgCat

variable {A B : LocAlgCat.{w} Λ k}

instance : Module k (𝔪 A).Cotangent := Module.compHom _ (A.e.symm : k →+* 𝓀 A)

lemma smul_cotangent_def (r : k) (x : (𝔪 A).Cotangent) : r • x = (A.e.symm r) • x := rfl

/-- map between cotangent spaces -/
def mapCotangent (f : A ⟶ B) : (𝔪 A).Cotangent →ₗ[k] (𝔪 B).Cotangent := .mk
  ((𝔪 A).mapCotangent (𝔪 B) f.toAlgHom (((local_hom_TFAE (f.toAlgHom : A →+* B)).out 0 3).mp
  (by exact ⟨IsLocalHom.map_nonunit⟩))).toAddHom (fun r x ↦ by
    obtain ⟨x, rfl⟩ := (𝔪 A).toCotangent_surjective x
    simp only [smul_cotangent_def, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, RingHom.id_apply,
      Ideal.mapCotangent_toCotangent]
    obtain ⟨s, hs⟩ := residue_surjective (R := A) (A.e.symm r)
    obtain ⟨t, ht⟩ := residue_surjective (R := B) (B.e.symm r)
    simp_rw [← hs, ← ht, residue_smul_toCotangent, Ideal.mapCotangent_toCotangent,
      Ideal.toCotangent_eq, SetLike.val_smul, smul_eq_mul, map_mul, ← sub_mul, pow_two]
    refine Ideal.mul_mem_mul ?_ ?_
    · rw [AlgEquiv.eq_symm_apply] at hs ht
      have := DFunLike.congr_fun f.e_comp ((residue A) s)
      simp only [AlgHom.coe_comp, AlgHom.coe_coe, Function.comp_apply, ResidueField.mapₐ_apply,
        ResidueField.map_residue, RingHom.coe_coe, hs] at this
      rwa [← ht, B.e.injective.eq_iff, ← sub_eq_zero, ← map_sub,
        residue_eq_zero_iff] at this
    · rw [← Ideal.mem_comap]; convert x.prop
      exact ((local_hom_TFAE (f.toAlgHom : A →+* B)).out 0 4).mp
        (by exact ⟨IsLocalHom.map_nonunit⟩))

lemma mapCotangent_def (f : A ⟶ B) (a : (𝔪 A).Cotangent) : mapCotangent f a =
    ((𝔪 A).mapCotangent (𝔪 B) f.toAlgHom (((local_hom_TFAE (f.toAlgHom : A →+* B)).out 0 3).mp
      (by exact ⟨IsLocalHom.map_nonunit⟩))) a := rfl

open scoped TensorProduct

/-- relative cotangent space for an object in `LocAlgCat`. -/
@[stacks 06GY]
def relCotangent (A : LocAlgCat.{w} Λ k) : Type _ := k ⊗[A] Ω[A⁄Λ]
deriving Inhabited, AddCommGroup, Module k

/-- Cotangent to relCotangent -/
abbrev ofCotangent (A : LocAlgCat.{w} Λ k) : (𝔪 A).Cotangent →ₗ[k] relCotangent A := sorry

end LocAlgCat

end Cotangent

end DeformationTheory

/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import Mathlib

@[expose] public section

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
/-
/-! # some basic preliminaries -/

section AlgEquiv

variable {R A₁ A₂ A₃ : Type*} [CommSemiring R] [Semiring A₁] [Semiring A₂] [Semiring A₃]
  [Algebra R A₁] [Algebra R A₂] [Algebra R A₃]

theorem AlgEquiv.coeAlgHom_trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) :
    (e₁.trans e₂ : A₁ →ₐ[R] A₃) = (e₂ : A₂ →ₐ[R] A₃).comp e₁ := rfl

theorem AlgEquiv.coeAlgHom_apply (e : A₁ ≃ₐ[R] A₂) (x : A₁): (e : A₁ →ₐ[R] A₂) x = e x := rfl

end AlgEquiv-/

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

/-- A surjective local ring homomorphism induces an equivalence of residue fields. -/
noncomputable def equivOfSurj {f : R →+* S} (h : Function.Surjective f) : 𝓀 R ≃+* 𝓀 S :=
  letI := h.isLocalHom
  .ofBijective (map f) ⟨RingHom.injective (map f), map_surjective h⟩

@[simp]
lemma equivOfSurj_apply {f : R →+* S} (h : Function.Surjective f) (x : 𝓀 R) :
    letI := h.isLocalHom
    equivOfSurj h x = map f x := rfl

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

lemma mapₐ_apply (f : R →ₐ[A] S) [IsLocalHom f] (x : ResidueField R) :
    mapₐ f x = map f x := rfl

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

end algMap

end IsLocalRing.ResidueField

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
  infer_instance

--------------------------------------------------------------------------------

@[instance]
theorem IsArtinianRing.isAdicComplete {R : Type*} [CommRing R] [IsArtinianRing R]
    [IsLocalRing R] : IsAdicComplete (𝔪 R) R := by
  let : WithIdeal R := ⟨𝔪 R⟩
  obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal R).mp inferInstance
  have n_pos : 0 < n := by
    revert hn; contrapose!
    simp only [nonpos_iff_eq_zero, Submodule.zero_eq_bot, ne_eq]
    intro h; simp [h]
  have : DiscreteTopology R := by
    have : IsAdic (𝔪 R ^ n) := is_ideal_adic_pow rfl n_pos
    rwa [← is_bot_adic_iff, ← Ideal.zero_eq_bot, ← hn]
  exact (IsAdic.isAdicComplete_iff (by rfl)).mpr
    ⟨IsRightUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace, inferInstance⟩

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
-- add `import Mathlib.RingTheory.Ideal.Maximal`

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

theorem ResidueField.finrank_eq_length {R k : Type*} [CommRing R] [IsLocalRing R] [Field k]
    [Algebra R k] [Module.Finite R k] :
    Module.finrank (ResidueField R) k = Module.length R k := by
  rw [← Module.length_eq_finrank, ← WithBot.coe_inj, Module.coe_length, Module.coe_length]
  let e_aux : Submodule (ResidueField R) k ↪o Submodule R k :=
    Submodule.restrictScalarsEmbedding R (ResidueField R) k
  have : Function.Surjective e_aux := fun p ↦ by
    let q : Submodule (𝓀 R) k := {
      carrier := p
      add_mem' := p.add_mem
      zero_mem' := p.zero_mem
      smul_mem' r a a_in := by
        induction r using Submodule.Quotient.induction_on (maximalIdeal R) with
        | H r =>
          change residue R r • a ∈ p
          rw [Algebra.smul_def, ← ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
            ← Algebra.smul_def]
          exact Submodule.smul_mem p r a_in
    }
    exact ⟨q, rfl⟩
  rw [Order.krullDim_eq_of_orderIso (RelIso.ofSurjective e_aux this)]

end IsLocalRing

--------------------------------------------------------------------------------

--------------------------------------------------------------------------------

namespace DeformationTheory

open IsLocalRing CategoryTheory Function

variable {Λ : Type u} [CommRing Λ]
variable {k : Type v} [Field k] [Algebra Λ k]

variable (Λ k) in
set_option backward.privateInPublic true in
/-- The category of local `Λ`-algebras and their morphisms. -/
structure LocAlgCat where
  private mk ::
  /-- The underlying type. -/
  carrier : Type w
  [commRing : CommRing carrier]
  [localRing : IsLocalRing carrier]
  [algebra : Algebra Λ carrier]
  [localhom : IsLocalHom (algebraMap Λ carrier)]
  residueEquiv : ResidueField carrier ≃ₐ[Λ] k

namespace LocAlgCat

variable {A B C : LocAlgCat.{w} Λ k} {X Y Z : Type w} [CommRing X] [IsLocalRing X] [Algebra Λ X]
  [CommRing Y] [IsLocalRing Y] [Algebra Λ Y] [CommRing Z] [IsLocalRing Z] [Algebra Λ Z]
  [IsLocalHom (algebraMap Λ X)] [IsLocalHom (algebraMap Λ Y)] [IsLocalHom (algebraMap Λ Z)]
  {eX : 𝓀 X ≃ₐ[Λ] k} {eY : 𝓀 Y ≃ₐ[Λ] k} {eZ : 𝓀 Z ≃ₐ[Λ] k}

attribute [instance] localRing commRing algebra localhom

initialize_simps_projections LocAlgCat (-localRing, -commRing, -algebra, -localhom)

instance : CoeSort (LocAlgCat Λ k) (Type w) := ⟨carrier⟩

attribute [coe] carrier

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The object in the category of local `Λ`-algebras associated to a type equipped with
the appropriate typeclasses. This is a preferred way to construct a term of `LocAlgCat Λ k`. -/
abbrev of (X : Type w) [CommRing X] [IsLocalRing X] [Algebra Λ X] [IsLocalHom (algebraMap Λ X)]
    (eX : 𝓀 X ≃ₐ[Λ] k) : LocAlgCat Λ k :=
  ⟨X, eX⟩

variable (Λ k) in
lemma coe_of (X : Type w) [CommRing X] [IsLocalRing X] [Algebra Λ X] [IsLocalHom (algebraMap Λ X)]
    (eX : 𝓀 X ≃ₐ[Λ] k) : (of X eX : Type w) = X :=
  rfl

/-- Given an object `A : LocAlgCat Λ k` and a surjective map `f : ↑A →ₐ[Λ] X` to a
nontrivial `Λ`-algebra `X`, `LocAlgCat.ofSurj` constructs an induced object of `LocAlgCat Λ k`. -/
noncomputable def ofSurj (A : LocAlgCat.{w} Λ k) (X : Type w) [CommRing X] [Nontrivial X]
    [Algebra Λ X] [IsLocalHom (algebraMap Λ X)] (f : A →ₐ[Λ] X) (hf : Surjective f) :
    LocAlgCat.{w} Λ k :=
  letI : IsLocalRing X := IsLocalRing.of_surjective' (f : A →+* X) hf
  letI : IsLocalHom f := ⟨hf.isLocalHom.map_nonunit⟩
  of X ((ResidueField.algEquivOfSurj (f := f) hf).symm.trans A.residueEquiv)

lemma coe_ofSurj (A : LocAlgCat.{w} Λ k) (X : Type w) [CommRing X] [Nontrivial X]
    [Algebra Λ X] [IsLocalHom (algebraMap Λ X)] (f : A →ₐ[Λ] X) (hf : Surjective f) :
      (ofSurj A X f hf : Type w) = X :=
  rfl

@[simp]
lemma ofSurj_residueEquiv (A : LocAlgCat.{w} Λ k) (X : Type w) [CommRing X] [Nontrivial X]
    [Algebra Λ X] [IsLocalHom (algebraMap Λ X)] (f : A →ₐ[Λ] X) (hf : Surjective f) :
  letI : IsLocalRing X := IsLocalRing.of_surjective' (f : A →+* X) hf
  letI : IsLocalHom f := ⟨hf.isLocalHom.map_nonunit⟩
  (ofSurj A X f hf).residueEquiv =
    (ResidueField.algEquivOfSurj (f := f) hf).symm.trans A.residueEquiv := rfl

/-- The type of morphisms in `LocAlgCat Λ k`. -/
@[ext]
structure Hom (A B : LocAlgCat.{w} Λ k) where
  private mk ::
  /-- The underlying algebra map. -/
  toAlgHom' : A →ₐ[Λ] B
  [localhom : IsLocalHom toAlgHom']
  residue_comp : (B.residueEquiv : 𝓀 B →ₐ[Λ] k).comp (ResidueField.mapₐ toAlgHom') =
    A.residueEquiv

/-- Cast a morphism of `LocAlgCat` into an `AlgHom`. -/
abbrev Hom.toAlgHom {A B : LocAlgCat.{w} Λ k} (f : A.Hom B) : A →ₐ[Λ] B :=
  f.toAlgHom'

/-- See Note [custom simps projection] -/
def Hom.Simps.toAlgHom {A B : LocAlgCat.{w} Λ k} (f : A.Hom B) : A →ₐ[Λ] B :=
  f.toAlgHom

attribute [instance] Hom.localhom

initialize_simps_projections Hom (-localhom, toAlgHom' → toAlgHom)

instance : FunLike (Hom A B) A B where
  coe f := f.toAlgHom
  coe_injective' f g h := by
    rcases f with ⟨f, hf⟩
    rcases g with ⟨g, hg⟩
    simpa using h

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance : Category (LocAlgCat.{w} Λ k) where
  Hom A B := Hom A B
  id A := ⟨AlgHom.id Λ A, by simp⟩
  comp {A B C} f g := ⟨g.toAlgHom.comp f.toAlgHom, by
    rw [ResidueField.mapₐ_comp, ← AlgHom.comp_assoc, g.residue_comp, f.residue_comp]⟩

instance : ConcreteCategory (LocAlgCat.{w} Λ k) Hom where
  hom := id
  ofHom := id

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Typecheck an `AlgHom` compatible with residue maps as a morphism in `LocAlgCat`. -/
abbrev ofHom (f : X →ₐ[Λ] Y) [IsLocalHom f] (hf : (eY : 𝓀 Y →ₐ[Λ] k).comp (ResidueField.mapₐ f) =
    eX) : of X eX ⟶ of Y eY := ⟨f, hf⟩

/-- Given an object `A : LocAlgCat Λ k` and a surjective map `f : ↑A →ₐ[Λ] X` to a
nontrivial `Λ`-algebra `X`, `LocAlgCat.ofHomSurj` upgrades `f` to a morphism in `LocAlgCat Λ k`
from `A` to the induced object `LocAlgCat.ofSurj A X f hf`. -/
noncomputable def ofHomSurj (A : LocAlgCat.{w} Λ k) (X : Type w) [CommRing X] [Nontrivial X]
    [Algebra Λ X] [IsLocalHom (algebraMap Λ X)] (f : A →ₐ[Λ] X) (hf : Surjective f) :
    A ⟶ ofSurj A X f hf :=
  letI : IsLocalRing X := IsLocalRing.of_surjective' (f : A →+* X) hf
  letI : IsLocalHom f := ⟨hf.isLocalHom.map_nonunit⟩
  ofHom f (by ext; simp [ResidueField.mapₐ_apply, AlgEquiv.symm_apply_eq])

@[simp]
lemma toAlgHom_ofHomSurj (A : LocAlgCat.{w} Λ k) (X : Type w) [CommRing X] [Nontrivial X]
    [Algebra Λ X] [IsLocalHom (algebraMap Λ X)] (f : A →ₐ[Λ] X) (hf : Surjective f) :
    (ofHomSurj A X f hf).toAlgHom = f :=
  rfl

@[simp] lemma hom_id : (𝟙 A : A ⟶ A).toAlgHom = AlgHom.id Λ A := rfl

@[simp] lemma id_apply (a : A) : (𝟙 A : A ⟶ A) a = a := by simp

@[simp] lemma hom_comp (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).toAlgHom = g.toAlgHom.comp f.toAlgHom := rfl

@[simp] lemma comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a) := by simp

@[ext] lemma hom_ext {f g : A ⟶ B} (hf : f.toAlgHom = g.toAlgHom) : f = g := Hom.ext hf

@[simp] lemma toAlgHom_ofHom (f : X →ₐ[Λ] Y) [IsLocalHom f]
    (hf : (eY : 𝓀 Y →ₐ[Λ] k).comp (ResidueField.mapₐ f) = eX) : (ofHom f hf).toAlgHom = f := rfl

@[simp] lemma ofhom_toAlgHom (f : A ⟶ B) : ofHom f.toAlgHom f.residue_comp = f := rfl

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
    {_ : IsLocalRing Y} {_ : Algebra Λ Y} {_ : IsLocalHom (algebraMap Λ X)}
    {_ : IsLocalHom (algebraMap Λ Y)} {eX : 𝓀 X ≃ₐ[Λ] k} {eY : 𝓀 Y ≃ₐ[Λ] k} (e : X ≃ₐ[Λ] Y)
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
lemma mapAlgEquiv_ofIso_trans_residueEquiv (i : A ≅ B) :
    (ResidueField.mapAlgEquiv (ofIso i)).trans B.residueEquiv = A.residueEquiv := by
  ext
  simpa using DFunLike.congr_fun i.hom.residue_comp _

/-- Algebra equivalences between `Algebra`s compatible with residue isomorphisms are
the same as isomorphisms in `LocAlgCat`. -/
@[simps]
def isoEquivSubtypeAlgEquiv : (of X eX ≅ of Y eY) ≃
    { e : X ≃ₐ[Λ] Y // (ResidueField.mapAlgEquiv e).trans eY = eX } where
  toFun i := ⟨ofIso i, mapAlgEquiv_ofIso_trans_residueEquiv i⟩
  invFun f := isoMk f.val f.prop

/-
section ulift

variable (Λ k)

/-- Universe lift functor for local algebras. -/
noncomputable def uliftFunctor : LocAlgCat.{w} Λ k ⥤ LocAlgCat.{max w w'} Λ k where
  obj A := .of (ULift A) ((ResidueField.mapAlgEquiv ULift.algEquiv).trans A.residueEquiv)
  map {A B} f := ofHom ((ULift.algEquiv (R := Λ) (A := B).symm : B →ₐ[Λ] ULift B).comp
    (f.toAlgHom.comp (ULift.algEquiv (R := Λ) (A := A) : ULift A →ₐ[Λ] A))) (by
      ext
      have hf := DFunLike.congr_fun f.residue_comp
      simp only [AlgHom.comp_apply, AlgHom.coe_coe] at hf
      simp [← hf, ← AlgHom.comp_apply, ← ResidueField.mapₐ_comp, ← AlgHom.comp_assoc])

set_option backward.isDefEq.respectTransparency false in
/-- The universe lift functor for local algebras is fully faithful. -/
noncomputable def fullyFaithfulUliftFunctor : (uliftFunctor.{w', w} Λ k).FullyFaithful where
  preimage {A B} f :=
    let f_hom : ULift A →ₐ[Λ] ULift B := f.toAlgHom
    letI : IsLocalHom f_hom := f.localhom
    ofHom ((ULift.algEquiv (R := Λ) (A := B) : ULift B →ₐ[Λ] B).comp
    (f_hom.comp (ULift.algEquiv (R := Λ) (A := A).symm : A →ₐ[Λ] ULift A))) (by
      ext x
      rcases AlgEquiv.surjective (ResidueField.mapAlgEquiv <|
        ULift.algEquiv.{u, w', w} (R := Λ) (A := A)) x with ⟨x, rfl⟩
      simpa [ResidueField.mapₐ_apply, uliftFunctor] using DFunLike.congr_fun f.residue_comp x)

instance : (uliftFunctor.{w', w} Λ k).Full := (fullyFaithfulUliftFunctor Λ k).full

instance : (uliftFunctor.{w', w} Λ k).Faithful := (fullyFaithfulUliftFunctor Λ k).faithful

end ulift
-/
end LocAlgCat

-----------------------------------------------------------------------------------------

/-- The property of an object in `LocAlgCat Λ k` being Noetherian
and adic complete with respect to its maximal ideal. -/
abbrev CompNoeth (Λ : Type u) [CommRing Λ] (k : Type v) [Field k] [Algebra Λ k] :
    ObjectProperty (LocAlgCat.{w} Λ k) := fun A ↦ IsNoetherianRing A ∧ IsAdicComplete (𝔪 A) A

/-- The property of an object in `LocAlgCat Λ k` being Artinian. -/
abbrev Art (Λ : Type u) [CommRing Λ] (k : Type v) [Field k] [Algebra Λ k] :
    ObjectProperty (LocAlgCat.{w} Λ k) := fun A ↦ IsArtinianRing A

/-- The full subcategory of `LocAlgCat Λ k` consisting of complete Noetherian local `Λ`-algebras.
In deformation theory, this is the complete base category and often denoted as `Ĉ_Λ`. -/
abbrev CBaseCat (Λ : Type u) [CommRing Λ] (k : Type v) [Field k] [Algebra Λ k] :=
  (CompNoeth.{w} Λ k).FullSubcategory

instance {A : CBaseCat Λ k} : IsNoetherianRing A.obj := A.property.left

instance {A : CBaseCat Λ k} : IsAdicComplete (𝔪 A.obj) A.obj := A.property.right

/-- base category -/
@[stacks 06GC]
abbrev BaseCat (Λ : Type u) [CommRing Λ] (k : Type v) [Field k] [Algebra Λ k] :=
  (Art.{w} Λ k).FullSubcategory

instance (A : BaseCat Λ k) : IsArtinianRing A.obj := A.property

namespace BaseCat

/-- to complete base -/
abbrev ιToCBaseCat (Λ : Type u) [CommRing Λ] (k : Type v) [Field k] [Algebra Λ k] :
    BaseCat.{w} Λ k ⥤ CBaseCat.{w} Λ k :=
  ObjectProperty.ιOfLE fun _ _ ↦ ⟨inferInstance, inferInstance⟩

variable {A B C : BaseCat.{w} Λ k} {f : A ⟶ B}

/-- The object in the category of artinian local `Λ`-algebras associated to a type equipped with
the appropriate typeclasses. This is the preferred way to construct a term of `BaseCat Λ k`. -/
abbrev of (X : Type w) [CommRing X] [IsLocalRing X] [Algebra Λ X] [IsArtinianRing X]
    [IsLocalHom (algebraMap Λ X)] (eX : 𝓀 X ≃ₐ[Λ] k) : BaseCat Λ k :=
  ⟨.of X eX, inferInstance⟩

/-- xxx -/
noncomputable abbrev ofSurj (A : BaseCat.{w} Λ k) (X : Type w) [CommRing X] [Nontrivial X]
    [Algebra Λ X] [IsLocalHom (algebraMap Λ X)] (f : A.obj →ₐ[Λ] X) (hf : Surjective f) :
    BaseCat Λ k :=
  ⟨.ofSurj A.obj X f hf, hf.isArtinianRing⟩

/-- xxx -/
noncomputable abbrev ofHomSurj (A : BaseCat.{w} Λ k) (X : Type w) [CommRing X] [Nontrivial X]
    [Algebra Λ X] [IsLocalHom (algebraMap Λ X)] (f : A.obj →ₐ[Λ] X) (hf : Surjective f) :
    A ⟶ ofSurj A X f hf :=
  ObjectProperty.homMk (LocAlgCat.ofHomSurj A.obj X f hf)

/-- small extenstion -/
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

/-- A preferred way to construct a small extension -/
theorem IsSmallExtension.of (A : BaseCat.{w} Λ k) {x : A.obj} [Nontrivial (A.obj ⧸ Ideal.span {x})]
    [IsLocalHom (algebraMap Λ (A.obj ⧸ Ideal.span {x}))] (hx : ∀ y ∈ 𝔪 A.obj, x * y = 0) :
    IsSmallExtension (A.ofHomSurj (A.obj ⧸ Ideal.span {x}) (Ideal.Quotient.mkₐ Λ (Ideal.span {x}))
      Ideal.Quotient.mk_surjective) := by
  rw [isSmallExtenstion_iff]
  refine ⟨Ideal.Quotient.mk_surjective, x, ?_, hx⟩
  ext; simp only [ObjectProperty.homMk_hom, LocAlgCat.toAlgHom_ofHomSurj, RingHom.mem_ker]
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  rfl

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
    have : IsLocalHom (algebraMap Λ (A.obj ⧸ Ideal.span {x})) := ⟨fun a ↦
      letI : IsLocalHom (algebraMap A.obj (A.obj ⧸ Ideal.span {x})) :=
        Ideal.Quotient.mk_surjective.isLocalHom
      IsLocalHom.map_nonunit (f := algebraMap Λ A.obj) a ∘ IsLocalHom.map_nonunit
        (f := algebraMap A.obj (A.obj ⧸ Ideal.span {x})) (algebraMap Λ A.obj a)⟩
    have aux : ∀ a ∈ Ideal.span {x}, (LocAlgCat.Hom.toAlgHom f.hom) a = 0 := by
      intro _ h; rw [Ideal.mem_span_singleton'] at h
      rcases h with ⟨_, rfl⟩; rw [← RingHom.mem_ker]
      exact Ideal.mul_mem_left _ _ x_in
    let C := ofSurj A (A.obj ⧸ Ideal.span {x}) (Ideal.Quotient.mkₐ ..)
      Ideal.Quotient.mk_surjective
    let g : A ⟶ C := ofHomSurj A (A.obj ⧸ Ideal.span {x}) (Ideal.Quotient.mkₐ ..)
      Ideal.Quotient.mk_surjective
    have hg : IsSmallExtension g := IsSmallExtension.of A hx
    let u : C.obj →ₐ[Λ] B.obj := Ideal.Quotient.liftₐ (Ideal.span {x}) f.hom.toAlgHom aux
    let v : A.obj →ₐ[Λ] C.obj := Ideal.Quotient.mkₐ Λ (Ideal.span {x})
    have u_surj : Surjective u :=
      Ideal.Quotient.lift_surjective_of_surjective (Ideal.span {x}) aux hf
    have : IsLocalHom u := ⟨u_surj.isLocalHom.map_nonunit⟩
    have : IsLocalHom v := ⟨Ideal.Quotient.mk_surjective.isLocalHom.map_nonunit⟩
    have aux' : (B.obj.residueEquiv : 𝓀 B.obj →ₐ[Λ] k).comp (ResidueField.mapₐ u) =
      C.obj.residueEquiv := AlgHom.ext fun y ↦ by
      let e_v := ResidueField.algEquivOfSurj (f := v) Ideal.Quotient.mk_surjective
      obtain ⟨y, rfl⟩ := e_v.surjective y
      calc
        _ = B.obj.residueEquiv (ResidueField.mapₐ u (ResidueField.mapₐ v y)) := rfl
        _ = A.obj.residueEquiv y := by
          rw [← AlgHom.comp_apply, ← ResidueField.mapₐ_comp]
          exact DFunLike.congr_fun f.hom.residue_comp y
        _ = _ := by
          change A.obj.residueEquiv y = A.obj.residueEquiv (e_v.symm (e_v y))
          rw [AlgEquiv.symm_apply_apply]
    let f' : C ⟶ B := ObjectProperty.homMk
      (LocAlgCat.ofHom u (eX := C.obj.residueEquiv) (eY := B.obj.residueEquiv) aux')
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

open Module in
theorem finrank_residueField_mul_length [IsLocalRing Λ] [Module.Finite Λ k] {M : Type*}
    [AddCommGroup M] [Module A.obj M] [Module Λ M] [IsScalarTower Λ A.obj M] :
      finrank (𝓀 Λ) k * length A.obj M = length Λ M := by
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
      rw [hl, hm, ih_m, ih_l]; rfl
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
      exact ⟨(e.restrictScalars Λ).trans <| f.toLinearEquiv.trans A.obj.residueEquiv.toLinearEquiv⟩
    rcases h' with ⟨e⟩
    rw [e.length_eq, ResidueField.finrank_eq_length]

end BaseCat

end DeformationTheory

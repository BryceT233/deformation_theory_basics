/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

module

public import Mathlib

@[expose] public section

universe w w' v u

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

theorem comp_pullbackFst_eq_comp_pullbackSnd (f : R →+* T) (g : S →+* T) :
    f.comp (f.pullbackFst g) = g.comp (f.pullbackSnd g) :=
  RingHom.ext fun x ↦ x.prop

theorem isUnit_pullback_mk_iff (f : R →+* T) (g : S →+* T) {a : R × S} (a_in : a ∈ f.pullback g) :
    IsUnit (⟨a, a_in⟩ : f.pullback g) ↔ IsUnit a.1 ∧ IsUnit a.2 := by
  rw [isUnit_eqLocus_mk_iff, Prod.isUnit_iff]

theorem isLocalHom_pullbackFst (f : R →+* T) (g : S →+* T) [IsLocalHom g] :
    IsLocalHom (f.pullbackFst g) where
  map_nonunit a ha := by
    rcases a with ⟨⟨r, s⟩, hrs⟩
    exact (isUnit_pullback_mk_iff f g _).mpr ⟨ha, isUnit_of_map_unit g _ (hrs ▸ ha.map f)⟩

theorem isLocalHom_pullbackSnd (f : R →+* T) (g : S →+* T) [IsLocalHom f] :
    IsLocalHom (f.pullbackSnd g) where
  map_nonunit a ha := by
    rcases a with ⟨⟨r, s⟩, hrs⟩
    exact (isUnit_pullback_mk_iff f g _).mpr ⟨isUnit_of_map_unit f _ (hrs.symm ▸ ha.map g), ha⟩

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

theorem comp_pullbackFst_eq_comp_pullbackSnd (f : A →ₐ[R] C) (g : B →ₐ[R] C) :
    f.comp (pullbackFst f g) = g.comp (pullbackSnd f g) :=
  AlgHom.ext fun x ↦ x.prop

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

lemma Ideal.mapCotangent_comp {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C] {I₁ : Ideal A} {I₂ : Ideal B} {I₃ : Ideal C}
  (f : A →ₐ[R] B) (g : B →ₐ[R] C) (h₁ : I₁ ≤ Ideal.comap f I₂) (h₂ : I₂ ≤ Ideal.comap g I₃) :
  Ideal.mapCotangent I₁ I₃ (g.comp f) (fun _ hx ↦ h₂ (h₁ hx)) =
    (Ideal.mapCotangent I₂ I₃ g h₂).comp (Ideal.mapCotangent I₁ I₂ f h₁) := by
  ext ⟨_, _⟩; rfl

--------------------------------------------------------------------------------

instance IsLocalRing.isLocalHom_algebraMap_of_isIntegral (R k : Type*) [CommRing R]
    [IsLocalRing R] [Field k] [Algebra R k] [Algebra.IsIntegral R k] :
    IsLocalHom (algebraMap R k) := by
  apply ((local_hom_TFAE (algebraMap R k)).out 0 4).mpr
  rw [maximalIdeal_eq_bot]
  exact eq_maximalIdeal (Algebra.ker_algebraMap_isMaximal_of_isIntegral R k)

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

---------------------------------------------------------------------------------

-- From Thmoas-Guan's PR #37975

section

open Ideal Quotient IsLocalRing AdicCompletion

variable {R : Type*} [CommRing R] (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]

lemma AdicCompletion.isAdicComplete_self (fg : I.FG) :
    IsAdicComplete (I.map (algebraMap R (AdicCompletion I R))) (AdicCompletion I R) :=
  (IsAdicComplete.map_algebraMap_iff _ _).mpr (AdicCompletion.isAdicComplete fg)

lemma AdicCompletion.isMaximal_map_of_le (m : Ideal R) [m.IsMaximal] (le : I ≤ m) (fg : I.FG) :
    (m.map (algebraMap R (AdicCompletion I R))).IsMaximal := by
  have compeq : (AdicCompletion.evalOneₐ I).toRingHom.comp (algebraMap R (AdicCompletion I R)) =
    (Ideal.Quotient.mk I) := rfl
  have kerle : RingHom.ker (evalOneₐ I).toRingHom ≤ m.map (algebraMap R (AdicCompletion I R)) := by
    intro x hx
    have : x ∈ (AdicCompletion.eval I R 1).ker := by
      have eq : I ^ 1 * ⊤ = I := by simp
      simp only [AlgHom.toRingHom_eq_coe, RingHom.mem_ker, RingHom.coe_coe, ← factorₐ_evalₐ_one,
        pow_one, smul_eq_mul, mul_top, le_refl, ← factor_eval_eq_evalₐ, Submodule.mapQ_eq_factor,
        Submodule.factor_eq_factor, factor_comp_apply] at hx
      have : (factor (le_of_eq eq.symm)) ((factor (le_of_eq eq)) ((eval I R 1) x)) = 0 := by
        simp [hx]
      simpa using this
    simp only [smul_eq_mul, ← pow_smul_top_eq_ker_eval fg, pow_one, smul_top_eq_map,
      Submodule.restrictScalars_mem] at this
    exact Ideal.map_mono le this
  have : m.map (algebraMap R (AdicCompletion I R)) = (m.map (Ideal.Quotient.mk I)).comap
    (AdicCompletion.evalOneₐ I).toRingHom := by
    rw [← compeq, ← Ideal.map_map,
      Ideal.comap_map_of_surjective' (evalOneₐ I).toRingHom (evalOneₐ_surjective I),
      eq_comm, sup_eq_left]
    exact kerle
  rw [this]
  let _ : (Ideal.map (Ideal.Quotient.mk I) m).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by simpa using le)
  exact Ideal.comap_isMaximal_of_surjective _ (evalOneₐ_surjective I)

lemma AdicCompletion.isLocalRing_of_fg [IsLocalRing R] (fg : (maximalIdeal R).FG) :
    IsLocalRing (AdicCompletion (maximalIdeal R) R) :=
  @isLocalRing_of_isAdicComplete_maximal _ _
    ((maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R)))
    (AdicCompletion.isMaximal_map_of_le _ _ (le_refl _) fg)
    (AdicCompletion.isAdicComplete_self _ fg)

instance [IsNoetherianRing R] [IsLocalRing R] : IsLocalRing (AdicCompletion (maximalIdeal R) R) :=
  AdicCompletion.isLocalRing_of_fg (fg_of_isNoetherianRing (maximalIdeal R))

lemma AdicCompletion.maximalIdeal_eq_map_of_fg [IsLocalRing R] (fg : (maximalIdeal R).FG) :
    letI := AdicCompletion.isLocalRing_of_fg fg
    maximalIdeal (AdicCompletion (maximalIdeal R) R) =
    (maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
  letI := AdicCompletion.isLocalRing_of_fg fg
  (IsLocalRing.eq_maximalIdeal (AdicCompletion.isMaximal_map_of_le _ _ (le_refl _) fg)).symm

lemma AdicCompletion.maximalIdeal_eq_map [IsNoetherianRing R] [IsLocalRing R] :
    maximalIdeal (AdicCompletion (maximalIdeal R) R) =
    (maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
  (IsLocalRing.eq_maximalIdeal (AdicCompletion.isMaximal_map_of_le _ _ (le_refl _)
    (maximalIdeal R).fg_of_isNoetherianRing)).symm

end

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
structure LocAlgCat (Λ : Type u) (k : Type v) [CommRing Λ] [Field k] [Algebra Λ k] : Type _ where
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

variable (X) in
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
structure Hom (A B : LocAlgCat.{w} Λ k) : Type w where
  /-- The underlying algebra map. -/
  toAlgHom : A →ₐ[Λ] B
  -- We do not use `IsLocalHom` to avoid introducing `IsLocalHom` instances for `AlgHom`.
  comap_maximalIdeal_eq : (maximalIdeal B).comap toAlgHom = maximalIdeal A
  residue_comp : B.residue.comp toAlgHom = A.residue

instance : Category (LocAlgCat.{w} Λ k) where
  Hom A B := Hom A B
  id A := ⟨AlgHom.id Λ A, by simp, by simp⟩
  comp {A B C} f g := ⟨g.toAlgHom.comp f.toAlgHom, by
    rw [← Ideal.comap_comapₐ, g.comap_maximalIdeal_eq, f.comap_maximalIdeal_eq], by
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
lemma toAlghom_id : (𝟙 A : A ⟶ A).toAlgHom = AlgHom.id Λ A := rfl

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

instance (f : A ⟶ B) : Nontrivial (A ⧸ RingHom.ker (f.toAlgHom)) :=
  Ideal.Quotient.nontrivial_iff.mpr <| RingHom.ker_ne_top f.toAlgHom

instance [IsLocalHom (algebraMap Λ k)] : IsLocalHom (algebraMap Λ A) :=
  haveI : IsLocalHom ((algebraMap A k).comp (algebraMap Λ A)) := by
    rwa [← IsScalarTower.algebraMap_eq]
  isLocalHom_of_comp _ (algebraMap A k)

lemma comap_algebraMap_maximalIdeal [IsLocalRing Λ] [IsLocalHom (algebraMap Λ k)] :
    (maximalIdeal A).comap (algebraMap Λ A) = maximalIdeal Λ := by
  have := ((local_hom_TFAE (algebraMap Λ k)).out 0 4).mp ‹_›
  rw [eq_comm, ← this, IsScalarTower.algebraMap_eq Λ A, ← Ideal.comap_comap,
    eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ A.surj)]

instance [IsLocalRing Λ] [IsLocalHom (algebraMap Λ k)] :
    Nontrivial (A ⧸ ((maximalIdeal Λ).map (algebraMap Λ A))) :=
  Ideal.Quotient.nontrivial_iff.mpr <| ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top <|
    ((local_hom_TFAE (algebraMap Λ A)).out 0 2).mp (by infer_instance)

instance (n : ℕ) [NeZero n] : Nontrivial (A ⧸ maximalIdeal A ^ n) := by
  rw [Ideal.Quotient.nontrivial_iff, Ideal.ne_top_iff_exists_maximal]
  exact ⟨maximalIdeal A, maximalIdeal.isMaximal A, Ideal.pow_le_self (NeZero.ne n)⟩

section ofQuot

variable {I : Ideal A}

/-- The residue algebra structure on `ofQuot`. -/
instance ofQuotResidueAlgebra (A : LocAlgCat.{w} Λ k) {I : Ideal A} [Nontrivial (A ⧸ I)] :
    Algebra (A ⧸ I) k := fast_instance%
  (Ideal.Quotient.lift I (algebraMap A k) fun a a_in ↦ by
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
    Algebra A (A.ofQuot I) :=
  fast_instance% Ideal.Quotient.algebra _

instance isScalarTower_algebraOfQuot (A : LocAlgCat.{w} Λ k) {I : Ideal A} [Nontrivial (A ⧸ I)] :
    IsScalarTower Λ A (A.ofQuot I) := .of_algebraMap_eq fun _ ↦ rfl

/-- Upgrades the canonical quotient map from `A → A ⧸ I` to a morphism in `LocAlgCat`. -/
def toOfQuot (A : LocAlgCat.{w} Λ k) (I : Ideal A) [Nontrivial (A ⧸ I)] : A ⟶ A.ofQuot I :=
  letI : IsLocalRing (A ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  ofHom (IsScalarTower.toAlgHom Λ A (A ⧸ I)) (eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective
    _ Ideal.Quotient.mk_surjective)) (by ext; simpa [residue] using residue_ofQuot_mk_apply ..)

@[simp]
lemma toAlgHom_toOfQuot_apply [Nontrivial (A ⧸ I)] (a : A) :
    (A.toOfQuot I).toAlgHom a = Ideal.Quotient.mk I a := rfl

lemma coe_toAlgHom_toOfQuot [Nontrivial (A ⧸ I)] :
    (A.toOfQuot I).toAlgHom = algebraMap A (A.ofQuot I) := rfl

@[simp]
lemma ker_toAlgHom_toOfQuot [Nontrivial (A ⧸ I)] : RingHom.ker (A.toOfQuot I).toAlgHom = I :=
  Ideal.mk_ker

lemma surjective_toAlgHom_toOfQuot [Nontrivial (A ⧸ I)] : Surjective (A.toOfQuot I).toAlgHom :=
  Ideal.Quotient.mk_surjective

theorem map_toAlgHom_toOfQuot_maximalIdeal_eq [Nontrivial (A ⧸ I)] :
    (maximalIdeal A).map (A.toOfQuot I).toAlgHom = maximalIdeal (A.ofQuot I) :=
  map_maximalIdeal_of_surjective _ surjective_toAlgHom_toOfQuot

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

@[simp]
theorem toOfQuot_comp_mapOfQuot (f : A ⟶ B) {J : Ideal B} [Nontrivial (A ⧸ I)] [Nontrivial (B ⧸ J)]
    (hf : I ≤ J.comap f.toAlgHom) : A.toOfQuot I ≫ mapOfQuot f hf = f ≫ B.toOfQuot J := rfl

@[simp]
lemma toAlgHom_mapOfQuot_apply (f : A ⟶ B) {J : Ideal B} [Nontrivial (A ⧸ I)] [Nontrivial (B ⧸ J)]
    (hf : I ≤ J.comap f.toAlgHom) (a : A) : (mapOfQuot f hf).toAlgHom (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk J (f.toAlgHom a) := rfl

/-- The isomorphism between `A.ofQuot (RingHom.ker f.toAlgHom)` and the codomain `B`
when the underlying `AlgHom` of a morphism `f : A ⟶ B` is surjective.
This is the categorical counterpart to `Ideal.quotientKerAlgEquivOfSurjective`. -/
noncomputable def ofQuotKerIsoOfSurjective (f : A ⟶ B) (h : Surjective f.toAlgHom) :
    A.ofQuot (RingHom.ker f.toAlgHom) ≅ B := isoMk (Ideal.quotientKerAlgEquivOfSurjective h) (by
  ext x
  rcases Ideal.Quotient.mk_surjective x with ⟨x, rfl⟩
  change _ = (A.ofQuot (RingHom.ker f.toAlgHom)).residue _
  simp [← AlgHom.comp_apply, f.residue_comp])

@[simp]
lemma toAlgHom_ofQuotKerIsoOfSurjective_hom_apply {f : A ⟶ B} (h : Surjective f.toAlgHom) (a : A) :
    (ofQuotKerIsoOfSurjective f h).hom.toAlgHom (Ideal.Quotient.mk (RingHom.ker f.toAlgHom) a) =
      f.toAlgHom a := rfl

@[simp]
lemma toAlgHom_ofQuotKerIsoOfSurjective_inv_apply {f : A ⟶ B} (h : Surjective f.toAlgHom) (a : A) :
    (ofQuotKerIsoOfSurjective f h).inv.toAlgHom (f.toAlgHom a) =
      Ideal.Quotient.mk (RingHom.ker f.toAlgHom) a :=
  (Ideal.quotientKerAlgEquivOfSurjective h).symm_apply_apply a

@[simp]
lemma toOfQuot_comp_ofQuotKerIsoOfSurjective_hom {f : A ⟶ B} (h : Surjective f.toAlgHom) :
    A.toOfQuot (RingHom.ker f.toAlgHom) ≫ (ofQuotKerIsoOfSurjective f h).hom = f := Hom.ext rfl

/-- The quotient of a local algebra by the `n`-th power of its maximal ideal.
Geometrically, this represents an infinitesimal neighborhood of the closed point. -/
abbrev infinitesimalNeighborhood (n : ℕ) [NeZero n] (A : LocAlgCat.{w} Λ k) : LocAlgCat Λ k :=
  A.ofQuot (maximalIdeal A ^ n)

/-- The canonical quotient morphism from `A` to its infinitesimal neighborhood. -/
abbrev toInfinitesimalNeighborhood (n : ℕ) [NeZero n] (A : LocAlgCat.{w} Λ k) :
    A ⟶ A.infinitesimalNeighborhood n := toOfQuot ..

/-- The morphism between infinitesimal neighborhoods induced by a morphism in `LocAlgCat`. -/
abbrev mapInfinitesimalNeighborhood (m n : ℕ) [NeZero m] [NeZero n] (hmn : n ≤ m) (f : A ⟶ B) :
    A.infinitesimalNeighborhood m ⟶ B.infinitesimalNeighborhood n :=
  mapOfQuot f (le_trans (Ideal.pow_le_pow_right hmn) (f.comap_maximalIdeal_eq ▸
      Ideal.le_comap_pow f.toAlgHom n))

lemma toInfinitesimalNeighborhood_comp_map (m n : ℕ) [NeZero m] [NeZero n] (hmn : n ≤ m)
    (f : A ⟶ B) : A.toInfinitesimalNeighborhood m ≫ mapInfinitesimalNeighborhood m n hmn f =
      f ≫ B.toInfinitesimalNeighborhood n := by simp

/-- The special fiber of `A` over `Λ` when `Λ` is a local ring, defined as the quotient by
the extended maximal ideal of `Λ`, viewed as an object in `LocAlgCat`. -/
abbrev specialFiber [IsLocalRing Λ] [IsLocalHom (algebraMap Λ k)]
    (A : LocAlgCat.{w} Λ k) : LocAlgCat.{w} Λ k :=
  A.ofQuot ((maximalIdeal Λ).map (algebraMap Λ A))

/-- The canonical morphism from `A` to its special fiber. -/
abbrev toSpecialFiber [IsLocalRing Λ] [IsLocalHom (algebraMap Λ k)]
    (A : LocAlgCat.{w} Λ k) : A ⟶ A.specialFiber := toOfQuot ..

/-- The morphism between special fibers induced by a morphism between two objects. -/
abbrev mapSpecialFiber [IsLocalRing Λ] [IsLocalHom (algebraMap Λ k)]
    (f : A ⟶ B) : A.specialFiber ⟶ B.specialFiber :=
  mapOfQuot f (by rw [Ideal.map_le_iff_le_comap, ← Ideal.comap_coe f.toAlgHom,
    Ideal.comap_comap, AlgHom.comp_algebraMap, ← Ideal.map_le_iff_le_comap])

@[simp]
lemma algebraMap_specialFiber_apply_eq_zero [IsLocalRing Λ] [IsLocalHom (algebraMap Λ k)]
    (A : LocAlgCat.{w} Λ k) {y : Λ} (y_in : y ∈ maximalIdeal Λ) :
    algebraMap Λ A.specialFiber y = 0 := by
  rw [IsScalarTower.algebraMap_apply Λ A A.specialFiber]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ y_in)

lemma toInfinitesimalNeighborhood_comp_mapInfinitesimalNeighborhood_toSpecialFiber [IsLocalRing Λ]
    [IsLocalHom (algebraMap Λ k)] (n : ℕ) [NeZero n] (A : LocAlgCat.{w} Λ k) :
    A.toInfinitesimalNeighborhood n ≫ mapInfinitesimalNeighborhood n n le_rfl A.toSpecialFiber =
      A.toSpecialFiber ≫ (A.specialFiber).toInfinitesimalNeighborhood n := by simp

end ofQuot

section ofPullback

variable {f : A ⟶ C} {g : B ⟶ C}

instance ofPullbackResidueAlgebra : Algebra (f.toAlgHom.pullback g.toAlgHom) k :=
  fast_instance% (A.residue.comp (f.toAlgHom.pullbackFst g.toAlgHom)).toAlgebra

instance isScalarTower_ofPullbackResidueAlgebra :
    IsScalarTower Λ (f.toAlgHom.pullback g.toAlgHom) k := .of_algebraMap_eq (by
  simp [RingHom.algebraMap_toAlgebra])

/-- Given morphisms `f : A ⟶ C` and `g : B ⟶ C` in `LocAlgCat` where `g.toAlgHom` is surjective,
`ofPullback` is the object in `LocAlgCat` obtained from the pullback of the underlying
algebra homomorphisms`. -/
def ofPullback (f : A ⟶ C) (g : B ⟶ C) (hg : Surjective g.toAlgHom) : LocAlgCat.{w} Λ k :=
  letI : IsLocalRing ↥(f.toAlgHom.pullback g.toAlgHom) :=
    isLocalRing_algHomPullback f.toAlgHom g.toAlgHom ⟨hg.isLocalHom.map_nonunit⟩
  of Λ k (f.toAlgHom.pullback g.toAlgHom) (by
    simpa [RingHom.algebraMap_toAlgebra] using Surjective.comp A.surj
      (AlgHom.surjective_pullbackFst_of_surjective _ _ hg))

/-- Upgrades the first projection map from the pullback algebra to a morphism in `LocAlgCat`. -/
abbrev pullbackFst (f : A ⟶ C) (g : B ⟶ C) (hg : Surjective g.toAlgHom) :
    ofPullback f g hg ⟶ A :=
  letI : IsLocalRing ↥(f.toAlgHom.pullback g.toAlgHom) :=
    isLocalRing_algHomPullback f.toAlgHom g.toAlgHom ⟨hg.isLocalHom.map_nonunit⟩
  ⟨f.toAlgHom.pullbackFst g.toAlgHom, eq_maximalIdeal <| Ideal.comap_isMaximal_of_surjective _
    (AlgHom.surjective_pullbackFst_of_surjective f.toAlgHom g.toAlgHom hg), rfl⟩

lemma residue_comp_pullbackFst (f : A ⟶ C) (g : B ⟶ C) :
    A.residue.comp (f.toAlgHom.pullbackFst g.toAlgHom) =
      B.residue.comp (f.toAlgHom.pullbackSnd g.toAlgHom) := by
  ext ⟨_, h⟩
  simp only [AlgHom.mem_equalizer, AlgHom.coe_comp, Function.comp_apply, AlgHom.fst_apply,
    AlgHom.snd_apply, Subalgebra.coe_val] at h ⊢
  rw [← DFunLike.congr_fun f.residue_comp, ← DFunLike.congr_fun g.residue_comp,
    AlgHom.comp_apply, AlgHom.comp_apply, ← h]

/-- Upgrades the second projection map from the pullback algebra to a morphism in `LocAlgCat`. -/
abbrev pullbackSnd (f : A ⟶ C) (g : B ⟶ C) (hg : Surjective g.toAlgHom) :
    ofPullback f g hg ⟶ B :=
  letI : IsLocalRing ↥(f.toAlgHom.pullback g.toAlgHom) :=
    isLocalRing_algHomPullback f.toAlgHom g.toAlgHom ⟨hg.isLocalHom.map_nonunit⟩
  haveI : IsLocalHom f.toAlgHom.toRingHom := ⟨f.isLocalHom_toAlgHom.map_nonunit⟩
  haveI : IsLocalHom (f.toAlgHom.pullbackSnd g.toAlgHom).toRingHom :=
    ⟨(RingHom.isLocalHom_pullbackSnd f.toAlgHom.toRingHom g.toAlgHom.toRingHom).map_nonunit⟩
  ⟨f.toAlgHom.pullbackSnd g.toAlgHom, IsLocalRing.maximalIdeal_comap
    (f.toAlgHom.pullbackSnd g.toAlgHom).toRingHom, (residue_comp_pullbackFst ..).symm⟩

lemma pullbackFst_comp_eq_pullbackSnd_comp (f : A ⟶ C) (g : B ⟶ C) (hg : Surjective g.toAlgHom) :
    pullbackFst f g hg ≫ f = pullbackSnd f g hg ≫ g :=
  Hom.ext <| AlgHom.comp_pullbackFst_eq_comp_pullbackSnd f.toAlgHom g.toAlgHom

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
theorem length_restrictScalars {M : Type*} [AddCommGroup M] [Module A M] [Module Λ M]
    [IsScalarTower Λ A M] : length Λ M = finrank (ResidueField Λ) k * length A M := by
  rw [IsLocalRing.length_restrictScalars Λ A M, mul_comm, ← length_eq_finrank,
    (A.residueEquiv.toLinearEquiv.extendScalarsOfSurjective <|
      IsLocalRing.residue_surjective (R := Λ)).length_eq]

example [IsArtinianRing A] : IsNoetherianRing A :=
  isNoetherian_of_isNoetherianRing_of_finite A A

variable (A) in
theorem isFiniteLength_of_isArtinianRing [IsArtinianRing A] : IsFiniteLength Λ A := by
  rw [← Module.length_ne_top_iff, length_restrictScalars (A := A)]
  have (n : ℕ) (s : ENat) (hs : s ≠ ⊤) : n * s ≠ ⊤ := by
    lift s to ℕ using hs
    exact WithTop.coe_ne_top
  exact this _ _ Module.length_ne_top

instance [IsArtinianRing A] : IsNoetherian Λ A :=
  (isFiniteLength_iff_isNoetherian_isArtinian.mp (isFiniteLength_of_isArtinianRing A)).left

instance [IsArtinianRing A] : IsArtinian Λ A :=
  (isFiniteLength_iff_isNoetherian_isArtinian.mp (isFiniteLength_of_isArtinianRing A)).right

instance [IsArtinianRing A] [IsArtinianRing B] (f : A ⟶ C) (g : B ⟶ C) :
    IsArtinianRing (f.toAlgHom.pullback g.toAlgHom) := by
  let PB := f.toAlgHom.pullback g.toAlgHom
  rw [isArtinianRing_iff_isFiniteLength, ← Module.length_ne_top_iff]
  refine ne_top_of_le_ne_top (b := Module.length Λ PB) ?_ ?_
  · refine ne_top_of_le_ne_top (b := Module.length Λ (A × B)) ?_ ?_
    · rw [Module.length_prod]
      exact WithTop.add_ne_top.mpr ⟨Module.length_ne_top, Module.length_ne_top⟩
    · exact Module.length_le_of_injective (Submodule.subtype PB.toSubmodule)
        (Submodule.subtype_injective _)
  have := Submodule.length_le_length_restrictScalars (R := PB) (M := PB) Λ ⊤
  rwa [Module.length_top, Submodule.restrictScalars_top, Module.length_top] at this

theorem isArtinianRing_ofPullback [IsArtinianRing A] [IsArtinianRing B] (f : A ⟶ C) (g : B ⟶ C)
    (h : Surjective g.toAlgHom) : IsArtinianRing (ofPullback f g h) := by
  rw [ofPullback]
  infer_instance

end ArtinianRing

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

---------------------------------------------------------------------------------

-- From Wenrong Zou

section ofTensor

open scoped TensorProduct

instance tensorResidueAlgebra (f : A ⟶ B) (g : A ⟶ C) :
    letI : Algebra A B := RingHom.toAlgebra f.toAlgHom
    letI : Algebra A C := RingHom.toAlgebra g.toAlgHom
    Algebra (B ⊗[A] C) k :=
  letI : Algebra A B := RingHom.toAlgebra f.toAlgHom
  letI : Algebra A C := RingHom.toAlgebra g.toAlgHom
  fast_instance% (Algebra.TensorProduct.lift
    (.mk (algebraMap B k) (AlgHom.congr_fun f.residue_comp))
      (.mk (algebraMap C k) (AlgHom.congr_fun g.residue_comp))
        (fun _ _ ↦ mul_comm _ _)).toRingHom.toAlgebra

instance IsScalarTower_tensorResidueAlgebra (f : A ⟶ B) (g : A ⟶ C) :
    letI : Algebra A B := RingHom.toAlgebra f.toAlgHom
    letI : Algebra A C := RingHom.toAlgebra g.toAlgHom
    IsScalarTower Λ (B ⊗[A] C) k :=
  letI : Algebra A B := RingHom.toAlgebra f.toAlgHom
  letI : Algebra A C := RingHom.toAlgebra g.toAlgHom
  .of_algebraMap_eq (R := Λ) (S := B ⊗[A] C) fun r ↦ by
    simpa [RingHom.algebraMap_toAlgebra] using IsScalarTower.algebraMap_apply Λ B k _

theorem surjective_algebraMap_tensorResidueAlgebra (f : A ⟶ B) (g : A ⟶ C) :
    letI : Algebra A B := RingHom.toAlgebra f.toAlgHom
    letI : Algebra A C := RingHom.toAlgebra g.toAlgHom
    Surjective (algebraMap (B ⊗[A] C) k) := fun y ↦ by
  letI : Algebra A B := RingHom.toAlgebra f.toAlgHom
  letI : Algebra A C := RingHom.toAlgebra g.toAlgHom
  obtain ⟨b, rfl⟩ := B.surj y
  exact ⟨Algebra.TensorProduct.includeLeft (S := A) b, by simp [RingHom.algebraMap_toAlgebra]⟩

end ofTensor

noncomputable section ofAdicCompletion

variable (Λ) in
abbrev ofAdicCompletionResidueAlgebra (X : Type w) [CommRing X] [Algebra Λ X] [Algebra X k]
    [IsScalarTower Λ X k] {I : Ideal X} (hI : I ≤ RingHom.ker (algebraMap X k)) :
    Algebra (AdicCompletion I X) k :=
  ((Ideal.Quotient.lift I (algebraMap X k) (by simpa [← RingHom.mem_ker])).comp
    (AdicCompletion.evalOneₐ I).toRingHom).toAlgebra

lemma isScalarTower_ofAdicCompletionResidueAlgebra (X : Type w) [CommRing X] [Algebra Λ X]
    [Algebra X k] [IsScalarTower Λ X k] {I : Ideal X} (hI : I ≤ RingHom.ker (algebraMap X k)) :
    @IsScalarTower Λ (AdicCompletion I X) k _ (ofAdicCompletionResidueAlgebra Λ X hI).toSMul _ :=
  letI := ofAdicCompletionResidueAlgebra Λ X hI
  .of_algebraMap_eq fun _ ↦ (IsScalarTower.algebraMap_apply Λ X k _) ▸ rfl

def ofAdicCompletion (X : Type w) [CommRing X] [Algebra Λ X] [Algebra X k] [IsScalarTower Λ X k]
    (hX : Surjective (algebraMap X k)) {m : Ideal X} (hm : m = RingHom.ker (algebraMap X k))
    (fg : m.FG) : LocAlgCat.{w} Λ k :=
  haveI : m.IsMaximal := hm ▸ RingHom.ker_isMaximal_of_surjective _ hX
  haveI := @isLocalRing_of_isAdicComplete_maximal _ _ (m.map (algebraMap X (AdicCompletion m X)))
    (AdicCompletion.isMaximal_map_of_le m m le_rfl fg) (AdicCompletion.isAdicComplete_self m fg)
  letI : Algebra (AdicCompletion m X) k := ofAdicCompletionResidueAlgebra Λ X hm.le
  haveI : IsScalarTower Λ (AdicCompletion m X) k := isScalarTower_ofAdicCompletionResidueAlgebra ..
  of Λ k (AdicCompletion m X) sorry

end ofAdicCompletion

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

lemma mapCotangent_comp (f : A ⟶ B) (g : B ⟶ C) :
    mapCotangent (f ≫ g) = mapCotangent g ∘ₗ mapCotangent f := LinearMap.ext fun _ ↦ by
  simp [mapCotangent, ← LinearMap.comp_apply, ← Ideal.mapCotangent_comp]

@[simp]
lemma mapCotangent_id (A : LocAlgCat Λ k) : mapCotangent (𝟙 A) = LinearMap.id := by
  ext x
  rcases (maximalIdeal A).toCotangent_surjective x with ⟨x, rfl⟩
  simp

/-- The `k`-linear equivalence between cotangent spaces induced by
an isomorphism in `LocAlgCat`. -/
def equivCotangent (e : A ≅ B) : CotangentSpace A ≃ₗ[k] CotangentSpace B where
  __ := mapCotangent e.hom
  invFun := mapCotangent e.inv
  left_inv x := by simp [← LinearMap.comp_apply, ← mapCotangent_comp]
  right_inv y := by simp [← LinearMap.comp_apply, ← mapCotangent_comp]

@[simp]
lemma equivCotangent_apply (e : A ≅ B) (x : CotangentSpace A) :
    equivCotangent e x = mapCotangent e.hom x := rfl

@[simp]
lemma equivCotangent_symm_apply (e : A ≅ B) (y : CotangentSpace B) :
    (equivCotangent e).symm y = mapCotangent e.inv y := rfl

set_option backward.isDefEq.respectTransparency false in
theorem surjective_mapCotangent_toOfQuot (I : Ideal A) [Nontrivial (A ⧸ I)] :
    Surjective (mapCotangent (A.toOfQuot I)) := by
  have : RingHom.ker (algebraMap A (A.ofQuot I)) ≤ maximalIdeal A := le_maximalIdeal (by
    rwa [← coe_toAlgHom_toOfQuot, RingHom.ker_coe_toRingHom, ker_toAlgHom_toOfQuot,
      ← Ideal.Quotient.nontrivial_iff])
  refine Ideal.mapCotangent_surjective_of_comap_eq (fun _ ↦ Ideal.Quotient.mk_surjective _) ?_
  rw [sup_eq_right.mpr this]
  exact (A.toOfQuot I).comap_maximalIdeal_eq

theorem bijective_mapCotangent_toOfQuot_iff (I : Ideal A) [Nontrivial (A ⧸ I)] :
    Bijective (mapCotangent (A.toOfQuot I)) ↔ I ≤ maximalIdeal A ^ 2 := by
  simp only [Bijective, surjective_mapCotangent_toOfQuot I, and_true]
  simp_rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff, LinearMap.mem_ker]
  refine ⟨fun h x hx ↦ ?_, fun h ↦ ?_⟩
  · have x_mem_m : x ∈ maximalIdeal A :=
      le_maximalIdeal (Ideal.Quotient.nontrivial_iff.mp inferInstance) hx
    let x_cot := (maximalIdeal A).toCotangent ⟨x, x_mem_m⟩
    have h_map_zero : mapCotangent (A.toOfQuot I) x_cot = 0 := by
      rw [mapCotangent_toCotangent, Ideal.toCotangent_eq_zero]
      change (A.toOfQuot I).toAlgHom x ∈ _
      rw [← ker_toAlgHom_toOfQuot (I := I), RingHom.mem_ker] at hx
      exact hx ▸ zero_mem _
    specialize h x_cot h_map_zero
    rwa [Ideal.toCotangent_eq_zero] at h
  intro x hx
  rcases (maximalIdeal A).toCotangent_surjective x with ⟨x, rfl⟩
  simp only [mapCotangent_toCotangent, toAlgHom_toOfQuot_apply, Ideal.toCotangent_eq_zero] at hx ⊢
  change (A.toOfQuot I).toAlgHom x ∈ _ at hx
  rwa [← map_toAlgHom_toOfQuot_maximalIdeal_eq, ← Ideal.mem_comap, ← Ideal.map_pow,
    Ideal.comap_map_of_surjective' _ surjective_toAlgHom_toOfQuot, ker_toAlgHom_toOfQuot,
    sup_eq_left.mpr h] at hx

@[stacks 06S3 "(1) => (2)"]
theorem surjective_mapCotangent_of_surjective {f : A ⟶ B} (h : Surjective f.toAlgHom) :
    Surjective (mapCotangent f) := by
  rw [← toOfQuot_comp_ofQuotKerIsoOfSurjective_hom h, mapCotangent_comp, LinearMap.coe_comp]
  exact Function.Surjective.comp (equivCotangent (ofQuotKerIsoOfSurjective f h)).surjective
    (surjective_mapCotangent_toOfQuot _)

theorem bijective_mapCotangent_iff {f : A ⟶ B} (hf : Surjective f.toAlgHom) :
    Function.Bijective (mapCotangent f) ↔ RingHom.ker f.toAlgHom ≤ maximalIdeal A ^ 2 := by
  rw [← bijective_mapCotangent_toOfQuot_iff]
  have h_comp : mapCotangent f = (mapCotangent (ofQuotKerIsoOfSurjective f hf).hom) ∘ₗ
      (mapCotangent (A.toOfQuot (RingHom.ker f.toAlgHom))) := by
    rw [← mapCotangent_comp, toOfQuot_comp_ofQuotKerIsoOfSurjective_hom hf]
  refine ⟨fun h_bij ↦ ?_, fun h_bij ↦ ?_⟩
  · suffices ⇑(mapCotangent (A.toOfQuot (RingHom.ker f.toAlgHom))) =
      ⇑(equivCotangent (ofQuotKerIsoOfSurjective f hf)).symm ∘ ⇑(mapCotangent f) from
      this ▸ Bijective.comp (equivCotangent (ofQuotKerIsoOfSurjective f hf)).symm.bijective h_bij
    ext
    simp only [h_comp, LinearMap.coe_comp, Function.comp_apply, equivCotangent_symm_apply]
    rw [← LinearMap.comp_apply, ← mapCotangent_comp]
    simp
  · rw [h_comp, LinearMap.coe_comp]
    exact Bijective.comp (equivCotangent (ofQuotKerIsoOfSurjective f hf)).bijective h_bij

@[stacks 06S3 "(2) => (3)"]
theorem mapCotangent_mapOfQuot_surjective_of_mapCotangent_surjective {I : Ideal A} {J : Ideal B}
    {f : A ⟶ B} [Nontrivial (A ⧸ I)] [Nontrivial (B ⧸ J)] (hf : I ≤ J.comap f.toAlgHom)
    (h : Surjective (mapCotangent f)) : Surjective (mapCotangent (mapOfQuot f hf)) := by
  have : Surjective ((mapCotangent (mapOfQuot f hf)) ∘ₗ (mapCotangent (A.toOfQuot I))) := by
    rw [← mapCotangent_comp, toOfQuot_comp_mapOfQuot, mapCotangent_comp, LinearMap.coe_comp]
    exact .comp (surjective_mapCotangent_toOfQuot J) h
  exact .of_comp this

@[stacks 06GZ "(2) => (1)"]
theorem surjective_of_surjective_mapCotangent [IsPrecomplete (maximalIdeal A) A]
    [IsNoetherianRing B] [haus : IsHausdorff (maximalIdeal B) B] (f : A ⟶ B)
    (h : Surjective (mapCotangent f)) : Surjective f.toAlgHom := by
  have map_eq : (maximalIdeal A).map f.toAlgHom = maximalIdeal B := by
    let M : Submodule B (maximalIdeal B) := Submodule.comap (maximalIdeal B).subtype
      ((maximalIdeal A).map f.toAlgHom)
    suffices M = ⊤ by
      refine le_antisymm f.map_maximalIdeal_le fun b hb ↦ ?_
      have hb_mem : (⟨b, hb⟩ : maximalIdeal B) ∈ (⊤ : Submodule B (maximalIdeal B)) := trivial
      rwa [← this] at hb_mem
    rw [← CotangentSpace.map_eq_top_iff, Submodule.eq_top_iff']
    intro x
    obtain ⟨x, rfl⟩ := h x
    obtain ⟨x, rfl⟩ := (maximalIdeal A).toCotangent_surjective x
    rw [mapCotangent_toCotangent]
    exact Submodule.mem_map_of_mem <| Ideal.mem_map_of_mem f.toAlgHom x.prop
  rw [← map_eq, ← Ideal.map_coe, ← AlgHom.toRingHom_eq_coe] at haus
  apply surjective_of_mk_map_comp_surjective (I := maximalIdeal A)
  intro y
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨x, hx⟩ := A.residue_surjective (B.residue y)
  use x
  rw [RingHom.comp_apply, Ideal.Quotient.eq, AlgHom.toRingHom_eq_coe, Ideal.map_coe, map_eq,
    ← residue_eq_zero_iff, map_sub, sub_eq_zero, ← hx]
  exact DFunLike.congr_fun f.residue_comp x

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
    Surjective (mapCotangent A.toSpecialFiber) := surjective_mapCotangent_toOfQuot _

/-- The canonical `k`-linear map from the base-changed cotangent space of `Λ`
to the cotangent space of `A`, induced by the algebra structure map. -/
def baseCotangentMap [Algebra.IsIntegral Λ k] (A : LocAlgCat.{w} Λ k) :
    k ⊗[ResidueField Λ] CotangentSpace Λ →ₗ[k] CotangentSpace A :=
  haveI := isLocalHom_algebraMap_of_isIntegral Λ k
  letI baseMap : CotangentSpace Λ →ₗ[ResidueField Λ] CotangentSpace A :=
    ((maximalIdeal Λ).mapCotangent (maximalIdeal A) (Algebra.ofId Λ A) (by
      change _ ≤ Ideal.comap (algebraMap Λ A) _
      rw [comap_algebraMap_maximalIdeal])).extendScalarsOfSurjective
    IsLocalRing.residue_surjective
  TensorProduct.AlgebraTensorModule.lift (LinearMap.toSpanSingleton k _ baseMap)

@[simp]
lemma baseCotangentMap_tmul [Algebra.IsIntegral Λ k]
    (r : k) (a : CotangentSpace Λ) : A.baseCotangentMap (r ⊗ₜ a) =
      r • ((maximalIdeal Λ).mapCotangent (maximalIdeal A) (Algebra.ofId Λ A) (by
        have := isLocalHom_algebraMap_of_isIntegral Λ k
        change _ ≤ Ideal.comap (algebraMap Λ A) _
        rw [comap_algebraMap_maximalIdeal]) a) := rfl

@[simp]
lemma mapCotangent_baseCotangentMap_apply [Algebra.IsIntegral Λ k] (f : A ⟶ B)
    (z : k ⊗[ResidueField Λ] CotangentSpace Λ) :
    mapCotangent f (A.baseCotangentMap z) = B.baseCotangentMap z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r a =>
    rcases (maximalIdeal Λ).toCotangent_surjective a with ⟨a, rfl⟩
    simp
  | add x y hx hy => simp [hx, hy]

open Submodule in
theorem range_baseCotangentMap [Algebra.IsIntegral Λ k] :
    A.baseCotangentMap.range = (mapCotangent A.toSpecialFiber).ker := ext fun x ↦ by
  haveI := isLocalHom_algebraMap_of_isIntegral Λ k
  rcases (maximalIdeal A).toCotangent_surjective x with ⟨x, rfl⟩
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  refine ⟨fun ⟨y, hy⟩ ↦ ?_, fun hx ↦ ?_⟩
  · rw [← hy]; clear * -
    induction y with
    | zero => simp
    | tmul x y =>
      rcases (maximalIdeal Λ).toCotangent_surjective y with ⟨y, rfl⟩
      simp [Ideal.toCotangent_eq_zero]
    | add x y hx hy => simp [hx, hy]
  · rcases x with ⟨x, x_in⟩
    simp only [mapCotangent_toCotangent, toAlgHom_toOfQuot_apply, Ideal.toCotangent_eq_zero] at hx
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
    | zero => use 0; simp [show (⟨0, _⟩ : maximalIdeal A) = 0 by rfl]
    | add z w hz hw ihz ihw =>
      rw [show (⟨z + w, _⟩ : maximalIdeal A) = ⟨z, map_maximalIdeal_le _ hz⟩ +
        ⟨w, map_maximalIdeal_le _ hw⟩ by simp, map_add]
      exact add_mem (ihz hz) (ihw hw)
    | smul a x hx ihx =>
      rw [show (⟨a • x, _⟩ : maximalIdeal A) = a • ⟨x, map_maximalIdeal_le _ hx⟩ by simp, map_smul,
        ← residue_smul_cotangent]
      exact smul_mem _ _ (ihx hx)

theorem exact_baseCotangentMap_mapCotangent_toSpecialFiber [Algebra.IsIntegral Λ k] :
    Exact A.baseCotangentMap (mapCotangent A.toSpecialFiber) :=
  LinearMap.exact_iff.mpr A.range_baseCotangentMap.symm

@[stacks 06S3 "(3) => (2)"]
theorem surjective_mapCotangent_of_surjective_mapCotangent_mapSpecialFiber [Algebra.IsIntegral Λ k]
    (f : A ⟶ B) (h : Surjective (mapCotangent (mapSpecialFiber f))) :
    Surjective (mapCotangent f) := by
  intro y
  obtain ⟨x, hx⟩ := h (mapCotangent B.toSpecialFiber y)
  obtain ⟨x, rfl⟩ := surjective_mapCotangent_toSpecialFiber x
  rw [← LinearMap.comp_apply, ← mapCotangent_comp, toOfQuot_comp_mapOfQuot,
    mapCotangent_comp, LinearMap.comp_apply] at hx
  have h_ker : y - mapCotangent f x ∈ LinearMap.ker (mapCotangent B.toSpecialFiber) := by
    rw [LinearMap.mem_ker, map_sub, hx, sub_self]
  rw [← B.range_baseCotangentMap, LinearMap.mem_range] at h_ker
  rcases h_ker with ⟨z, hz⟩
  exact ⟨x + A.baseCotangentMap z, by simp [hz]⟩

end IsLocalRing

end Cotangent

end LocAlgCat

/-- The complete base category for deformation theory over `Λ`. This is the full subcategory of
`LocAlgCat Λ k` consisting of complete Noetherian local `Λ`-algebras with residue field `k`. -/
abbrev CBaseCat (Λ : Type u) [CommRing Λ] (k : Type v) [Field k] [Algebra Λ k] : Type _ :=
  ObjectProperty.FullSubcategory fun A : LocAlgCat.{w} Λ k ↦
    IsNoetherianRing A ∧ IsAdicComplete (maximalIdeal A) A

namespace CBaseCat

instance {A : CBaseCat Λ k} : IsNoetherianRing A.obj := A.property.left

instance {A : CBaseCat Λ k} : IsAdicComplete (maximalIdeal A.obj) A.obj := A.property.right

end CBaseCat

/-- The base category for deformation theory over `Λ`. This is the full subcategory of
`LocAlgCat Λ k` consisting of Artinian local `Λ`-algebras with residue field `k`. -/
@[stacks 06GC]
abbrev BaseCat (Λ : Type u) [CommRing Λ] (k : Type v) [Field k] [Algebra Λ k] : Type _ :=
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

/-- Upgrades the canonical quotient map `A → A ⧸ I` to a morphism in `BaseCat`. -/
abbrev toOfQuot (A : BaseCat.{w} Λ k) (I : Ideal A.obj) [Nontrivial (A.obj ⧸ I)] :
    A ⟶ A.ofQuot I := ObjectProperty.homMk (A.obj.toOfQuot I)

/-- The morphism between quotient objects in `BaseCat` induced by a morphism `f : A ⟶ B`.
This is the categorical counterpart to `Ideal.quotientMapₐ` in the Artinian setting. -/
abbrev mapOfQuot (f : A ⟶ B) {I : Ideal A.obj} {J : Ideal B.obj} [Nontrivial (A.obj ⧸ I)]
    [Nontrivial (B.obj ⧸ J)] (hf : I ≤ J.comap f.hom.toAlgHom) : A.ofQuot I ⟶ B.ofQuot J :=
  ObjectProperty.homMk <| LocAlgCat.mapOfQuot f.hom hf

lemma toOfQuot_comp_mapOfQuot (f : A ⟶ B) {I : Ideal A.obj} {J : Ideal B.obj}
    [Nontrivial (A.obj ⧸ I)] [Nontrivial (B.obj ⧸ J)] (hf : I ≤ J.comap f.hom.toAlgHom) :
    A.toOfQuot I ≫ mapOfQuot f hf = f ≫ B.toOfQuot J := rfl

/-- The quotient of a local Artinian algebra by the `n`-th power of its maximal ideal,
viewed as an object in `BaseCat`. -/
abbrev infinitesimalNeighborhood (n : ℕ) [NeZero n] (A : BaseCat.{w} Λ k) : BaseCat Λ k :=
  A.ofQuot (maximalIdeal A.obj ^ n)

/-- The canonical quotient morphism from `A` to its infinitesimal neighborhood in `BaseCat`. -/
abbrev toInfinitesimalNeighborhood (n : ℕ) [NeZero n] (A : BaseCat.{w} Λ k) :
    A ⟶ A.infinitesimalNeighborhood n := toOfQuot ..

/-- The morphism between infinitesimal neighborhoods induced by a morphism in `BaseCat`. -/
abbrev mapInfinitesimalNeighborhood (m n : ℕ) [NeZero m] [NeZero n] (hmn : n ≤ m) (f : A ⟶ B) :
    A.infinitesimalNeighborhood m ⟶ B.infinitesimalNeighborhood n :=
  ObjectProperty.homMk (LocAlgCat.mapInfinitesimalNeighborhood m n hmn f.hom)

/-- The special fiber of `A` over `Λ` when `Λ` is a local ring, defined as the quotient by
the extended maximal ideal of `Λ`, viewed as an object in `BaseCat`. -/
abbrev specialFiber [IsLocalRing Λ] [IsLocalHom (algebraMap Λ k)]
    (A : BaseCat.{w} Λ k) : BaseCat.{w} Λ k :=
  ⟨A.obj.specialFiber, Ideal.Quotient.mk_surjective.isArtinianRing⟩

/-- The canonical morphism from `A` to its special fiber in `BaseCat`. -/
abbrev toSpecialFiber [IsLocalRing Λ] [IsLocalHom (algebraMap Λ k)]
    (A : BaseCat.{w} Λ k) : A ⟶ A.specialFiber :=
  ObjectProperty.homMk A.obj.toSpecialFiber

/-- The morphism between special fibers induced by a morphism in `BaseCat`. -/
abbrev mapSpecialFiber [IsLocalRing Λ] [IsLocalHom (algebraMap Λ k)]
    (f : A ⟶ B) : A.specialFiber ⟶ B.specialFiber :=
  ObjectProperty.homMk (LocAlgCat.mapSpecialFiber f.hom)

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

instance IsSmallExtension.hom_iso (e : A ≅ B) : IsSmallExtension e.hom := by
  apply isSmallExtension_of_bijective
  rw [bijective_iff_has_inverse]
  use e.inv.hom.toAlgHom
  simp [leftInverse_iff_comp, rightInverse_iff_comp, ← AlgHom.coe_comp, ← LocAlgCat.toAlgHom_comp]

theorem IsSmallExtension.toOfQuot_span_singleton (A : BaseCat.{w} Λ k) (x : A.obj)
    [Nontrivial (A.obj ⧸ (Ideal.span {x}))] (h : ∀ y ∈ maximalIdeal A.obj, x * y = 0) :
    IsSmallExtension (A.toOfQuot (Ideal.span {x})) := by
  rw [isSmallExtenstion_iff]
  refine ⟨Ideal.Quotient.mk_surjective, x, ?_, h⟩
  change _ = RingHom.ker (A.obj.toOfQuot (Ideal.span {x})).toAlgHom
  rw [LocAlgCat.ker_toAlgHom_toOfQuot]

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
    have := Submodule.length_le_length_restrictScalars (R := (A.obj ⧸ Ideal.span {x}))
      (M := (A.obj ⧸ Ideal.span {x})) A.obj ⊤
    rw [Module.length_top, restrictScalars_top, Module.length_top] at this
    rw [← ENat.coe_lt_coe, ← hlen, ← hm]
    exact lt_of_le_of_lt this (length_quotient_lt (Ideal.span {x}) (by simpa))

/-- A morphism `f : A ⟶ B` in the base category is called essentially surjective if its
underlying algebra homomorphism is surjective, and it satisfies the following minimality
condition: for any object `C` and morphism `g : C ⟶ A` in `BaseCat`, if the composition
`g ≫ f` is surjective, then `g` itself must be surjective. -/
@[stacks 06GF, mk_iff]
class IsEssSurj (f : A ⟶ B) : Prop where
  surjective (f) : Surjective f.hom.toAlgHom
  surjective_of_comp_left (f) {C : BaseCat.{w} Λ k} (g : C ⟶ A) :
    Surjective (g ≫ f).hom.toAlgHom → Surjective g.hom.toAlgHom

instance IsEssSurj.hom_iso (e : A ≅ B) : IsEssSurj e.hom := by
  constructor
  · rw [surjective_iff_hasRightInverse]
    use e.inv.hom.toAlgHom
    simp [rightInverse_iff_comp, ← AlgHom.coe_comp, ← LocAlgCat.toAlgHom_comp]
  · intro C g hg
    rw [ObjectProperty.FullSubcategory.comp_hom, LocAlgCat.toAlgHom_comp, AlgHom.coe_comp] at hg
    apply Surjective.of_comp_left hg
    rw [injective_iff_hasLeftInverse]
    use e.inv.hom.toAlgHom
    simp [leftInverse_iff_comp, ← AlgHom.coe_comp, ← LocAlgCat.toAlgHom_comp]

instance IsEssSurj.comp (f : A ⟶ B) (g : B ⟶ C) [IsEssSurj f] [IsEssSurj g] :
    IsEssSurj (f ≫ g) :=
  ⟨by simpa using .comp (IsEssSurj.surjective g) (IsEssSurj.surjective f), fun _ h ↦
    IsEssSurj.surjective_of_comp_left f _ (IsEssSurj.surjective_of_comp_left g _ h)⟩

theorem isEssSurj_toOfQuot_of_le {I : Ideal A.obj} [Nontrivial (A.obj ⧸ I)]
    (h : I ≤ maximalIdeal A.obj ^ 2) : IsEssSurj (A.toOfQuot I) := by
  rw [← LocAlgCat.bijective_mapCotangent_toOfQuot_iff] at h
  refine ⟨Ideal.Quotient.mk_surjective, fun {C} g hg ↦ ?_⟩
  apply LocAlgCat.surjective_of_surjective_mapCotangent
  apply Surjective.of_comp_left (f := LocAlgCat.mapCotangent (A.obj.toOfQuot I))
  · rw [← LinearMap.coe_comp, ← LocAlgCat.mapCotangent_comp]
    exact LocAlgCat.surjective_mapCotangent_of_surjective hg
  · exact h.injective

instance IsEssSurj.toInfinitesimalNeighborhood : IsEssSurj (A.toInfinitesimalNeighborhood 2) :=
  isEssSurj_toOfQuot_of_le (I := maximalIdeal A.obj ^ 2) le_rfl

section IsLocalRing

variable [IsLocalRing Λ] [Module.Finite Λ k]

/-- Given morphisms `f : A ⟶ C` and `g : B ⟶ C` in `BaseCat` where `g.hom.toAlgHom` is surjective,
`ofPullback` is the object in `BaseCat` obtained from the pullback of the underlying
algebra homomorphisms`. -/
@[stacks 06GH "(1)" ]
def ofPullback (f : A ⟶ C) (g : B ⟶ C) (hg : Surjective g.hom.toAlgHom) : BaseCat.{w} Λ k :=
  ⟨.ofPullback f.hom g.hom hg, LocAlgCat.isArtinianRing_ofPullback ..⟩

/-- Upgrades the first projection map from the pullback algebra to a morphism in `BaseCat`. -/
abbrev pullbackFst (f : A ⟶ C) (g : B ⟶ C) (hg : Surjective g.hom.toAlgHom) :
    ofPullback f g hg ⟶ A := ObjectProperty.homMk (LocAlgCat.pullbackFst f.hom g.hom hg)

/-- Upgrades the second projection map from the pullback algebra to a morphism in `BaseCat`. -/
abbrev pullbackSnd (f : A ⟶ C) (g : B ⟶ C) (hg : Surjective g.hom.toAlgHom) :
    ofPullback f g hg ⟶ B := ObjectProperty.homMk (LocAlgCat.pullbackSnd f.hom g.hom hg)

@[stacks 06GH "(2)"]
instance pullbackFst_isSmallExtension (f : A ⟶ C) (g : B ⟶ C) [IsSmallExtension g] :
    IsSmallExtension (pullbackFst f g (IsSmallExtension.surjective g)) := by
  obtain ⟨x, x_span, hx⟩ := ((isSmallExtenstion_iff (f := g)).mp ‹_›).right
  rw [isSmallExtenstion_iff]; constructor
  · exact f.hom.toAlgHom.surjective_pullbackFst_of_surjective g.hom.toAlgHom
      (IsSmallExtension.surjective g)
  · have : (0, x) ∈ f.hom.toAlgHom.pullback g.hom.toAlgHom := by
      simp only [AlgHom.mem_equalizer, AlgHom.coe_comp, Function.comp_apply, AlgHom.fst_apply,
        map_zero, AlgHom.snd_apply]
      rw [eq_comm, ← RingHom.mem_ker, ← x_span]
      exact Ideal.mem_span_singleton_self x
    refine ⟨⟨(0, x), this⟩, ?_, fun ⟨⟨a, b⟩, hab⟩ h ↦ ?_⟩
    · change (Ideal.span {⟨(0, x), this⟩} : Ideal (f.hom.toAlgHom.pullback g.hom.toAlgHom)) =
        RingHom.ker (AlgHom.pullbackFst ..)
      ext ⟨⟨u, v⟩, h⟩
      simp only [Ideal.mem_span_singleton', eq_comm, Subtype.exists,
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
    · rw [mem_maximalIdeal, mem_nonunits_iff] at h
      change ¬ IsUnit (⟨(a, b), hab⟩ : f.hom.toAlgHom.pullback g.hom.toAlgHom) at h
      rw [AlgHom.isUnit_pullback_mk_iff, not_and] at h
      change (⟨(0, x), this⟩ * ⟨(a, b), hab⟩ : f.hom.toAlgHom.pullback g.hom.toAlgHom) = 0
      suffices ¬ IsUnit b by simpa [← Subtype.val_inj] using hx b this
      intro hb
      simp only [AlgHom.mem_equalizer, AlgHom.coe_comp, Function.comp_apply, AlgHom.fst_apply,
        AlgHom.snd_apply] at hab
      have : IsUnit ((LocAlgCat.Hom.toAlgHom f.hom) a) := hab ▸ IsUnit.map g.hom.toAlgHom hb
      apply f.hom.isLocalHom_toAlgHom.map_nonunit at this
      exact (iff_false_intro (h this)).mp hb

/-- When `Λ` is a local ring and `k` over the residue field of `Λ` is
a finite separable field extension, `ofPullbackOfIsSeparable` is the object in `BaseCat`
obtained from the pullback of the underlying algebra homomorphisms of two morphisms`. -/
def ofPullbackOfIsSeparable [Algebra.IsSeparable (ResidueField Λ) k] (f : A ⟶ C) (g : B ⟶ C) :
    BaseCat Λ k :=
  haveI : IsLocalRing ↥(f.hom.toAlgHom.pullback g.hom.toAlgHom) :=
    isLocalRing_algHomPullback _ _ g.hom.isLocalHom_toAlgHom
  ⟨.of Λ k (f.hom.toAlgHom.pullback g.hom.toAlgHom)
    (LocAlgCat.surjective_residue_comp_pullbackFst_of_isSeparable f.hom g.hom), inferInstance⟩

@[stacks 06S5]
theorem isEssSurj_TFAE [IsLocalHom (algebraMap Λ k)] (f : A ⟶ B) : List.TFAE [IsEssSurj f,
    IsEssSurj (mapInfinitesimalNeighborhood 2 2 le_rfl f), IsEssSurj
      (mapInfinitesimalNeighborhood 2 2 le_rfl <| mapSpecialFiber f)] := by
  tfae_have 1 → 2 := by
    rintro ⟨surj, comp⟩
    have surj' : Surjective (mapInfinitesimalNeighborhood 2 2 le_rfl f).hom.toAlgHom := by
      apply Surjective.of_comp (g := (A.toInfinitesimalNeighborhood 2).hom.toAlgHom)
      simp only [ObjectProperty.homMk_hom, ← AlgHom.coe_comp, ← LocAlgCat.toAlgHom_comp]
      simp only [ofQuot, LocAlgCat.toOfQuot_comp_mapOfQuot, LocAlgCat.toAlgHom_comp]
      exact fun r ↦ Surjective.comp (B.obj.surjective_toAlgHom_toOfQuot
        (I := maximalIdeal B.obj ^ 2)) surj r
    refine ⟨surj', fun {C} g hg ↦ ?_⟩
    let C' := ofPullback g (A.toInfinitesimalNeighborhood 2) Ideal.Quotient.mk_surjective
    let p : C' ⟶ C :=
      pullbackFst g (A.toInfinitesimalNeighborhood 2) Ideal.Quotient.mk_surjective
    sorry
  sorry

end IsLocalRing

end BaseCat

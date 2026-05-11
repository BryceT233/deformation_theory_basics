/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

module

public import Mathlib

@[expose] public section

universe v u

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
  refine (Submodule.ne_bot_iff _).mpr ⟨x, mem_inf.mpr ⟨mem_annihilator.mpr fun r r_in ↦ ?_,
    Ideal.mul_le_right x_in⟩, x_ne⟩
  rw [smul_eq_mul, ← mem_bot, ← ht, ← hs, pow_succ, ← smul_eq_mul, ← smul_assoc]
  exact smul_mem_smul x_in r_in

--------------------------------------------------------------------------------

namespace RingHom

section eqLocus

theorem isUnit_eqLocus_mk_iff {R S : Type*} [Ring R] [Semiring S] (f g : R →+* S) {r : R}
    (r_in : r ∈ f.eqLocus g) : IsUnit (⟨r, r_in⟩ : f.eqLocus g) ↔ IsUnit r := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp [isUnit_iff_exists, ← Subtype.val_inj] at h ⊢
    grind
  rw [mem_eqLocus] at r_in
  obtain ⟨s, hs⟩ := isUnit_iff_exists.mp h
  suffices ∃ a, r * a = 1 ∧ f a = g a ∧ a * r = 1 by simpa [isUnit_iff_exists, ← Subtype.val_inj]
  refine ⟨s, hs.left, ?_, hs.right⟩
  rw [← mul_one (f s), ← map_one g, ← hs.left, map_mul, ← mul_assoc, ← r_in, ← map_mul, hs.right,
    map_one, one_mul]

theorem isLocalRing_eqLocus {R S : Type*} [Ring R] [Semiring S] [IsLocalRing R] (f g : R →+* S) :
    IsLocalRing (f.eqLocus g) :=
  Subring.isLocalRing_of_unit _ fun _ h ↦ (RingHom.isUnit_eqLocus_mk_iff f g h).mpr

end eqLocus

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

theorem pullback_comm_sq (f : R →+* T) (g : S →+* T) :
    f.comp (f.pullbackFst g) = g.comp (f.pullbackSnd g) := ext fun x ↦ x.prop

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

theorem surjective_pullbackFst_of_surjective (f : R →+* T) (g : S →+* T)
    (h : Function.Surjective g) : Function.Surjective (f.pullbackFst g) :=
  fun r ↦ by simpa [eq_comm] using h (f r)

theorem surjective_pullbackSnd_of_surjective (f : R →+* T) (g : S →+* T)
    (h : Function.Surjective f) : Function.Surjective (f.pullbackSnd g) :=
  fun s ↦ by simpa [eq_comm] using h (g s)

theorem map_pullbackSnd_ker_pullbackFst_eq (f : R →+* T) (g : S →+* T) :
    Ideal.map (f.pullbackSnd g) (RingHom.ker (f.pullbackFst g)) = RingHom.ker g := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    rintro ⟨⟨_, _⟩, h⟩
    simp at h ⊢; grind
  · intro s hs
    rw [RingHom.mem_ker] at hs
    exact Ideal.mem_map_of_mem (f.pullbackSnd g) (x := ⟨(0, s), by simpa using hs.symm⟩)
      (I := RingHom.ker (f.pullbackFst g)) (by simp)

theorem isLocalRing_pullback [IsLocalRing R] (f : R →+* T) (g : S →+* T) (hg : IsLocalHom g) :
    IsLocalRing (RingHom.pullback (f : R →+* T) (g : S →+* T)) where
  isUnit_or_isUnit_of_add_one {a b} h := by
    rcases a with ⟨⟨u, v⟩, huv⟩; rcases b with ⟨⟨s, t⟩, hst⟩
    simp only [AddMemClass.mk_add_mk, Prod.mk_add_mk, ← Subtype.val_inj, OneMemClass.coe_one,
      Prod.mk_eq_one] at h
    simp only [RingHom.mem_eqLocus, RingHom.coe_comp, RingHom.coe_fst, Function.comp_apply,
      RingHom.coe_snd] at huv hst
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one h.left with hu | hs
    · have : IsUnit (g v) := by rw [← huv]; exact IsUnit.map f hu
      apply IsLocalHom.map_nonunit at this
      left; simpa [isUnit_pullback_mk_iff] using ⟨hu, this⟩
    have : IsUnit (g t) := by rw [← hst]; exact IsUnit.map f hs
    apply IsLocalHom.map_nonunit at this
    right; simpa [isUnit_pullback_mk_iff] using ⟨hs, this⟩

end pullback

end RingHom

namespace AlgHom

variable {R A B C : Type*} [CommSemiring R]

section Semiring

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

/-- The subalgebra of pairs `(a, b) : A × B` such that `f a = g b`, i.e.,
  the pullback of f and g as a subalgebra of A × B. -/
abbrev pullback (f : A →ₐ[R] C) (g : B →ₐ[R] C) : Subalgebra R (A × B) :=
  equalizer (f.comp (fst R A B)) (g.comp (snd R A B))

/-- The first projection from the pullback of `f` and `g` to `A`. -/
abbrev pullbackFst (f : A →ₐ[R] C) (g : B →ₐ[R] C) : pullback f g →ₐ[R] A :=
  (fst R A B).comp (pullback f g).val

/-- The second projection from the pullback of `f` and `g` to `B`. -/
abbrev pullbackSnd (f : A →ₐ[R] C) (g : B →ₐ[R] C) : pullback f g →ₐ[R] B :=
  (snd R A B).comp (pullback f g).val

theorem pullback_comm_sq (f : A →ₐ[R] C) (g : B →ₐ[R] C) :
    f.comp (pullbackFst f g) = g.comp (pullbackSnd f g) := ext fun x ↦ x.prop

end Semiring

section Ring

variable [Ring A] [Algebra R A] [Ring B] [Algebra R B] [Semiring C] [Algebra R C]

theorem isUnit_pullback_mk_iff (f : A →ₐ[R] C) (g : B →ₐ[R] C) {a : A × B}
    (a_in : a ∈ f.pullback g) : IsUnit (⟨a, a_in⟩ : f.pullback g) ↔ IsUnit a.1 ∧ IsUnit a.2 :=
  RingHom.isUnit_pullback_mk_iff (f : A →+* C) (g : B →+* C) a_in

theorem surjective_pullbackFst_of_surjective (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (h : Function.Surjective g) : Function.Surjective (pullbackFst f g) :=
  RingHom.surjective_pullbackFst_of_surjective (f : A →+* C) (g : B →+* C) h

theorem surjective_pullbackSnd_of_surjective (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (h : Function.Surjective f) : Function.Surjective (pullbackSnd f g) :=
  RingHom.surjective_pullbackSnd_of_surjective (f : A →+* C) (g : B →+* C) h

end Ring

end AlgHom

-------------------------------------------------------------------------------

lemma IsLocalRing.isLocalHom_of_isIntegral (R k : Type*) [CommRing R] [IsLocalRing R] [Field k]
    [Algebra R k] [Algebra.IsIntegral R k] : IsLocalHom (algebraMap R k) := by
  apply ((local_hom_TFAE (algebraMap R k)).out 0 4).mpr
  rw [maximalIdeal_eq_bot]
  exact eq_maximalIdeal (Algebra.ker_algebraMap_isMaximal_of_isIntegral R k)

-------------------------------------------------------------------------------

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

---------------------------------------------------------------------------------

noncomputable section

namespace Algebra

open Function KaehlerDifferential

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

namespace Extension

instance {P P' : Extension R S} : FunLike (P.Hom P') P.Ring P'.Ring where
  coe f := f.toRingHom
  coe_injective' _ _ h := Extension.Hom.ext (DFunLike.coe_fn_eq.mp h)

instance [IsLocalRing S] : IsLocalRing (Extension.self R S).Ring :=
  inferInstanceAs <| IsLocalRing S

instance {P : Extension R S} : Unique (P.Hom (Extension.self R S)) where
  default := ⟨algebraMap P.Ring S, fun r ↦ (IsScalarTower.algebraMap_apply R P.Ring S r).symm,
    fun _ ↦ rfl⟩
  uniq f := by ext x; exact f.algebraMap_toRingHom x

@[simp]
lemma Hom.ofAlgHom_toAlgHom {P P' : Extension R S} (f : P.Hom P') :
    ofAlgHom f.toAlgHom (by ext; simp) = f := rfl

lemma Cotangent.map_surjective_of_comap_eq {P P' : Extension R S} (f : P.Hom P')
    (h : Surjective f.toRingHom)
    (eq : P'.ker.comap f.toRingHom = RingHom.ker f.toRingHom ⊔ P.ker) :
    Surjective (Cotangent.map f) := fun x ↦ by
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  obtain ⟨y, y_in, hy⟩ := Ideal.exists_of_comap_eq_ker_sup _ h eq x.prop
  exact ⟨Cotangent.mk ⟨y, y_in⟩, by simp [hy]⟩

lemma Cotangent.map_ker_of_surjective {P P' : Extension R S} (f : P.Hom P')
    (h : Surjective f.toRingHom)
    (eq : P'.ker.comap f.toRingHom = RingHom.ker f.toRingHom ⊔ P.ker) :
    (Cotangent.map f).ker.restrictScalars P.Ring =
      (Submodule.comap P.ker.subtype (RingHom.ker f.toRingHom ⊓ P.ker)).map Cotangent.mk := by
  have eq_map := Ideal.eq_map_of_comap_eq_ker_sup _ h eq
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
    simp only [Submodule.restrictScalars_mem, LinearMap.mem_ker, map_mk, Hom.toAlgHom_apply,
      mk_eq_zero_iff] at hx
    rw [eq_map, ← Ideal.map_pow, ← Ideal.mem_comap, Ideal.comap_map_of_surjective' _ h,
      Submodule.mem_sup] at hx
    rcases hx with ⟨y, y_in, z, z_in, hyz⟩
    suffices ∃ a, a ∈ RingHom.ker f.toRingHom ∧ a ∈ P.ker ∧ a - x ∈ P.ker ^ 2 by
      simpa [mk_eq_mk_iff_sub_mem]
    refine ⟨z, z_in, ?_, by simpa [← hyz]⟩
    rw [← eq_sub_iff_add_eq'] at hyz
    exact hyz ▸ Ideal.sub_mem _ x.prop (Ideal.pow_le_self (show 2 ≠ 0 by lia) y_in)
  · obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
    obtain ⟨y, y_in, y_in', hy⟩ : ∃ a ∈ RingHom.ker f.toRingHom, a ∈ P.ker ∧
      a - x ∈ P.ker ^ 2 := by simpa [mk_eq_mk_iff_sub_mem] using hx
    suffices f.toRingHom x ∈ P'.ker ^ 2 by simpa [mk_eq_zero_iff]
    rw [eq_map, ← Ideal.map_pow, ← Ideal.mem_comap, Ideal.comap_map_of_surjective' _ h,
      Submodule.mem_sup]
    exact ⟨x - y, by rwa [← Submodule.neg_mem_iff, neg_sub], y, y_in, by ring⟩

end Extension

lemma Extension.h1Cotangentι_surjective_of_subsingleton {P : Extension R S}
    [Subsingleton Ω[P.Ring⁄R]] : Surjective P.h1Cotangentι := by
  rw [← LinearMap.range_eq_top, ← P.exact_hCotangentι_cotangentComplex.linearMap_ker_eq,
    LinearMap.ker_eq_top]
  exact Subsingleton.eq_zero P.cotangentComplex

open Algebra.Extension

/-- The canonical linear equivalence between the first homology of
the naive cotangent complex `H_1(L_{S/R})` and the cotangent space of
the kernel of a surjective algebra map `R → S`. -/
def h1CotangentEquivOfSurjective (h : Surjective (algebraMap R S)) :
    H1Cotangent R S ≃ₗ[R] (RingHom.ker (algebraMap R S)).Cotangent :=
  let P := Generators.ofSurjectiveAlgebraMap.{0} h
  let E := ofSurjective (Algebra.ofId R S) h
  have : Subsingleton Ω[E.Ring⁄R] := subsingleton_of_surjective R R fun _ ↦ by simp
  let aux : P.toExtension.Hom E := .ofAlgHom (MvPolynomial.isEmptyAlgEquiv R PEmpty).toAlgHom (by
    change (IsScalarTower.toAlgHom R R S).comp (MvPolynomial.isEmptyAlgEquiv R PEmpty.{1}).toAlgHom
      = _; ext i; exact i.elim)
  let e : P.toExtension.H1Cotangent ≃ₗ[S] E.H1Cotangent :=
    Extension.H1Cotangent.equiv aux (.ofAlgHom (Algebra.ofId R P.toExtension.Ring) (by ext))
  let f := LinearEquiv.ofBijective E.h1Cotangentι
    ⟨E.h1Cotangentι_injective, h1Cotangentι_surjective_of_subsingleton⟩
  ((Generators.equivH1Cotangent P).symm ≪≫ₗ e ≪≫ₗ f).restrictScalars R ≪≫ₗ
    E.cotangentEquivCotangentKer

lemma val_h1CotangentEquivOfSurjective_symm_toCotangent
    (h : Surjective (algebraMap R S)) (x : RingHom.ker (algebraMap R S)) :
      ((h1CotangentEquivOfSurjective h).symm ((RingHom.ker (algebraMap R S)).toCotangent x)).1 =
        Cotangent.mk ⟨algebraMap R (MvPolynomial S R) x.val, by
          change MvPolynomial.aeval _ _ = 0; simp [← RingHom.mem_ker]⟩ := by
  let E := ofSurjective (Algebra.ofId R S) h
  have : Subsingleton Ω[E.Ring⁄R] := subsingleton_of_surjective _ _ fun _ ↦ ⟨_, rfl⟩
  dsimp [h1CotangentEquivOfSurjective]
  let f := LinearEquiv.ofBijective E.h1Cotangentι
    ⟨E.h1Cotangentι_injective, h1Cotangentι_surjective_of_subsingleton⟩
  change Cotangent.map _ (Cotangent.map _ (f.symm (E.cotangentEquivCotangentKer.symm
    ((RingHom.ker (algebraMap R S)).toCotangent x))).val) = _
  have : f.symm (E.cotangentEquivCotangentKer.symm ((RingHom.ker (algebraMap R S)).toCotangent x))
    = ⟨Cotangent.mk x, Subsingleton.elim ..⟩ := f.symm_apply_eq.mpr rfl
  rw [this, Subtype.coe_mk, Cotangent.map_mk, Cotangent.map_mk]
  congr 1; ext
  exact AlgHom.commutes ..

end Algebra

end

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

/-!
# The Category of Local extension over a Fixed Residue Field

This file adds definitions and basic lemmas about the category of local extensions
with base algebra `Λ` over a fixed residue field `k`, which serves as
an ambient environment for formal deformation theory.

## Main Definitions

* `LocExtCat Λ k` : The type of objects in the category of local extensions with base algebra `Λ`
  over a fixed residue field `k`.

* `LocExtCat.Hom` : The type of morphisms between objects in `LocAlgCat Λ k`.
  A morphism `f : A ⟶ B` is an extension homomorphism between the underlying extensions.

* `LocExtCat.isoMk`, `LocExtCat.ofIso` : Canonical translations between algebra
  equivalences and categorical isomorphisms.

-/

noncomputable section

open IsLocalRing CategoryTheory Function Algebra

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The category of local extensions of a fixed residue field `k`. -/
structure LocExtCat (Λ k : Type u) [CommRing Λ] [Field k] [Algebra Λ k] extends
    Extension.{u} Λ k where
  of (Λ k) ::
  [localRing : IsLocalRing Ring]

namespace LocExtCat

variable {A B C : LocExtCat Λ k} {X Y Z : Extension.{u} Λ k}
variable [IsLocalRing X.Ring] [IsLocalRing Y.Ring] [IsLocalRing Z.Ring]

attribute [instance] localRing

initialize_simps_projections LocExtCat (-localRing)

instance coeExtension : CoeOut (LocExtCat Λ k) (Extension.{u} Λ k) where
  coe A := A.toExtension

instance coeRing : CoeSort (LocExtCat Λ k) (Type u) where
  coe A := A.Ring

variable (X) in
lemma coe_of : (of Λ k X : Type u) = X.Ring := rfl

@[simp]
lemma ker_extension : A.ker = maximalIdeal A :=
  eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ A.algebraMap_surjective)

/-- The canonical residue map from the underlying ring of an object `A` to `k`.
This is a prefered way to apply residue maps in `LocExtCat`. -/
def residue (A : LocExtCat Λ k) : A →ₐ[Λ] k :=
  IsScalarTower.toAlgHom Λ A k

lemma residue_toRingHom : A.residue = algebraMap A k := rfl

lemma residue_apply {a : A} : A.residue a = algebraMap A k a := rfl

@[simp]
lemma ker_residue : RingHom.ker (residue A) = maximalIdeal A := ker_extension

lemma residue_surjective : Surjective (residue A) := A.algebraMap_surjective

lemma residue_eq_zero_iff {x : A} : residue A x = 0 ↔ x ∈ maximalIdeal A := by
  rw [← RingHom.mem_ker, ker_residue]

/-- The canonical equivalence between the residue field of
the underlying local ring of an object and `k`. -/
def residueEquiv (A : LocExtCat Λ k) : ResidueField A ≃ₐ[Λ] k where
  __ := (Ideal.quotEquivOfEq (ker_residue (A := A)).symm).trans
    (RingHom.quotientKerEquivOfSurjective A.residue_surjective)
  commutes' r := (IsScalarTower.algebraMap_apply Λ A k r).symm

@[simp]
lemma residueEquiv_residue_apply {x : A} :
    A.residueEquiv (IsLocalRing.residue A x) = A.residue x := rfl

/-- The type of morphisms in `LocExtCat` is the same as morphisms of the underlying extensions. -/
@[ext]
structure Hom (A B : LocExtCat Λ k) : Type u where
  hom' : A.toExtension.Hom B.toExtension

instance : Category (LocExtCat Λ k) where
  Hom A B := Hom A B
  id A := ⟨Extension.Hom.id A.toExtension⟩
  comp {A B C} f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory (LocExtCat Λ k) (fun A B ↦ A.toExtension.Hom B.toExtension) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `LocExtCat` back into an extension homomorphism. -/
abbrev Hom.hom (f : Hom A B) := ConcreteCategory.hom (C := LocExtCat Λ k) f

/-- Typecheck an extension homomorphism as a morphism in `LocExtCat`. -/
abbrev ofHom (f : X.Hom Y) : of Λ k X ⟶ of Λ k Y := ConcreteCategory.ofHom (C := LocExtCat Λ k) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (A B : LocExtCat Λ k) (f : Hom A B) := f.hom

initialize_simps_projections Hom (hom' → hom)

/-- The underlying algebra homomorphism of a morphism in `LocExtCat`. -/
abbrev Hom.toAlgHom (f : A ⟶ B) : A.Ring →ₐ[Λ] B.Ring := f.hom.toAlgHom

@[simp]
lemma Hom.residue_comp (f : A ⟶ B) : B.residue.comp f.toAlgHom = A.residue := by
  ext x
  exact f.hom.algebraMap_toRingHom x

lemma Hom.comap_maximalIdeal_eq (f : A ⟶ B) :
    (maximalIdeal B).comap f.toAlgHom = maximalIdeal A := by
  rw [← ker_residue, RingHom.ker, Ideal.comap_comapₐ, residue_comp, ← RingHom.ker, ker_residue]

lemma Hom.isLocalHom_toAlgHom (f : A ⟶ B) : IsLocalHom f.toAlgHom := by
  have := (((local_hom_TFAE (f.toAlgHom : A →+* B)).out 0 4).mpr (by
    rw [Ideal.comap_coe, f.comap_maximalIdeal_eq]))
  exact ⟨this.map_nonunit⟩

lemma Hom.map_maximalIdeal_le (f : A ⟶ B) :
    (maximalIdeal A).map f.toAlgHom ≤ maximalIdeal B := by
  have := (local_hom_TFAE f.toAlgHom.toRingHom).out 4 2
  rw [AlgHom.toRingHom_eq_coe, Ideal.comap_coe, Ideal.map_coe] at this
  rw [← this, f.comap_maximalIdeal_eq]

/-- The relative algebra structure on `B` canonically induced by a morphism `f : A ⟶ B`. -/
abbrev Hom.relativeAlgebra (f : A ⟶ B) : Algebra A B :=
  fast_instance% f.hom.toRingHom.toAlgebra

lemma Hom.isScalarTower_relativeAlgebra (f : A ⟶ B) :
    @IsScalarTower Λ A B _ f.relativeAlgebra.toSMul _ := .of_algHom f.toAlgHom

lemma Hom.isScalarTower'_relativeAlgebra (f : A ⟶ B) :
    @IsScalarTower A B k f.relativeAlgebra.toSMul _ _ :=
  letI := f.relativeAlgebra
  .of_algebraMap_eq (fun a ↦ (DFunLike.congr_fun f.residue_comp a).symm)

@[simp]
lemma ofHom_hom (f : A ⟶ B) : ofHom f.hom = f := rfl

@[simp]
lemma ofHom_comp (f : X.Hom Y) (g : Y.Hom Z) : ofHom (g.comp f) = ofHom f ≫ ofHom g:= rfl

@[simp]
lemma ofHom_id : ofHom (Extension.Hom.id X) = 𝟙 (of Λ k X) := rfl

@[ext]
lemma hom_ext {f g : A ⟶ B} (h : f.hom = g.hom) : f = g := Hom.ext h

lemma comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a) := by simp

@[simp]
lemma toAlghom_id : (𝟙 A : A ⟶ A).toAlgHom = AlgHom.id Λ A := rfl

@[simp]
lemma toAlgHom_comp (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).toAlgHom = g.toAlgHom.comp f.toAlgHom :=
  rfl

@[ext]
lemma toAlgHom_ext {f g : A ⟶ B} (h : f.toAlgHom = g.toAlgHom) : f = g := by
  ext x
  exact DFunLike.congr_fun h x

lemma ofHom_toAlgHom_apply (f : X.Hom Y) (x : X.Ring) : (ofHom f).toAlgHom x = f x := rfl

lemma inv_hom_apply (e : A ≅ B) (x : A) : e.inv (e.hom x) = x := by simp
lemma hom_inv_apply (e : A ≅ B) (x : B) : e.hom (e.inv x) = x := by simp

instance : Unique (A ⟶ (of Λ k (Extension.self Λ k))) where
  default := ofHom default
  uniq f := by rw [← ofHom_hom f, Unique.eq_default (Hom.hom f)]

variable (Λ k) in
/-- The terminal object in `LocExtCat` is the trivial extension of `k`. -/
def isTerminalOfSelf : Limits.IsTerminal (of Λ k (Extension.self Λ k)) := .ofUnique _

/-- Build an isomorphism in the category `LocExtCat` from a bijective extension homomorphism
between the underlying extensions. -/
@[simps]
def isoMk {X Y : Extension.{u} Λ k} {_ : IsLocalRing X.Ring} {_ : IsLocalRing Y.Ring}
    (e : X.Hom Y) (he : Bijective e.toAlgHom) : of Λ k X ≅ of Λ k Y where
  hom := ofHom e
  inv := ofHom <| .ofAlgHom (AlgEquiv.ofBijective e.toAlgHom he).symm (AlgHom.ext fun r ↦ by
    obtain ⟨r, rfl⟩ := he.surjective r
    nth_rw 1 [AlgHom.comp_apply, AlgEquiv.coe_algHom, ← AlgEquiv.coe_ofBijective e.toAlgHom he,
      AlgEquiv.symm_apply_apply]
    simp)
  inv_hom_id := by
    ext r
    suffices e.toAlgHom ((AlgEquiv.ofBijective e.toAlgHom he).symm r) = r by simpa
    rw [← AlgEquiv.coe_ofBijective e.toAlgHom he, AlgEquiv.apply_symm_apply]
  hom_inv_id := by
    ext r
    suffices (AlgEquiv.ofBijective e.toAlgHom he).symm (e.toAlgHom r) = r by simpa
    rw [← AlgEquiv.coe_ofBijective e.toAlgHom he, AlgEquiv.symm_apply_apply]

/-- Build an `AlgEquiv` from an isomorphism in the category `LocAlgCat Λ k`. -/
@[simps]
def ofIso (i : A ≅ B) : A ≃ₐ[Λ] B where
  __ := i.hom.toAlgHom
  toFun := i.hom.toAlgHom
  invFun := i.inv.toAlgHom
  left_inv _ := inv_hom_apply ..
  right_inv _ := hom_inv_apply ..

@[simp]
lemma residue_comp_coe_ofIso (i : A ≅ B) : B.residue.comp (ofIso i) = A.residue :=
  i.hom.residue_comp

@[simp]
lemma residue_comp_coe_ifIso_symm (i : A ≅ B) : A.residue.comp (ofIso i).symm = B.residue :=
  i.inv.residue_comp

----------------------------------------------------------------------------------------------

instance (f : A ⟶ B) : Nontrivial (A ⧸ RingHom.ker f.toAlgHom) :=
  Ideal.Quotient.nontrivial_iff.mpr <| RingHom.ker_ne_top f.toAlgHom

variable (A) in
lemma isLocalHom_algebraMap [IsLocalRing Λ] [Algebra.IsIntegral Λ k] :
    IsLocalHom (algebraMap Λ A) := by
  have : IsLocalHom (algebraMap Λ k) := isLocalHom_of_isIntegral Λ k
  rw [IsScalarTower.algebraMap_eq Λ A] at this
  exact isLocalHom_of_comp (algebraMap Λ A) (algebraMap A k)

variable (A) in
lemma comap_algebraMap_maximalIdeal [IsLocalRing Λ] [Algebra.IsIntegral Λ k] :
    (maximalIdeal A).comap (algebraMap Λ A) = maximalIdeal Λ := by
  have : IsLocalHom (algebraMap Λ k) := isLocalHom_of_isIntegral Λ k
  have := ((local_hom_TFAE (algebraMap Λ k)).out 0 4).mp ‹_›
  rw [eq_comm, ← this, IsScalarTower.algebraMap_eq Λ A, ← Ideal.comap_comap,
    eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ A.algebraMap_surjective)]

instance [IsLocalRing Λ] [Algebra.IsIntegral Λ k] :
    Nontrivial (A ⧸ ((maximalIdeal Λ).map (algebraMap Λ A))) :=
  Ideal.Quotient.nontrivial_iff.mpr <| ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top <|
    ((local_hom_TFAE (algebraMap Λ A)).out 4 2).mp (comap_algebraMap_maximalIdeal A)

instance (n : ℕ) [NeZero n] : Nontrivial (A ⧸ maximalIdeal A ^ n) := by
  rw [Ideal.Quotient.nontrivial_iff, Ideal.ne_top_iff_exists_maximal]
  exact ⟨maximalIdeal A, maximalIdeal.isMaximal A, Ideal.pow_le_self (NeZero.ne n)⟩

/-- Up to a perturbation by an element in the maximal ideal of `A`, any element in `A`
can be mapped via a surjective morphism `f` to an element in the image of `g`. -/
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

section ofQuot

variable {I : Ideal A}

/-- The quotient of an object `A` in `LocExtCat` by a proper ideal `I`. -/
def ofQuot (A : LocExtCat Λ k) (I : Ideal A) [Nontrivial (A ⧸ I)] : LocExtCat Λ k :=
  haveI hI : ∀ a ∈ I, A.residue a = 0 := by
    simp_rw [← RingHom.mem_ker, ker_residue]
    exact le_maximalIdeal (Ideal.Quotient.nontrivial_iff.mp ‹_›)
  letI P : Extension Λ k := (.ofSurjective (Ideal.Quotient.liftₐ I A.residue hI)
    (Ideal.Quotient.lift_surjective_of_surjective I hI A.residue_surjective))
  haveI : Nontrivial P.Ring := ‹_›
  haveI : IsLocalRing P.Ring := .of_surjective' _ Ideal.Quotient.mk_surjective
  of Λ k P

@[simp]
lemma residue_ofQuot_mk_apply [Nontrivial (A ⧸ I)] (a : A) :
    (A.ofQuot I).residue (Ideal.Quotient.mk I a) = A.residue a := rfl

/-- Upgrades the canonical quotient map `A → A ⧸ I` to a morphism in `LocExtCat`. -/
def toOfQuot (A : LocExtCat Λ k) (I : Ideal A) [Nontrivial (A ⧸ I)] : A ⟶ A.ofQuot I :=
  haveI hI : ∀ a ∈ I, A.residue a = 0 := by
    simp_rw [← RingHom.mem_ker, ker_residue]
    exact le_maximalIdeal (Ideal.Quotient.nontrivial_iff.mp ‹_›)
  letI P : Extension Λ k := (.ofSurjective (Ideal.Quotient.liftₐ I A.residue hI)
    (Ideal.Quotient.lift_surjective_of_surjective I hI A.residue_surjective))
  haveI : Nontrivial P.Ring := ‹_›
  haveI : IsLocalRing P.Ring := .of_surjective' _ Ideal.Quotient.mk_surjective
  ofHom <| .ofAlgHom (Ideal.Quotient.mkₐ Λ I)
    (by ext; simpa [residue] using residue_ofQuot_mk_apply ..)

@[simp]
lemma ker_toRingHom_toOfQuot [Nontrivial (A ⧸ I)] :
    RingHom.ker (A.toOfQuot I).hom.toRingHom = I := Ideal.mk_ker

@[simp]
lemma ker_toAlgHom_toOfQuot [Nontrivial (A ⧸ I)] : RingHom.ker (A.toOfQuot I).toAlgHom = I :=
  Ideal.mk_ker

lemma toalghom_toOfQuot_surjective (I) [Nontrivial (A ⧸ I)] : Surjective (A.toOfQuot I).toAlgHom :=
  Ideal.Quotient.mk_surjective

theorem map_toAlgHom_toOfQuot_maximalIdeal_eq [Nontrivial (A ⧸ I)] :
    (maximalIdeal A).map (A.toOfQuot I).toAlgHom = maximalIdeal (A.ofQuot I) :=
  map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective

/-- The morphism between `A.ofQuot I` and `B.ofQuot J` induced by a morphism `f : A ⟶ B`. -/
def mapOfQuot (f : A ⟶ B) {J : Ideal B} [Nontrivial (A ⧸ I)] [Nontrivial (B ⧸ J)]
    (hf : I ≤ J.comap f.toAlgHom) : A.ofQuot I ⟶ B.ofQuot J :=
  haveI hI : ∀ a ∈ I, A.residue a = 0 := by
    simp_rw [← RingHom.mem_ker, ker_residue]
    exact le_maximalIdeal (Ideal.Quotient.nontrivial_iff.mp ‹_›)
  letI P : Extension Λ k := (.ofSurjective (Ideal.Quotient.liftₐ I A.residue hI)
    (Ideal.Quotient.lift_surjective_of_surjective I hI A.residue_surjective))
  haveI : Nontrivial P.Ring := ‹_›
  haveI : IsLocalRing P.Ring := .of_surjective' _ Ideal.Quotient.mk_surjective
  haveI hJ : ∀ a ∈ J, B.residue a = 0 := by
    simp_rw [← RingHom.mem_ker, ker_residue]
    exact le_maximalIdeal (Ideal.Quotient.nontrivial_iff.mp ‹_›)
  letI Q : Extension Λ k := (.ofSurjective (Ideal.Quotient.liftₐ J B.residue hJ)
    (Ideal.Quotient.lift_surjective_of_surjective J hJ B.residue_surjective))
  haveI : Nontrivial Q.Ring := ‹_›
  haveI : IsLocalRing Q.Ring := .of_surjective' _ Ideal.Quotient.mk_surjective
  ofHom (.ofAlgHom (Ideal.quotientMapₐ J f.toAlgHom hf) (AlgHom.ext fun x ↦ by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact DFunLike.congr_fun f.residue_comp x))

@[simp]
theorem toOfQuot_comp_mapOfQuot (f : A ⟶ B) {J : Ideal B} [Nontrivial (A ⧸ I)]
    [Nontrivial (B ⧸ J)] (hf : I ≤ J.comap f.toAlgHom) :
    A.toOfQuot I ≫ mapOfQuot f hf = f ≫ B.toOfQuot J := rfl

/-- Lifts a morphism `f : A ⟶ B` to a morphism out of `A.ofQuot I`,
given that `I` is contained in the kernel of `f`. -/
def liftToOfQuot (I : Ideal A) [Nontrivial (A ⧸ I)] (f : A ⟶ B)
    (hI : ∀ a ∈ I, f.toAlgHom a = 0) : A.ofQuot I ⟶ B :=
  haveI hI' : ∀ a ∈ I, A.residue a = 0 := by
    simp_rw [← RingHom.mem_ker, ker_residue]
    exact le_maximalIdeal (Ideal.Quotient.nontrivial_iff.mp ‹_›)
  letI P : Extension Λ k := (.ofSurjective (Ideal.Quotient.liftₐ I A.residue hI')
    (Ideal.Quotient.lift_surjective_of_surjective I hI' A.residue_surjective))
  haveI : Nontrivial P.Ring := ‹_›
  haveI : IsLocalRing P.Ring := .of_surjective' _ Ideal.Quotient.mk_surjective
  ofHom (.ofAlgHom (Ideal.Quotient.liftₐ I f.toAlgHom hI) (by
    change B.residue.comp _ = Ideal.Quotient.liftₐ I A.residue hI'
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective Λ I x
    exact DFunLike.congr_fun f.residue_comp x))

@[simp]
lemma toOfQuot_comp_liftToOfQuot (I : Ideal A) [Nontrivial (A ⧸ I)] (f : A ⟶ B)
    (hI : ∀ a ∈ I, f.toAlgHom a = 0) : A.toOfQuot I ≫ liftToOfQuot I f hI = f := rfl

/-- The isomorphism between `A.ofQuot (RingHom.ker f.toAlgHom)` and the codomain `B`
when the underlying `AlgHom` of a morphism `f : A ⟶ B` is surjective. -/
def ofQuotKerIsoOfSurjective (f : A ⟶ B) (h : Surjective f.toAlgHom) :
    A.ofQuot (RingHom.ker f.toAlgHom) ≅ B :=
  isoMk (.ofAlgHom (Ideal.quotientKerAlgEquivOfSurjective h).toAlgHom (by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact DFunLike.congr_fun f.residue_comp x
    )) (Ideal.quotientKerAlgEquivOfSurjective h).bijective

@[simp]
lemma toOfQuot_comp_ofQuotKerIsoOfSurjective_hom {f : A ⟶ B} (h : Surjective f.toAlgHom) :
    A.toOfQuot (RingHom.ker f.toAlgHom) ≫ (ofQuotKerIsoOfSurjective f h).hom = f := Hom.ext rfl

/-- The quotient of a local algebra by the `n`-th power of its maximal ideal.
Geometrically, this represents an infinitesimal neighborhood of the closed point. -/
abbrev infinitesimal (n : ℕ) [NeZero n] (A : LocExtCat Λ k) : LocExtCat Λ k :=
  A.ofQuot (maximalIdeal A ^ n)

/-- The canonical quotient morphism from `A` to its infinitesimal neighborhood. -/
abbrev toInfinitesimal (n : ℕ) [NeZero n] (A : LocExtCat Λ k) :
    A ⟶ A.infinitesimal n := toOfQuot ..

/-- The morphism between infinitesimal neighborhoods induced by a morphism in `LocExtCat`. -/
abbrev mapInfinitesimal (m n : ℕ) [NeZero m] [NeZero n] (hmn : n ≤ m) (f : A ⟶ B) :
    A.infinitesimal m ⟶ B.infinitesimal n :=
  mapOfQuot f (le_trans (Ideal.pow_le_pow_right hmn) (f.comap_maximalIdeal_eq ▸
      Ideal.le_comap_pow f.toAlgHom n))

lemma toInfinitesimal_comp_map (m n : ℕ) [NeZero m] [NeZero n] (hmn : n ≤ m)
    (f : A ⟶ B) : A.toInfinitesimal m ≫ mapInfinitesimal m n hmn f =
      f ≫ B.toInfinitesimal n := by simp

/-- The special fiber of `A` over `Λ` when `Λ` is a local ring, defined as the quotient by
the extended maximal ideal of `Λ`, viewed as an object in `LocExtCat`. -/
abbrev specialFiber [IsLocalRing Λ] [Algebra.IsIntegral Λ k] (A : LocExtCat Λ k) :
    LocExtCat Λ k := A.ofQuot ((maximalIdeal Λ).map (algebraMap Λ A))

/-- The canonical morphism from `A` to its special fiber. -/
abbrev toSpecialFiber [IsLocalRing Λ] [Algebra.IsIntegral Λ k] (A : LocExtCat Λ k) :
    A ⟶ A.specialFiber := toOfQuot ..

/-- The morphism between special fibers induced by a morphism between two objects. -/
abbrev mapSpecialFiber [IsLocalRing Λ] [Algebra.IsIntegral Λ k] (f : A ⟶ B) :
    A.specialFiber ⟶ B.specialFiber :=
  mapOfQuot f (by rw [Ideal.map_le_iff_le_comap, ← Ideal.comap_coe f.toAlgHom,
    Ideal.comap_comap, AlgHom.comp_algebraMap, ← Ideal.map_le_iff_le_comap])

@[simp]
lemma algebraMap_specialFiber_apply_eq_zero [IsLocalRing Λ] [Algebra.IsIntegral Λ k] (y : Λ)
    (h : y ∈ maximalIdeal Λ) : (algebraMap Λ A.specialFiber) y = 0 := by
  change algebraMap Λ (A ⧸ (maximalIdeal Λ).map (algebraMap Λ A)) y = 0
  rw [IsScalarTower.algebraMap_apply Λ A, Ideal.Quotient.algebraMap_eq, ← RingHom.mem_ker,
    Ideal.mk_ker]
  exact Ideal.mem_map_of_mem _ h

lemma toInfinitesimal_comp_mapInfinitesimal_toSpecialFiber [IsLocalRing Λ]
    [Algebra.IsIntegral Λ k] (n : ℕ) [NeZero n] (A : LocExtCat Λ k) :
    A.toInfinitesimal n ≫ mapInfinitesimal n n le_rfl A.toSpecialFiber =
      A.toSpecialFiber ≫ (A.specialFiber).toInfinitesimal n := by simp

end ofQuot

section ofPullback

variable {f : A ⟶ C} {g : B ⟶ C}

/-- Given morphisms `f : A ⟶ C` and `g : B ⟶ C` in `LocExtCat` where `g.toAlgHom` is surjective,
`ofPullback` is the object in `LocExtCat` obtained from the pullback of the underlying
algebra homomorphisms`. -/
def ofPullback (f : A ⟶ C) (g : B ⟶ C) (hg : Surjective g.toAlgHom) : LocExtCat Λ k :=
  letI P : Extension Λ k := .ofSurjective (A.residue.comp (f.toAlgHom.pullbackFst g.toAlgHom))
    (by simpa using Surjective.comp A.residue_surjective <|
      AlgHom.surjective_pullbackFst_of_surjective _ _ hg)
  haveI : IsLocalRing P.Ring := RingHom.isLocalRing_pullback
    f.toAlgHom.toRingHom g.toAlgHom.toRingHom ⟨hg.isLocalHom.map_nonunit⟩
  of Λ k P

/-- Upgrades the first projection map from the pullback algebra to a morphism in `LocExtCat`. -/
abbrev pullbackFst (f : A ⟶ C) (g : B ⟶ C) (hg : Surjective g.toAlgHom) :
    ofPullback f g hg ⟶ A :=
  letI P : Extension Λ k := .ofSurjective (A.residue.comp (f.toAlgHom.pullbackFst g.toAlgHom))
    (by simpa using Surjective.comp A.residue_surjective <|
        AlgHom.surjective_pullbackFst_of_surjective _ _ hg)
  haveI : IsLocalRing P.Ring := RingHom.isLocalRing_pullback
    f.toAlgHom.toRingHom g.toAlgHom.toRingHom ⟨hg.isLocalHom.map_nonunit⟩
  ofHom (.ofAlgHom (f.toAlgHom.pullbackFst g.toAlgHom) rfl)

lemma surjective_pullbackFst (f : A ⟶ C) (g : B ⟶ C) (hg : Surjective g.toAlgHom) :
    Surjective (pullbackFst f g hg).toAlgHom :=
  AlgHom.surjective_pullbackFst_of_surjective _ _ hg

lemma residue_comp_pullbackFst (f : A ⟶ C) (g : B ⟶ C) :
    A.residue.comp (f.toAlgHom.pullbackFst g.toAlgHom) =
      B.residue.comp (f.toAlgHom.pullbackSnd g.toAlgHom) := by
  ext ⟨_, h⟩
  simp only [AlgHom.mem_equalizer, AlgHom.coe_comp, Function.comp_apply, AlgHom.fst_apply,
    AlgHom.snd_apply, Subalgebra.coe_val] at h ⊢
  rw [← DFunLike.congr_fun f.residue_comp, ← DFunLike.congr_fun g.residue_comp,
    AlgHom.comp_apply, AlgHom.comp_apply, ← h]

/-- Upgrades the second projection map from the pullback algebra to a morphism in `LocExtCat`. -/
abbrev pullbackSnd (f : A ⟶ C) (g : B ⟶ C) (hg : Surjective g.toAlgHom) :
    ofPullback f g hg ⟶ B :=
  letI P : Extension Λ k := .ofSurjective (A.residue.comp (f.toAlgHom.pullbackFst g.toAlgHom))
    (by simpa using Surjective.comp A.residue_surjective <|
        AlgHom.surjective_pullbackFst_of_surjective _ _ hg)
  haveI : IsLocalRing P.Ring := RingHom.isLocalRing_pullback
    f.toAlgHom.toRingHom g.toAlgHom.toRingHom ⟨hg.isLocalHom.map_nonunit⟩
  ofHom (.ofAlgHom (f.toAlgHom.pullbackSnd g.toAlgHom) (residue_comp_pullbackFst ..).symm)

lemma pullback_comm_sq (f : A ⟶ C) (g : B ⟶ C) (hg : Surjective g.toAlgHom) :
    pullbackFst f g hg ≫ f = pullbackSnd f g hg ≫ g :=
  toAlgHom_ext <| AlgHom.pullback_comm_sq f.toAlgHom g.toAlgHom

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
theorem residue_comp_pullbackfst_surjective_of_isSeparable [IsLocalRing Λ] [Module.Finite Λ k]
    [HenselianRing A (maximalIdeal A)] [HenselianRing B (maximalIdeal B)]
    [Algebra.IsSeparable (ResidueField Λ) k] (f : A ⟶ C) (g : B ⟶ C) :
    Surjective (A.residue.comp (f.toAlgHom.pullbackFst g.toAlgHom)) := by
  obtain ⟨x, hx⟩ := Field.exists_primitive_element (ResidueField Λ) k
  let p := minpoly (ResidueField Λ) x
  obtain ⟨q, map_q, deg_q, monic_q⟩ := lifts_and_natDegree_eq_and_monic
    (show p ∈ lifts (IsLocalRing.residue Λ) by
      rw [lifts_iff_coeff_lifts]; exact fun _ ↦ IsLocalRing.residue_surjective _)
    (minpoly.monic (Algebra.IsIntegral.isIntegral x))
  obtain ⟨a', ha⟩ := A.residue_surjective x
  obtain ⟨a, a_rt, a_sub⟩ := HenselianRing.is_henselian (R := A) (I := maximalIdeal A)
    (q.map (algebraMap Λ A)) (Monic.map _ monic_q) a' (by
      simpa using LocExtCat.not_isUnit_aeval_of_aeval_eq_zero x (minpoly.aeval (ResidueField Λ) x)
        map_q ha)
    (by change IsUnit (IsLocalRing.residue A _); simpa using
      LocExtCat.isUnit_aeval_derivative_of_isSeparable (Algebra.IsSeparable.isSeparable
        (ResidueField Λ) x) map_q ha)
  replace ha : A.residue a = x := by
    rw [← sub_add_cancel a a', map_add, ha, LocExtCat.residue_eq_zero_iff.mpr a_sub, zero_add]
  obtain ⟨b', hb⟩ := B.residue_surjective x
  obtain ⟨b, b_rt, b_sub⟩ := HenselianRing.is_henselian (R := B) (I := maximalIdeal B)
    (q.map (algebraMap Λ B)) (Monic.map _ monic_q) b' (by
      simpa using LocExtCat.not_isUnit_aeval_of_aeval_eq_zero x (minpoly.aeval (ResidueField Λ) x)
        map_q hb)
    (by change IsUnit (IsLocalRing.residue B _); simpa using
      LocExtCat.isUnit_aeval_derivative_of_isSeparable (Algebra.IsSeparable.isSeparable
        (ResidueField Λ) x) map_q hb)
  replace hb : B.residue b = x := by
    rw [← sub_add_cancel b b', map_add, hb, LocExtCat.residue_eq_zero_iff.mpr b_sub, zero_add]
  clear a' a_sub b' b_sub
  have hab : f.toAlgHom a = g.toAlgHom b := by
    simp only [IsRoot.def, eval_map_algebraMap, aeval_def] at a_rt b_rt
    apply DFunLike.congr_arg f.toAlgHom at a_rt
    apply DFunLike.congr_arg g.toAlgHom at b_rt
    rw [algHom_eval₂_algebraMap, map_zero, eval₂_eq_eval_map] at a_rt b_rt
    refine eq_of_eval_eq_zero_of_not_isUnit_sub a_rt b_rt ?_ ?_
    · rw [← notMem_maximalIdeal, not_not, ← LocExtCat.residue_eq_zero_iff, map_sub, sub_eq_zero,
        ← AlgHom.comp_apply, ← AlgHom.comp_apply, f.residue_comp, g.residue_comp, ha, hb]
    · rw [derivative_map, eval_map_algebraMap]
      exact LocExtCat.isUnit_aeval_derivative_of_isSeparable
        (Algebra.IsSeparable.isSeparable (ResidueField Λ) x) map_q (by
          rwa [← AlgHom.comp_apply, f.residue_comp])
  apply Algebra.adjoin_eq_top_of_primitive_element (Algebra.IsAlgebraic.isAlgebraic x) at hx
  simp only [SetLike.ext_iff, Algebra.mem_top, iff_true] at hx
  intro y
  suffices ∃ a, (∃ x, f.toAlgHom a = g.toAlgHom x) ∧ A.residue a = y by simpa
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
  have : IsLocalHom (algebraMap Λ A) := isLocalHom_algebraMap A
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

instance isArtinianRing_pullback [IsArtinianRing A] [IsArtinianRing B] (f : A ⟶ C)
    (g : B ⟶ C) : IsArtinianRing (f.toAlgHom.pullback g.toAlgHom) := by
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
  simp_rw [ofPullback, Extension.ofSurjective_Ring]
  exact isArtinianRing_pullback f g

end ArtinianRing

---------------------------------------------------------------------------------

-- From Wenrong Zou

noncomputable section ofAdicCompletion

/-- The object in `LocExtCat` constructed from the `m`-adic completion of the underlying ring of
an `Algebra.Extension Λ k`, where `m` is the finitely generated kernel of the algebra map to `k`. -/
def ofAdicCompletion (X : Extension.{u} Λ k) {m : Ideal X.Ring}
    (hm : m = RingHom.ker (algebraMap X.Ring k)) (fg : m.FG) : LocExtCat Λ k :=
  letI P : Extension.{u} Λ k := .ofSurjective
    ((Ideal.Quotient.liftₐ m (IsScalarTower.toAlgHom Λ X.Ring k)
      (by simp [← RingHom.mem_ker, hm])).comp ((AdicCompletion.evalOneₐ m).restrictScalars Λ))
    (by simpa using Surjective.comp (Ideal.Quotient.lift_surjective_of_surjective m (by simp [hm])
        X.algebraMap_surjective) (AdicCompletion.evalOneₐ_surjective m))
  haveI : m.IsMaximal := hm ▸ RingHom.ker_isMaximal_of_surjective _ X.algebraMap_surjective
  haveI : IsLocalRing P.Ring := @isLocalRing_of_isAdicComplete_maximal _ _
    (m.map (algebraMap X.Ring (AdicCompletion m X.Ring)))
    (AdicCompletion.isMaximal_map_of_le m m le_rfl fg)
    (AdicCompletion.isAdicComplete_self m fg)
  of Λ k P

end ofAdicCompletion
/-
section ofTensor

open scoped TensorProduct

abbrev tensorResidueAlgebra (f : A ⟶ B) (g : A ⟶ C) :
    letI := f.relativeAlgebra
    letI := g.relativeAlgebra
    Algebra (B ⊗[A] C) k :=
  letI := f.relativeAlgebra
  letI := g.relativeAlgebra
  fast_instance% (Algebra.TensorProduct.lift
    (.mk (algebraMap B k) (AlgHom.congr_fun f.residue_comp))
      (.mk (algebraMap C k) (AlgHom.congr_fun g.residue_comp))
        (fun _ _ ↦ mul_comm _ _)).toRingHom.toAlgebra

lemma IsScalarTower_tensorResidueAlgebra (f : A ⟶ B) (g : A ⟶ C) :
    letI := f.relativeAlgebra
    letI := g.relativeAlgebra
    @IsScalarTower Λ (B ⊗[A] C) k _ (tensorResidueAlgebra f g).toSMul _ :=
  letI := f.relativeAlgebra
  letI := g.relativeAlgebra
  .of_algebraMap_eq (R := Λ) (S := B ⊗[A] C) fun r ↦ by simp [RingHom.algebraMap_toAlgebra]

lemma surjective_algebraMap_tensorResidueAlgebra (f : A ⟶ B) (g : A ⟶ C) :
    letI := f.relativeAlgebra
    letI := g.relativeAlgebra
    Surjective (algebraMap (B ⊗[A] C) k) := fun y ↦ by
  letI := f.relativeAlgebra
  letI := g.relativeAlgebra
  obtain ⟨b, rfl⟩ := B.isSurjective y
  exact ⟨Algebra.TensorProduct.includeLeft (S := A) b, by simp [RingHom.algebraMap_toAlgebra]⟩

end ofTensor-/

---------------------------------------------------------------------------------

noncomputable section Cotangent

open Algebra.Extension KaehlerDifferential TensorProduct

section mapCotangent

/-- A morphism in `LocExtCat` induces a map between cotangent spaces of
the underlying extensions. -/
abbrev mapCotangent (f : A ⟶ B) : A.Cotangent →ₗ[k] B.Cotangent :=
  Cotangent.map f.hom

@[simp]
lemma mapCotangent_id : mapCotangent (𝟙 A) = LinearMap.id := Cotangent.map_id

lemma mapCotangent_comp (f : A ⟶ B) (g : B ⟶ C) :
    mapCotangent (f ≫ g) = mapCotangent g ∘ₗ mapCotangent f :=
  Cotangent.map_comp C.toExtension f.hom g.hom

/-- The `k`-linear equivalence between cotangent spaces induced by
an isomorphism in `LocAlgCat`. -/
def equivCotangent (e : A ≅ B) : A.Cotangent ≃ₗ[k] B.Cotangent where
  __ := mapCotangent e.hom
  invFun := mapCotangent e.inv
  left_inv _ := by simp [← LinearMap.comp_apply, ← mapCotangent_comp]
  right_inv _ := by simp [← LinearMap.comp_apply, ← mapCotangent_comp]

@[simp]
lemma equivCotangent_apply (e : A ≅ B) (x : A.Cotangent) :
    equivCotangent e x = mapCotangent e.hom x := rfl

@[simp]
lemma equivCotangent_symm_apply (e : A ≅ B) (x : B.Cotangent) :
    (equivCotangent e).symm x = mapCotangent e.inv x := rfl

private lemma comap_hom_toRingHom_ker_eq (I : Ideal A) [Nontrivial (A ⧸ I)] :
    Ideal.comap (Hom.hom (A.toOfQuot I)).toRingHom (A.ofQuot I).ker =
      RingHom.ker (Hom.hom (A.toOfQuot I)).toRingHom ⊔ A.ker := by
  simp only [ker_extension]
  have : IsLocalRing (A ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have : IsLocalHom (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective.isLocalHom
  change Ideal.comap (Ideal.Quotient.mk I) (maximalIdeal (A ⧸ I)) =
    RingHom.ker (Ideal.Quotient.mk I) ⊔ _
  rw [maximalIdeal_comap, Ideal.mk_ker, right_eq_sup]
  exact le_maximalIdeal (Ideal.Quotient.nontrivial_iff.mp ‹_›)

theorem mapcotangent_toOfQuot_surjective (I : Ideal A) [Nontrivial (A ⧸ I)] :
    Surjective (mapCotangent (A.toOfQuot I)) :=
  Extension.Cotangent.map_surjective_of_comap_eq (A.toOfQuot I).hom Ideal.Quotient.mk_surjective
    (comap_hom_toRingHom_ker_eq I)

open Submodule in
theorem mapcotangent_toOfQuot_bijective_iff (I : Ideal A) [Nontrivial (A ⧸ I)] :
    Bijective (mapCotangent (A.toOfQuot I)) ↔ I ≤ maximalIdeal A ^ 2 := by
  simp only [Bijective, mapcotangent_toOfQuot_surjective I, and_true, ← LinearMap.ker_eq_bot]
  rw [← Submodule.restrictScalars_inj A.Ring, Cotangent.map_ker_of_surjective _
    Ideal.Quotient.mk_surjective (comap_hom_toRingHom_ker_eq I)]
  simp only [ker_toRingHom_toOfQuot, ker_extension, comap_inf, comap_subtype_le_iff, Std.le_refl,
    inf_of_le_left, inf_le_left, restrictScalars_bot]
  rw [eq_bot_iff, map_le_iff_le_comap, comap_bot, Cotangent.ker_mk,
    ← map_le_map_iff_of_injective (subtype_injective _), map_comap_eq, range_subtype,
    ker_extension, map_smul'', Submodule.map_top, smul_eq_mul, range_subtype, ← pow_two,
    ← right_eq_inf.mpr (le_maximalIdeal (Ideal.Quotient.nontrivial_iff.mp ‹_›))]

@[stacks 06S3 "(1) => (2)"]
theorem mapcotangent_surjective_of_surjective {f : A ⟶ B} (h : Surjective f.toAlgHom) :
    Surjective (mapCotangent f) := by
  rw [← toOfQuot_comp_ofQuotKerIsoOfSurjective_hom h, mapCotangent_comp, LinearMap.coe_comp]
  exact Function.Surjective.comp (equivCotangent (ofQuotKerIsoOfSurjective f h)).surjective
    (mapcotangent_toOfQuot_surjective _)

theorem mapCotangent_bijective_iff {f : A ⟶ B} (hf : Surjective f.toAlgHom) :
    Function.Bijective (mapCotangent f) ↔ RingHom.ker f.toAlgHom ≤ maximalIdeal A ^ 2 := by
  nth_rw 1 [← mapcotangent_toOfQuot_bijective_iff, ← toOfQuot_comp_ofQuotKerIsoOfSurjective_hom hf,
    mapCotangent_comp, LinearMap.coe_comp, Bijective.of_comp_iff']
  exact (equivCotangent (ofQuotKerIsoOfSurjective f hf)).bijective

@[stacks 06S3 "(2) => (3)"]
theorem mapCotangent_mapOfQuot_surjective_of_mapCotangent_surjective {I : Ideal A} {J : Ideal B}
    {f : A ⟶ B} [Nontrivial (A ⧸ I)] [Nontrivial (B ⧸ J)] (hf : I ≤ J.comap f.toAlgHom)
    (h : Surjective (mapCotangent f)) : Surjective (mapCotangent (mapOfQuot f hf)) := by
  have : Surjective ((mapCotangent (mapOfQuot f hf)) ∘ₗ (mapCotangent (A.toOfQuot I))) := by
    rw [← mapCotangent_comp, toOfQuot_comp_mapOfQuot, mapCotangent_comp, LinearMap.coe_comp]
    exact .comp (mapcotangent_toOfQuot_surjective J) h
  exact .of_comp this

open Submodule in
@[stacks 06GZ "(2) => (1)"]
theorem surjective_of_mapcotangent_surjective [IsPrecomplete (maximalIdeal A) A]
    [IsNoetherianRing B] [haus : IsHausdorff (maximalIdeal B) B] (f : A ⟶ B)
    (h : Surjective (mapCotangent f)) : Surjective f.toAlgHom := by
  have map_eq : (maximalIdeal A).map f.toAlgHom = maximalIdeal B := by
    refine le_antisymm f.map_maximalIdeal_le ?_
    rw [← comap_subtype_eq_top, ← CotangentSpace.map_eq_top_iff, eq_top_iff']
    intro x
    obtain ⟨⟨x, x_in⟩, rfl⟩ := (maximalIdeal B).toCotangent_surjective x
    obtain ⟨y, hy⟩ := h (Cotangent.mk ⟨x, B.ker_extension ▸ x_in⟩)
    obtain ⟨y, rfl⟩ := Cotangent.mk_surjective y
    simp only [Cotangent.map_mk, Hom.toAlgHom_apply, Cotangent.mk_eq_mk_iff_sub_mem] at hy
    suffices ∃ a ∈ Ideal.map (Hom.toAlgHom f) A.ker, a ∈ B.ker ∧ a - x ∈ B.ker ^ 2 by
      simpa [Ideal.toCotangent_eq]
    refine ⟨f.toAlgHom y, Ideal.mem_map_of_mem _ y.prop, ?_, hy⟩
    rw [ker_extension, ← Ideal.mem_comap, f.comap_maximalIdeal_eq, ← ker_extension]
    exact y.prop
  rw [← map_eq, ← Ideal.map_coe, ← AlgHom.toRingHom_eq_coe] at haus
  refine surjective_of_mk_map_comp_surjective (I := maximalIdeal A) _ fun y ↦ ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨x, hx⟩ := A.residue_surjective (B.residue y)
  exact ⟨x, by rw [RingHom.comp_apply, Ideal.Quotient.eq, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Ideal.map_coe, map_eq, ← residue_eq_zero_iff, map_sub, sub_eq_zero, ← hx, ← AlgHom.comp_apply,
    f.residue_comp]⟩

end mapCotangent

section specialFiber

open LinearMap

variable [IsLocalRing Λ] [Algebra.IsIntegral Λ k]

/-- The canonical linear map from the cotangent space of `Λ` to the cotangent space of `A`. -/
def baseCotangentMap (A : LocExtCat Λ k) : CotangentSpace Λ →ₗ[Λ] A.Cotangent :=
  (cotangentEquivCotangentKer.symm.toLinearMap.restrictScalars Λ).comp <|
    (maximalIdeal Λ).mapCotangent A.ker (Algebra.ofId Λ A) (by rw [← Ideal.comap_coe,
      Algebra.toRingHom_ofId, ker_extension, comap_algebraMap_maximalIdeal])

@[simp]
lemma baseCotangentMap_toCotangent (x : maximalIdeal Λ) :
    A.baseCotangentMap ((maximalIdeal Λ).toCotangent x) = Cotangent.mk ⟨algebraMap Λ A x, by
      have := isLocalHom_algebraMap A
      rw [← Ideal.mem_comap, ker_extension, maximalIdeal_comap]
      exact x.prop⟩ := rfl

theorem range_baseCotangentMap_le (A : LocExtCat Λ k) :
    A.baseCotangentMap.range ≤ A.cotangentComplex.ker.restrictScalars Λ := by
  intro x hx
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  rcases hx with ⟨y, hy⟩
  rw [Submodule.restrictScalars_mem, mem_ker, ← hy]
  obtain ⟨y, rfl⟩ := (maximalIdeal Λ).toCotangent_surjective y
  simp

lemma mapCotangent_comp_liftBaseChange_baseCotangentMap (f : A ⟶ B) :
    (mapCotangent f).comp (liftBaseChange k A.baseCotangentMap) =
      liftBaseChange k B.baseCotangentMap := by
  ext x
  obtain ⟨x, rfl⟩ := (maximalIdeal Λ).toCotangent_surjective x
  simp

open Submodule in
theorem range_liftBaseChange_baseCotangentMap :
    (liftBaseChange k A.baseCotangentMap).range = (mapCotangent A.toSpecialFiber).ker := by
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
    rcases hx with ⟨y, hy⟩; rw [← hy]
    clear * -; induction y with
    | zero => simp
    | tmul x y =>
      obtain ⟨y, rfl⟩ := (maximalIdeal Λ).toCotangent_surjective y
      simp [(mk_eq_zero ..).mpr]
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  · rw [← restrictScalars_mem A, Cotangent.map_ker_of_surjective _ Ideal.Quotient.mk_surjective <|
        comap_hom_toRingHom_ker_eq ((maximalIdeal Λ).map (algebraMap Λ A)), ker_toRingHom_toOfQuot,
      comap_inf, comap_subtype_self, inf_top_eq, mem_map] at hx
    obtain ⟨⟨x, x_in⟩, rfl⟩ := Cotangent.mk_surjective x
    simp only [mem_comap, subtype_apply, Subtype.exists, ker_extension, exists_and_left] at hx
    rcases hx with ⟨y, y_in, y_in', hy⟩
    rw [← hy]; clear * - y_in
    have : IsLocalHom (algebraMap Λ A) := isLocalHom_algebraMap A
    induction y_in using span_induction with
    | mem x h =>
      obtain ⟨r, r_in, rfl⟩ := h
      exact ⟨1 ⊗ₜ (maximalIdeal Λ).toCotangent ⟨r, r_in⟩, by simp⟩
    | zero => simp only [(mk_eq_zero ..).mpr, map_zero, zero_mem]
    | add u v hu hv ihu ihv =>
      exact add_mem (ihu (map_maximalIdeal_le _ hu)) (ihv (map_maximalIdeal_le _ hv))
    | smul a x hx ih =>
      rw [← SetLike.mk_smul_mk _ _ _ (A.ker_extension ▸ map_maximalIdeal_le _ hx), map_smul,
        algebra_compatible_smul k]
      exact smul_mem _ _ (ih (map_maximalIdeal_le _ hx))

theorem exact_liftBaseChange_baseCotangentMap_mapCotangent_toSpecialFiber :
    Exact (liftBaseChange k A.baseCotangentMap) (mapCotangent A.toSpecialFiber) :=
  LinearMap.exact_iff.mpr A.range_liftBaseChange_baseCotangentMap.symm

@[stacks 06S3 "(3) => (2)"]
theorem mapcotangent_surjective_of_mapcotangent_surjective_mapSpecialFiber
    (f : A ⟶ B) (h : Surjective (mapCotangent (mapSpecialFiber f))) :
    Surjective (mapCotangent f) := fun y ↦ by
  obtain ⟨x, hx⟩ := h (mapCotangent B.toSpecialFiber y)
  obtain ⟨x, rfl⟩ := mapcotangent_toOfQuot_surjective _ x
  rw [← LinearMap.comp_apply, ← mapCotangent_comp, toOfQuot_comp_mapOfQuot,
    mapCotangent_comp, LinearMap.comp_apply] at hx
  have h_ker : y - mapCotangent f x ∈ LinearMap.ker (mapCotangent B.toSpecialFiber) := by
    rw [LinearMap.mem_ker, map_sub, hx, sub_self]
  rw [← range_liftBaseChange_baseCotangentMap, LinearMap.mem_range] at h_ker
  rcases h_ker with ⟨z, hz⟩
  use x + liftBaseChange k A.baseCotangentMap z
  rw [map_add, ← LinearMap.comp_apply, mapCotangent_comp_liftBaseChange_baseCotangentMap, hz,
    add_sub_cancel]

end specialFiber

end Cotangent

end LocExtCat

/-- The complete base category for deformation theory over `Λ`. This is the full subcategory of
`LocExtCat Λ k` consisting of complete Noetherian local `Λ`-algebras with residue field `k`. -/
abbrev CBaseCat (Λ : Type u) [CommRing Λ] (k : Type u) [Field k] [Algebra Λ k] : Type _ :=
  ObjectProperty.FullSubcategory fun A : LocExtCat Λ k ↦
    IsNoetherianRing A ∧ IsAdicComplete (maximalIdeal A) A

namespace CBaseCat

instance {A : CBaseCat Λ k} : IsNoetherianRing A.obj := A.property.left

instance {A : CBaseCat Λ k} : IsAdicComplete (maximalIdeal A.obj) A.obj := A.property.right

end CBaseCat

/-- The base category for deformation theory over `Λ`. This is the full subcategory of
`LocExtCat Λ k` consisting of Artinian local `Λ`-algebras with residue field `k`. -/
@[stacks 06GC]
abbrev BaseCat (Λ : Type u) [CommRing Λ] (k : Type u) [Field k] [Algebra Λ k] : Type _ :=
  ObjectProperty.FullSubcategory fun A : LocExtCat Λ k ↦ IsArtinianRing A

namespace BaseCat

instance (A : BaseCat Λ k) : IsArtinianRing A.obj := A.property

/-- The natural inclusion functor from the base category to the complete base category. -/
abbrev ιToCBaseCat (Λ : Type u) [CommRing Λ] (k : Type u) [Field k] [Algebra Λ k] :
    BaseCat Λ k ⥤ CBaseCat Λ k :=
  ObjectProperty.ιOfLE fun _ _ ↦ ⟨inferInstance, inferInstance⟩

instance coeExtension : CoeOut (BaseCat Λ k) (Extension.{u} Λ k) := ⟨fun A ↦ A.obj.toExtension⟩

instance coeRing : CoeSort (BaseCat Λ k) (Type u) := ⟨fun A ↦ A.obj.Ring⟩

variable {A B C : BaseCat Λ k} {f : A ⟶ B}

variable (Λ k) in
/-- Lift an unbundled extension whose underlying ring is local and Artinian
to an object in `BaseCat Λ k`. -/
abbrev of (X : Extension.{u} Λ k) [IsLocalRing X.Ring] [IsArtinianRing X.Ring] :
    BaseCat Λ k := ⟨.of Λ k X, inferInstance⟩

lemma coe_of (X : Extension.{u} Λ k) [IsLocalRing X.Ring] [IsArtinianRing X.Ring] :
    (of Λ k X : Type u) = X.Ring := rfl

/-- The object in `BaseCat` obtained from the quotient by a proper ideal. -/
def ofQuot (A : BaseCat Λ k) (I : Ideal A) [Nontrivial (A ⧸ I)] : BaseCat Λ k :=
  ⟨A.obj.ofQuot I, (A.obj.toalghom_toOfQuot_surjective I).isArtinianRing⟩

/-- Upgrades the canonical quotient map `A → A ⧸ I` to a morphism in `BaseCat`. -/
abbrev toOfQuot (A : BaseCat Λ k) (I : Ideal A) [Nontrivial (A ⧸ I)] :
    A ⟶ A.ofQuot I := ObjectProperty.homMk (A.obj.toOfQuot I)

/-- The morphism between quotient objects in `BaseCat` induced by a morphism `f : A ⟶ B`.
This is the categorical counterpart to `Ideal.quotientMapₐ` in the Artinian setting. -/
abbrev mapOfQuot (f : A ⟶ B) {I : Ideal A} {J : Ideal B} [Nontrivial (A ⧸ I)]
    [Nontrivial (B ⧸ J)] (hf : I ≤ J.comap f.hom.toAlgHom) : A.ofQuot I ⟶ B.ofQuot J :=
  ObjectProperty.homMk <| LocExtCat.mapOfQuot f.hom hf

lemma toOfQuot_comp_mapOfQuot (f : A ⟶ B) {I : Ideal A} {J : Ideal B}
    [Nontrivial (A ⧸ I)] [Nontrivial (B ⧸ J)] (hf : I ≤ J.comap f.hom.toAlgHom) :
    A.toOfQuot I ≫ mapOfQuot f hf = f ≫ B.toOfQuot J := rfl

/-- The quotient of a local Artinian algebra by the `n`-th power of its maximal ideal,
viewed as an object in `BaseCat`. -/
abbrev infinitesimal (n : ℕ) [NeZero n] (A : BaseCat Λ k) : BaseCat Λ k :=
  A.ofQuot (maximalIdeal A ^ n)

/-- The canonical quotient morphism from `A` to its infinitesimal neighborhood in `BaseCat`. -/
abbrev toInfinitesimal (n : ℕ) [NeZero n] (A : BaseCat Λ k) :
    A ⟶ A.infinitesimal n := toOfQuot ..

/-- The morphism between infinitesimal neighborhoods induced by a morphism in `BaseCat`. -/
abbrev mapInfinitesimal (m n : ℕ) [NeZero m] [NeZero n] (hmn : n ≤ m) (f : A ⟶ B) :
    A.infinitesimal m ⟶ B.infinitesimal n :=
  ObjectProperty.homMk (LocExtCat.mapInfinitesimal m n hmn f.hom)

/-- The special fiber of `A` over `Λ` when `Λ` is a local ring, defined as the quotient by
the extended maximal ideal of `Λ`, viewed as an object in `BaseCat`. -/
abbrev specialFiber [IsLocalRing Λ] [Algebra.IsIntegral Λ k] (A : BaseCat Λ k) :
    BaseCat Λ k :=
  ⟨A.obj.specialFiber, (A.obj.toalghom_toOfQuot_surjective _).isArtinianRing⟩

/-- The canonical morphism from `A` to its special fiber in `BaseCat`. -/
abbrev toSpecialFiber [IsLocalRing Λ] [Algebra.IsIntegral Λ k] (A : BaseCat Λ k) :
    A ⟶ A.specialFiber :=
  ObjectProperty.homMk A.obj.toSpecialFiber

/-- The morphism between special fibers induced by a morphism in `BaseCat`. -/
abbrev mapSpecialFiber [IsLocalRing Λ] [Algebra.IsIntegral Λ k] (f : A ⟶ B) :
    A.specialFiber ⟶ B.specialFiber :=
  ObjectProperty.homMk (LocExtCat.mapSpecialFiber f.hom)

/-- A morphism `f : A ⟶ B` in `BaseCat` is a small extension if it is a surjective map
whose kernel is a principal ideal annihilated by the maximal ideal of `A`. -/
@[stacks 06GD]
class IsSmallExtension (f : A ⟶ B) : Prop where
  private mk ::
  surjective (f) : Function.Surjective f.hom.toAlgHom
  isPrincipal_ker (f) : (RingHom.ker f.hom.toAlgHom).IsPrincipal
  le_annihilator_ker (f) : maximalIdeal A ≤ (RingHom.ker f.hom.toAlgHom).annihilator

variable (f) in
theorem isSmallExtenstion_iff : IsSmallExtension f ↔ Surjective f.hom.toAlgHom ∧
    ∃ x : A, Ideal.span {x} = RingHom.ker f.hom.toAlgHom ∧ ∀ y ∈ maximalIdeal A, x * y = 0 := by
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
  (isSmallExtenstion_iff f).mpr ⟨h.surjective, 0, by
    have := h.injective
    rw [RingHom.injective_iff_ker_eq_bot] at this
    simp [this]⟩

instance IsSmallExtension.hom_iso (e : A ≅ B) : IsSmallExtension e.hom :=
  isSmallExtension_of_bijective <| ConcreteCategory.bijective_of_isIso e.hom

theorem IsSmallExtension.toOfQuot_span_singleton (A : BaseCat Λ k) (x : A)
    [Nontrivial (A ⧸ (Ideal.span {x}))] (h : ∀ y ∈ maximalIdeal A, x * y = 0) :
    IsSmallExtension (A.toOfQuot (Ideal.span {x})) := by
  rw [isSmallExtenstion_iff]
  refine ⟨A.obj.toalghom_toOfQuot_surjective _, x, ?_, h⟩
  change _ = RingHom.ker (A.obj.toOfQuot (Ideal.span {x})).toAlgHom
  rw [LocExtCat.ker_toAlgHom_toOfQuot]

open Submodule in
@[elab_as_elim, stacks 06GE]
theorem induction_on_isSmallExtension (hf : Surjective f.hom.toAlgHom)
    {P : ∀ {A B : BaseCat Λ k} (f : A ⟶ B), Surjective f.hom.toAlgHom → Prop}
    (small_ext : ∀ {X Y : BaseCat Λ k} (f : X ⟶ Y) [IsSmallExtension f],
      P f (IsSmallExtension.surjective f))
    (comp : ∀ {A B C : BaseCat Λ k} (f : A ⟶ B) (g : B ⟶ C) [IsSmallExtension f]
      (hg : Surjective g.hom.toAlgHom), P g hg →
    P (f ≫ g) (hg.comp (IsSmallExtension.surjective f))) : P f hf := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = Module.length A A :=
    ENat.ne_top_iff_exists.mp Module.length_ne_top
  revert A; induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A f hf hlen
    have hn : n ≠ 0 := by
      intro hn; revert hlen
      rw [imp_false, hn, Nat.cast_zero, eq_comm, Module.length_eq_zero_iff,
        ← not_nontrivial_iff_subsingleton, not_not]
      infer_instance
    let I := RingHom.ker f.hom.toAlgHom
    by_cases hI : I = ⊥
    · rw [← RingHom.injective_iff_ker_eq_bot] at hI
      have : IsSmallExtension f := isSmallExtension_of_bijective ⟨hI, hf⟩
      exact small_ext f
    obtain ⟨x, hx, x_ne⟩ := (Submodule.ne_bot_iff _).mp (Ideal.annihilator_inf_ne_bot
      ((isArtinianRing_iff_isNilpotent_maximalIdeal A).mp inferInstance) hI)
    have x_in : x ∈ I := (mem_inf.mp hx).right
    replace hx : ∀ y ∈ maximalIdeal A, x * y = 0 := mem_annihilator.mp (mem_inf.mp hx).left
    have : Nontrivial (A ⧸ Ideal.span {x}) := by
      rw [Ideal.Quotient.nontrivial_iff]
      refine Ideal.span_singleton_ne_top (le_maximalIdeal ?_ x_in)
      rw [Ideal.ne_top_iff_exists_maximal]
      exact ⟨maximalIdeal A, maximalIdeal.isMaximal A, le_maximalIdeal
        (RingHom.ker_ne_top f.hom.toAlgHom)⟩
    have : IsLocalRing (A ⧸ Ideal.span {x}) := .of_surjective' _ Ideal.Quotient.mk_surjective
    let C := A.ofQuot (Ideal.span {x})
    let g : A ⟶ C := A.toOfQuot (Ideal.span {x})
    have hg : IsSmallExtension g := IsSmallExtension.toOfQuot_span_singleton A x hx
    let f' : C ⟶ B := ObjectProperty.homMk (LocExtCat.liftToOfQuot (Ideal.span {x}) f.hom
      (by simpa [← RingHom.mem_ker, ← SetLike.le_def]))
    have g_comp : g ≫ f' = f := by ext1; simpa using LocExtCat.toOfQuot_comp_liftToOfQuot ..
    obtain ⟨m, hm⟩ : ∃ n : ℕ, n = Module.length C C :=
      ENat.ne_top_iff_exists.mp Module.length_ne_top
    suffices h : m < n by
      simp_rw [← g_comp]
      refine comp g f' ?_ (ih m h _ hm)
      exact Ideal.Quotient.lift_surjective_of_surjective (Ideal.span {x}) (by
        simpa [← RingHom.mem_ker, ← SetLike.le_def]) hf
    have := Submodule.length_le_length_restrictScalars (R := (A ⧸ Ideal.span {x}))
      (M := (A ⧸ Ideal.span {x})) A ⊤
    rw [Module.length_top, restrictScalars_top, Module.length_top] at this
    rw [← ENat.coe_lt_coe, hlen, hm]
    exact this.trans_lt (length_quotient_lt (Ideal.span {x}) (by simpa))

/-- A morphism `f : A ⟶ B` in the base category is called minimally surjective if its
underlying algebra homomorphism is surjective, and it satisfies the following minimality
condition: for any object `C` and morphism `g : C ⟶ A` in `BaseCat`, if the composition
`g ≫ f` is surjective, then `g` itself must be surjective. -/
@[stacks 06GF, mk_iff]
class IsMinimallySurjective (f : A ⟶ B) : Prop where
  surjective (f) : Surjective f.hom.toAlgHom
  surjective_of_comp_left (f) {C : BaseCat Λ k} (g : C ⟶ A) :
    Surjective (g ≫ f).hom.toAlgHom → Surjective g.hom.toAlgHom

instance IsMinimallySurjective.hom_iso (e : A ≅ B) : IsMinimallySurjective e.hom := by
  refine ⟨(ConcreteCategory.bijective_of_isIso e.hom).surjective, fun {C} g hg ↦ ?_⟩
  rw [ObjectProperty.FullSubcategory.comp_hom, LocExtCat.toAlgHom_comp, AlgHom.coe_comp] at hg
  exact Surjective.of_comp_left hg (ConcreteCategory.bijective_of_isIso e.hom).injective

instance IsMinimallySurjective.comp (f : A ⟶ B) (g : B ⟶ C) [IsMinimallySurjective f]
    [IsMinimallySurjective g] : IsMinimallySurjective (f ≫ g) :=
  ⟨by simpa using .comp (IsMinimallySurjective.surjective g) (IsMinimallySurjective.surjective f),
  fun _ h ↦ IsMinimallySurjective.surjective_of_comp_left f _
    (IsMinimallySurjective.surjective_of_comp_left g _ h)⟩

theorem isMinimallySurjective_toOfQuot_of_le {I : Ideal A} [Nontrivial (A ⧸ I)]
    (h : I ≤ maximalIdeal A ^ 2) : IsMinimallySurjective (A.toOfQuot I) := by
  rw [← LocExtCat.mapcotangent_toOfQuot_bijective_iff] at h
  refine ⟨A.obj.toalghom_toOfQuot_surjective I, fun {C} g hg ↦ ?_⟩
  apply LocExtCat.surjective_of_mapcotangent_surjective
  apply Surjective.of_comp_left (f := LocExtCat.mapCotangent (A.obj.toOfQuot I))
  · rw [← LinearMap.coe_comp, ← LocExtCat.mapCotangent_comp]
    exact LocExtCat.mapcotangent_surjective_of_surjective hg
  · exact h.injective

section IsLocalRing

variable [IsLocalRing Λ] [Module.Finite Λ k]

/-- Given morphisms `f : A ⟶ C` and `g : B ⟶ C` in `BaseCat` where `g.hom.toAlgHom` is surjective,
`ofPullback` is the object in `BaseCat` obtained from the pullback of the underlying
algebra homomorphisms`. -/
@[stacks 06GH "(1)"]
def ofPullback (f : A ⟶ C) (g : B ⟶ C) (hg : Surjective g.hom.toAlgHom) : BaseCat Λ k :=
  ⟨.ofPullback f.hom g.hom hg, LocExtCat.isArtinianRing_ofPullback ..⟩

/-- Upgrades the first projection map from the pullback algebra to a morphism in `BaseCat`. -/
abbrev pullbackFst (f : A ⟶ C) (g : B ⟶ C) (hg : Surjective g.hom.toAlgHom) :
    ofPullback f g hg ⟶ A := ObjectProperty.homMk (LocExtCat.pullbackFst f.hom g.hom hg)

/-- Upgrades the second projection map from the pullback algebra to a morphism in `BaseCat`. -/
abbrev pullbackSnd (f : A ⟶ C) (g : B ⟶ C) (hg : Surjective g.hom.toAlgHom) :
    ofPullback f g hg ⟶ B := ObjectProperty.homMk (LocExtCat.pullbackSnd f.hom g.hom hg)

lemma pullback_comm_sq (f : A ⟶ C) (g : B ⟶ C) (hg : Surjective g.hom.toAlgHom) :
    pullbackFst f g hg ≫ f = pullbackSnd f g hg ≫ g := by
  ext1; simpa using LocExtCat.pullback_comm_sq f.hom g.hom hg

@[stacks 06GH "(2)"]
instance pullbackFst_isSmallExtension (f : A ⟶ C) (g : B ⟶ C) [IsSmallExtension g] :
    IsSmallExtension (pullbackFst f g (IsSmallExtension.surjective g)) := by
  have : IsLocalRing ↥(f.hom.toAlgHom.pullback g.hom.toAlgHom) :=
    RingHom.isLocalRing_pullback f.hom.toAlgHom.toRingHom g.hom.toAlgHom.toRingHom
      ⟨(IsSmallExtension.surjective g).isLocalHom.map_nonunit⟩
  obtain ⟨x, x_span, hx⟩ := ((isSmallExtenstion_iff g).mp ‹_›).right
  have g_apply : g.hom.toAlgHom x = 0 := by
    rw [← RingHom.mem_ker, ← x_span]
    exact Ideal.mem_span_singleton_self x
  rw [isSmallExtenstion_iff]
  refine ⟨(f.hom.toAlgHom.surjective_pullbackFst_of_surjective g.hom.toAlgHom
    (IsSmallExtension.surjective g)), ?_⟩
  change ∃ x : f.hom.toAlgHom.pullback g.hom.toAlgHom, Ideal.span {x} =
    RingHom.ker (AlgHom.pullbackFst ..) ∧
      ∀ y ∈ maximalIdeal (f.hom.toAlgHom.pullback g.hom.toAlgHom), x * y = 0
  refine ⟨⟨(0, x), by simpa using g_apply.symm⟩, ?_, fun ⟨⟨a, b⟩, hab⟩ h ↦ ?_⟩
  · ext ⟨⟨u, v⟩, h⟩
    suffices (∃ a b, f.hom.toAlgHom a = g.hom.toAlgHom b ∧ 0 = u ∧ b * x = v) ↔ u = 0 by
      simpa [Ideal.mem_span_singleton']
    simp_rw [and_left_comm, eq_comm, exists_and_left, and_iff_left_iff_imp]
    intro u_eq
    replace h : 0 = g.hom.toAlgHom v := by simpa [u_eq] using h
    rw [eq_comm, ← RingHom.mem_ker, ← x_span, Ideal.mem_span_singleton'] at h
    rcases h with ⟨w, hw⟩
    obtain ⟨z, m, m_in, hm⟩ := LocExtCat.exists_mem_maximalIdeal_toAlgHom_apply_add_eq
      g.hom f.hom w (IsSmallExtension.surjective g)
    exact ⟨z, w + m, hm.symm, by rw [add_mul, hw, mul_comm, hx m m_in, add_zero]⟩
  · suffices x * b = 0 by simpa [← Subtype.val_inj]
    simp only [mem_maximalIdeal, mem_nonunits_iff, AlgHom.isUnit_pullback_mk_iff, not_and] at h
    simp only [AlgHom.mem_equalizer, AlgHom.coe_comp, Function.comp_apply, AlgHom.fst_apply,
      AlgHom.snd_apply] at hab
    apply hx; intro hb; revert h
    simpa [hb] using f.hom.isLocalHom_toAlgHom.map_nonunit a (hab ▸ IsUnit.map g.hom.toAlgHom hb)

open ObjectProperty.FullSubcategory in
@[stacks 06S5]
theorem isMinimallySurjective_iff_isMinimallySurjective_mapOfQuot (f : A ⟶ B) {I : Ideal A}
    {J : Ideal B} [Nontrivial (A ⧸ I)] [Nontrivial (B ⧸ J)] (hI : I ≤ maximalIdeal A ^ 2)
    (hJ : J ≤ maximalIdeal B ^ 2) (hf : I ≤ J.comap f.hom.toAlgHom) :
    IsMinimallySurjective f ↔ IsMinimallySurjective (mapOfQuot f hf) := by
  refine ⟨fun h ↦ ⟨?_, fun {C} g hg ↦ ?_⟩, fun h ↦ ⟨?_, fun {C} g hg ↦ ?_⟩⟩
  · apply Surjective.of_comp (g := (A.toOfQuot I).hom.toAlgHom)
    rw [← AlgHom.coe_comp, ← LocExtCat.toAlgHom_comp, ← comp_hom, toOfQuot_comp_mapOfQuot]
    simpa using Surjective.comp (B.obj.toalghom_toOfQuot_surjective J) h.surjective
  · let C' := ofPullback g (A.toOfQuot I) (A.obj.toalghom_toOfQuot_surjective I)
    let p : C' ⟶ C := pullbackFst g (A.toOfQuot I) (A.obj.toalghom_toOfQuot_surjective I)
    apply Surjective.of_comp (g := p.hom.toAlgHom)
    rw [← AlgHom.coe_comp, ← LocExtCat.toAlgHom_comp, ← comp_hom, pullback_comm_sq, comp_hom,
      LocExtCat.toAlgHom_comp, AlgHom.coe_comp]
    refine Surjective.comp (A.obj.toalghom_toOfQuot_surjective I) ?_
    apply isMinimallySurjective_toOfQuot_of_le at hJ
    apply IsMinimallySurjective.surjective_of_comp_left (f ≫ B.toOfQuot J)
    rw [← toOfQuot_comp_mapOfQuot (I := I) f hf, Category.assoc', ← pullback_comm_sq,
      Category.assoc, comp_hom, LocExtCat.toAlgHom_comp, AlgHom.coe_comp]
    exact hg.comp (LocExtCat.surjective_pullbackFst _ _ (A.obj.toalghom_toOfQuot_surjective I))
  · apply LocExtCat.surjective_of_mapcotangent_surjective
    apply Surjective.of_comp_left (f := LocExtCat.mapCotangent (B.toOfQuot J).hom)
    · rw [← LinearMap.coe_comp, ← LocExtCat.mapCotangent_comp, ← comp_hom,
        ← toOfQuot_comp_mapOfQuot (I := I) f hf, comp_hom, LocExtCat.mapCotangent_comp,
        LinearMap.coe_comp]
      exact Surjective.comp (LocExtCat.mapcotangent_surjective_of_surjective h.surjective)
        (LocExtCat.mapcotangent_surjective_of_surjective (A.obj.toalghom_toOfQuot_surjective I))
    · exact ((LocExtCat.mapcotangent_toOfQuot_bijective_iff J).mpr hJ).injective
  · apply isMinimallySurjective_toOfQuot_of_le at hI
    apply IsMinimallySurjective.surjective_of_comp_left (A.toOfQuot I ≫ (mapOfQuot f hf))
    rw [toOfQuot_comp_mapOfQuot, Category.assoc', comp_hom, LocExtCat.toAlgHom_comp,
      AlgHom.coe_comp]
    exact (B.obj.toalghom_toOfQuot_surjective J).comp hg

/--/
/-- When `Λ` is a local ring and `k / ResidueField Λ` is a finite separable field extension,
`ofPullbackOfIsSeparable` is the object in `BaseCat` obtained from the pullback of
the underlying algebra homomorphisms of two morphisms`. -/
def ofPullbackOfIsSeparable [Algebra.IsSeparable (ResidueField Λ) k] (f : A ⟶ C) (g : B ⟶ C) :
    BaseCat Λ k :=
  haveI : IsLocalRing ↥(f.hom.toAlgHom.pullback g.hom.toAlgHom) := RingHom.isLocalRing_pullback
    f.hom.toAlgHom.toRingHom g.hom.toAlgHom.toRingHom ⟨g.hom.isLocalHom_toAlgHom.map_nonunit⟩
  ⟨.of Λ k (f.hom.toAlgHom.pullback g.hom.toAlgHom)
    (LocExtCat.residue_comp_pullbackfst_surjective_of_isSeparable f.hom g.hom), inferInstance⟩

end IsLocalRing

end BaseCat

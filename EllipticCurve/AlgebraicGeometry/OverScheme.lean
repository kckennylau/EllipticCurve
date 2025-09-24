/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import EllipticCurve.AlgebraicGeometry.BigAffineZariski
import EllipticCurve.CategoryTheory.PresheafCostructured
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# The Category of Commutative Rings Over a Scheme

Fix a scheme `X`. We define the category of commutative rings `R` equipped with a morphism
`Spec R ⟶ X`.

We define a Grothendieck topology on `OverScheme X` and show that sheaves on `OverScheme X` extend
to sheaves on `CommRingCatᵒᵖ`.
-/

universe w v v₁ v₂ v₃ u u₁ u₂ u₃

open CategoryTheory AlgebraicGeometry Opposite Limits Category

-- MOVE

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D)
  (K : GrothendieckTopology D)

class IsLocallyFullEvil (G : C ⥤ D) : Prop where
  full (G) {X : D} {Y : C} (f : X ⟶ G.obj Y) :
    ∃ (X' : C) (g : X' ⟶ Y) (e : X = G.obj X'), eqToHom e ≫ G.map g = f

class IsLocallyFaithfulEvil (G : C ⥤ D) : Prop where
  faithful (G) {X X' Y : C} {f : X ⟶ Y} {g : X' ⟶ Y} (e : G.obj X = G.obj X')
    (e₂ : G.map f = eqToHom e ≫ G.map g) : ∃ h : X = X', f = eqToHom h ≫ g

theorem _root_.CategoryTheory.Sieve.functorPushforward_functorPullback
    [G.IsLocallyFullEvil] {X : C} (S : Sieve (G.obj X)) :
    (S.functorPullback G).functorPushforward G = S := by
  refine le_antisymm S.functorPullback_pushforward_le fun Y u hu ↦ ?_
  obtain ⟨Y, u, rfl, rfl⟩ := IsLocallyFullEvil.full G u
  rw [eqToHom_refl, id_comp] at hu ⊢
  exact Sieve.image_mem_functorPushforward G _ hu

variable [G.IsLocallyFullEvil] [G.IsLocallyFaithfulEvil]

def inducedTopologyEvil : GrothendieckTopology C where
  sieves _ S := K _ (S.functorPushforward G)
  top_mem' X := by
    change K _ _
    rw [Sieve.functorPushforward_top]
    exact K.top_mem _
  pullback_stable' X Y S iYX hS := by
    refine K.superset_covering ?_ (K.pullback_stable (G.map iYX) hS)
    rintro Z f ⟨W, iWX, iZW, hS, e⟩
    obtain ⟨Z, f, rfl, rfl⟩ := IsLocallyFullEvil.full G f
    obtain ⟨U, g, e, rfl⟩ := IsLocallyFullEvil.full G iZW
    rw [eqToHom_refl, id_comp] at e ⊢
    rw [assoc, ← map_comp, ← map_comp] at e
    obtain ⟨rfl, e⟩ := IsLocallyFaithfulEvil.faithful G _ e
    refine ⟨_, f, 𝟙 _, ?_, (id_comp _).symm⟩
    rw [eqToHom_refl, id_comp] at e
    exact congr(S.arrows $e).to_iff.mpr (S.downward_closed hS g)
  transitive' X S hS S' H' := by
    apply K.transitive hS
    rintro Y _ ⟨Z, g, i, hg, rfl⟩
    rw [Sieve.pullback_comp]
    apply K.pullback_stable i
    refine K.superset_covering ?_ (H' hg)
    rintro W _ ⟨Z', g', i', hg, rfl⟩
    refine ⟨Z', g' ≫ g , i', hg, ?_⟩
    simp

@[simp] lemma coe_inducedTopologyEvil {X : C} :
    G.inducedTopologyEvil K X = {S | S.functorPushforward G ∈ K _} := rfl

theorem functorPullback_mem_inducedTopologyEvil {X : C} {S : Sieve (G.obj X)} (hs : S ∈ K _) :
    S.functorPullback G ∈ G.inducedTopologyEvil K X := by
  rwa [coe_inducedTopologyEvil, Set.mem_setOf, S.functorPushforward_functorPullback]

end CategoryTheory.Functor

-- MOVE
namespace CategoryTheory.CostructuredArrow

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (S : C ⥤ D) (T : D)
  (K : GrothendieckTopology C)

open GrothendieckTopology

instance : (proj S T).IsLocallyFullEvil where
  full {X Y} f := ⟨mk (S.map f ≫ Y.hom), homMk f, rfl, id_comp _⟩

instance : (proj S T).IsLocallyFaithfulEvil where
  faithful {X X' Y} f g e₁ e₂ := by
    obtain ⟨X, x, rfl⟩ := mk_surjective X
    obtain ⟨X', x', rfl⟩ := mk_surjective X'
    obtain ⟨Y, y, rfl⟩ := mk_surjective Y
    change X = X' at e₁; subst e₁
    rw [eqToHom_refl, id_comp] at e₂
    change f.left = g.left at e₂
    have wf : S.map f.left ≫ y = x := w f
    have wg : S.map g.left ≫ y = x' := w g
    rw [e₂] at wf
    have : x = x' := wf.symm.trans wg; subst this
    refine ⟨rfl, ?_⟩
    rw [eqToHom_refl, id_comp]
    exact (proj S T).map_injective e₂

def inducedTopology : GrothendieckTopology (CostructuredArrow S T) :=
  (proj S T).inducedTopologyEvil K

variable {S T}

def FamilyOfElements (ℱ : (CostructuredArrow S T)ᵒᵖ ⥤ Type (max w v₂)) (X : CostructuredArrow S T)
    (p : Presieve ((proj S T).obj X)) : Type _ :=
  ∀ ⦃Y⦄ (u : Y ⟶ ((proj S T).obj X)) (_ : p u), ℱ.obj (op (mk (S.map u ≫ X.hom)))

variable (ℱ : (CostructuredArrow S T)ᵒᵖ ⥤ Type (max w v₂))

namespace FamilyOfElements

variable (X : CostructuredArrow S T) (s : Sieve ((proj S T).obj X))

@[simps] def equiv :
    FamilyOfElements ℱ X s.arrows ≃ Presieve.FamilyOfElements ℱ s.functorPullback.arrows where
  toFun elems Y u hu := ℱ.map (eqToHom ((eq_mk _).trans <| by rw [← w u])).op (elems u.left hu)
  invFun elems Y u hu := elems (homMk u) hu
  left_inv elems := funext₃ fun Y u hu ↦ by simp
  right_inv elems := funext₃ fun Y u hu ↦ by
    obtain ⟨Y, y, rfl⟩ := mk_surjective Y
    obtain ⟨u : Y ⟶ X.left, w, rfl⟩ := homMk_surjective u
    dsimp at w; subst w; simp

-- we'll skip the generalisation
variable {ℱ X s}

def Compatible (elems : FamilyOfElements ℱ X s.arrows) : Prop :=
  ∀ {Y Z} {f : Y ⟶ ((proj S T).obj X)} (g : Z ⟶ Y) (hf : s f),
    ℱ.map (homMk g).op (elems _ hf) = elems _ (s.downward_closed hf _)

variable (elems : FamilyOfElements ℱ X s.arrows)

theorem compatible_equiv_iff_compatible :
    (equiv ℱ X s elems).Compatible ↔ elems.Compatible := by
  rw [Presieve.compatible_iff_sieveCompatible]
  refine ⟨fun c Y Z f g hf ↦ ?_, fun c Y Z f g hf ↦ ?_⟩
  · have := @c (mk (S.map f ≫ X.hom)) (mk (S.map (g ≫ f) ≫ X.hom)) (homMk f) (homMk g) hf
    simp_rw [equiv_apply, ← FunctorToTypes.map_comp_apply, ← op_comp, ← eqToIso.hom, ← Iso.op_hom,
      ← Functor.mapIso_hom, ← Iso.toEquiv_fun, ← Equiv.eq_symm_apply, comp_left, homMk_left] at this
    simp [this]
  · have : _ = elems ((g ≫ f).left) _ := c g.left hf
    simp_rw [equiv_apply, ← this, ← FunctorToTypes.map_comp_apply, ← op_comp]
    exact congr_arg₂ _ (congr_arg _ (by simp)) rfl

@[simp] def toExtension : Presieve.FamilyOfElements (Types.extension ℱ) s.arrows :=
  fun _ u hu ↦ .mk (S.map u ≫ X.hom) (elems u hu)

def IsAmalgamation (x₀ : ℱ.obj (op X)) : Prop :=
  ∀ ⦃Y⦄ (u : Y ⟶ X.left) (hu : s u), ℱ.map (homMk u).op x₀ = elems u hu

variable {elems} {x₀ : ℱ.obj (op X)}

theorem isAmalgamation_equiv_iff :
    (equiv ℱ X s elems).IsAmalgamation x₀ ↔ elems.IsAmalgamation x₀ := by
  refine ⟨fun ha Y u hu ↦ ?_, fun ha Y u hu ↦ ?_⟩
  · refine (@ha (mk (S.map u ≫ X.hom)) (homMk u) hu).trans ?_
    rw [equiv_apply, eqToHom_op, eqToHom_refl, ℱ.map_id, types_id_apply]; rfl
  · obtain ⟨Y, y, rfl⟩ := mk_surjective Y
    obtain ⟨u : Y ⟶ X.left, w, rfl⟩ := homMk_surjective u
    dsimp at w; subst w
    exact (ha u hu).trans (by simp [equiv])

theorem isAmalgamation_toExtension_iff {X : C} {t : S.obj X ⟶ T} {s : Sieve X}
    {elems : FamilyOfElements ℱ (mk t) s.arrows}
    (isSheafFor_yoneda : Presieve.IsSheafFor (S.op ⋙ yoneda.obj T) s.arrows)
    {x₀ : (Types.extension ℱ).obj (op X)} :
    elems.toExtension.IsAmalgamation x₀ ↔
      ∃ h : x₀.fst = t, elems.IsAmalgamation (ℱ.map (eqToHom (by rw [h])).op x₀.snd) := by
  refine ⟨fun ha ↦ ⟨?_, ?_⟩, fun ha ↦ ?_⟩
  · refine isSheafFor_yoneda.isSeparatedFor.ext fun Y u hu ↦ ?_
    simpa using congr($(ha u hu).fst)
  · intro Y u hu
    obtain ⟨h₁, h₂⟩ := Total.ext_iff'.mp (ha u hu)
    simp only [toExtension, Total.mk] at h₂
    rw [← eqToIso.hom, ← Iso.op_hom, ← Functor.mapIso_hom, ← Iso.toEquiv_fun,
      ← Equiv.symm_apply_eq] at h₂
    simp_rw [← h₂, Equiv.eq_symm_apply, Types.extension_map, Total.comap_snd, Iso.toEquiv_fun,
      Functor.mapIso_hom, ← FunctorToTypes.map_comp_apply, Iso.op_hom, ← op_comp]
    exact congr_arg₂ _ (congr_arg _ (by simp)) rfl
  · obtain ⟨rfl, ha⟩ := ha
    intro Y u hu
    simp [← ha u hu, Total.comap]

end FamilyOfElements

variable {ℱ}

theorem of_sieveCompatible {X : C} {s : Sieve X}
    (isSheafFor_yoneda : Presieve.IsSheafFor (S.op ⋙ yoneda.obj T) s.arrows)
    (x : Presieve.FamilyOfElements (Types.extension ℱ) s.arrows)
    (hx : x.SieveCompatible) :
    ∃ (t : S.obj X ⟶ T) (x₀ : FamilyOfElements ℱ (mk t) s.arrows),
      x₀.toExtension = x ∧ x₀.Compatible := by
  obtain ⟨t, ht, htu⟩ := isSheafFor_yoneda (fun Y u hu ↦ (x u hu).fst) <|
    (Presieve.compatible_iff_sieveCompatible _).mpr fun Y Z f g hf ↦ by
      simpa [Between.toHom, Between.fst, Between.snd, Between.terminalFiber,
        Functor.Fiber.fiberInclusion] using congr($(hx f g hf).fst)
  change Sieve ((proj S T).obj (mk t)) at s
  have ht₁ {Y} (u : Y ⟶ X) (hu : s u) : S.map u ≫ t = (x u hu).fst := ht u hu
  refine ⟨t, fun Y u hu ↦ ℱ.map (eqToHom congr(mk $(ht u hu))).op (x u hu).2,
    funext₃ fun Y u hu ↦ Total.ext (ht u hu) ?_, fun {Y Z f} g hf ↦ ?_⟩
  · simp [FamilyOfElements.toExtension]
  · dsimp
    replace hx := hx _ g hf
    rw [Types.extension_map] at hx
    obtain ⟨hx₁, hx₂⟩ := Total.ext_iff'.mp hx
    dsimp only at hx₂
    simp_rw [hx₂, Total.comap_snd, ← FunctorToTypes.map_comp_apply, ← op_comp]
    exact congr_arg₂ _ (congr_arg _ (by simp)) rfl

@[simps] def sheafOfInduced (ℱ : Sheaf (inducedTopology S T K) (Type (max w v₂)))
    (isSheaf_yoneda : Presheaf.IsSheaf K (S.op ⋙ yoneda.obj T)) : Sheaf K (Type (max w v₂)) where
  val := Types.extension.{w} ℱ.val
  cond := by
    have isSheaf_F := ℱ.cond
    rw [isSheaf_iff_isSheaf_of_type] at isSheaf_F isSheaf_yoneda ⊢
    intro X s hs x hx
    rw [Presieve.compatible_iff_sieveCompatible] at hx
    obtain ⟨t, x, rfl, hx'⟩ := of_sieveCompatible (isSheaf_yoneda _ hs) _ hx
    change Sieve ((proj S T).obj (mk t)) at s
    obtain ⟨x₀, hx₀, hx₀'⟩ := @isSheaf_F (mk t) (s.functorPullback _)
      ((proj S T).functorPullback_mem_inducedTopologyEvil K hs)
      (x.equiv ℱ.val (mk t) s) (x.compatible_equiv_iff_compatible.mpr hx')
    rw [FamilyOfElements.isAmalgamation_equiv_iff] at hx₀
    refine ⟨.mk t x₀, ?_, ?_⟩
    · exact (FamilyOfElements.isAmalgamation_toExtension_iff (isSheaf_yoneda _ hs)).mpr
        ⟨rfl, by simpa using hx₀⟩
    · intro x₁ hx₁
      obtain ⟨rfl, hx₁⟩ :=
        (FamilyOfElements.isAmalgamation_toExtension_iff (isSheaf_yoneda _ hs)).mp hx₁
      exact Total.ext rfl <| hx₀' _ (FamilyOfElements.isAmalgamation_equiv_iff.mpr hx₁)

end CategoryTheory.CostructuredArrow

namespace CommRingCat

-- this shouldn't be in CommRingCat (?), but we put it here for now
/-- The category of affine schemes over a fixed base scheme `𝒮`. -/
abbrev OverScheme (𝒮 : Scheme.{u}) : Type (u + 1) :=
  CostructuredArrow Scheme.Spec 𝒮

instance : AffineScheme.Spec.IsEquivalence where

/-- The category of commutative rings under `R` is equivalent to
the opposite category of affine schemes over `Spec R`. -/
noncomputable def underEquivOverSpec (R : CommRingCat.{u}) :
    (CostructuredArrow AffineScheme.Spec (AffineScheme.of (Spec R)))ᵒᵖ ≌ Under R := by
  refine (costructuredArrowOpEquivalence _ _).trans ?_
  unfold Under
  -- #synth AffineScheme.Spec.op.IsEquivalence
  -- #check pre (op (AffineScheme.of (Spec R)))
  sorry


namespace OverScheme

variable (𝒮 : Scheme.{u})

@[simps!] noncomputable abbrev forget : OverScheme 𝒮 ⥤ CommRingCat.{u}ᵒᵖ :=
  CostructuredArrow.proj Scheme.Spec 𝒮

@[simps!] noncomputable nonrec
def zariskiTopology : GrothendieckTopology (OverScheme 𝒮) :=
  CostructuredArrow.inducedTopology _ _ zariskiTopology

end OverScheme

-- MOVE
instance hasLimitsOfShape_structuredArrow_op
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {T : Type u₃} [Category.{v₃} T] {S : C ⥤ D} {d : Dᵒᵖ}
    [HasColimitsOfShape (CostructuredArrow S d.unop) Tᵒᵖ] :
    HasLimitsOfShape (StructuredArrow d S.op) T := by
  obtain ⟨d⟩ := d
  have h₁ : HasColimitsOfShape (StructuredArrow (op d) S.op)ᵒᵖ Tᵒᵖ :=
    hasColimitsOfShape_of_equivalence (costructuredArrowOpEquivalence S d).rightOp
  exact hasLimitsOfShape_of_hasColimitsOfShape_op

instance hasLimitsOfShape_all_structuredArrow_op
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {T : Type u₃} [Category.{v₃} T] {S : C ⥤ D}
    [∀ d : D, HasColimitsOfShape (CostructuredArrow S d) Tᵒᵖ] :
    ∀ d : Dᵒᵖ, HasLimitsOfShape (StructuredArrow d S.op) T :=
  fun _ ↦ hasLimitsOfShape_structuredArrow_op

variable {𝒮 : Scheme.{u}}

theorem affine_subcanonical : Presheaf.IsSheaf zariskiTopology (Scheme.Spec.op ⋙ yoneda.obj 𝒮) :=
  ((Scheme.Spec.sheafPushforwardContinuous (Type u) zariskiTopology Scheme.zariskiTopology).obj
    (Scheme.zariskiTopology.yoneda.obj 𝒮)).cond

@[simps!] noncomputable def sheafOfOverScheme
    (S : Sheaf (OverScheme.zariskiTopology 𝒮) (Type (max w u))) :
    Sheaf zariskiTopology (Type (max w u)) :=
  CostructuredArrow.sheafOfInduced _ S affine_subcanonical

end CommRingCat

/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import EllipticCurve.Grassmannians.BigAffineZariski
import Mathlib.CategoryTheory.Limits.Types.Shapes

/-!

# The Category of Commutative Rings Over a Scheme

Fix a scheme `X`. We define the category of commutative rings `R` equipped with a morphism
`Spec R ⟶ X`.

-/

universe u

open CategoryTheory AlgebraicGeometry Opposite Limits

namespace CommRingCat

abbrev OverScheme (X : Scheme.{u}) : Type (u + 1) :=
  CostructuredArrow Scheme.Spec X

namespace OverScheme

variable (X : Scheme.{u})

@[simps!] noncomputable abbrev forget : OverScheme X ⥤ CommRingCat.{u}ᵒᵖ :=
  CostructuredArrow.proj Scheme.Spec X

variable {X}

abbrev mk {R : CommRingCat.{u}} (f : Spec R ⟶ X) : OverScheme X :=
  CostructuredArrow.mk f

abbrev homMk {R S : CommRingCat.{u}} {f : Spec R ⟶ X} {g : Spec S ⟶ X} (φ : R ⟶ S)
    (w : Spec.map φ ≫ f = g := by aesop_cat) :
    mk g ⟶ mk f :=
  CostructuredArrow.homMk φ.op w

abbrev homMk' {R : CommRingCat.{u}} (S : OverScheme X) (φ : S.left.unop ⟶ R) :
    mk (Spec.map φ ≫ S.hom) ⟶ S :=
  CostructuredArrow.homMk' S φ.op

@[simp] lemma homMk_id {R : CommRingCat.{u}} (f : Spec R ⟶ X)
    (w : Spec.map (𝟙 R) ≫ f = f) :
    homMk (𝟙 R) w = 𝟙 (mk f) :=
  rfl

@[simp] lemma homMk_comp_homMk {R S T : CommRingCat.{u}} {f : Spec R ⟶ X} {g : Spec S ⟶ X}
    {h : Spec T ⟶ X} (φ : R ⟶ S) (ψ : S ⟶ T)
    (w₁ : Spec.map φ ≫ f = g)
    (w₂ : Spec.map ψ ≫ g = h) :
    homMk ψ w₂ ≫ homMk φ w₁ = homMk (φ ≫ ψ) :=
  rfl

lemma hom_eta {R S : OverScheme X} (f : R ⟶ S) :
    homMk f.left.unop (CostructuredArrow.w f) = f :=
  rfl

lemma hom_eta' {R S : (OverScheme X)ᵒᵖ} (f : R ⟶ S) :
    (homMk f.unop.left.unop (CostructuredArrow.w f.unop)).op = f :=
  rfl

variable (F : (OverScheme X)ᵒᵖ ⥤ Type u)

abbrev fiberFun (R : CommRingCat.{u}) (u : Spec R ⟶ X) :=
  F.obj (op (mk u))

abbrev fiberCocone (R : CommRingCat.{u}) : Cofan (fiberFun F R) :=
  (Types.coproductColimitCocone (fiberFun F R)).cocone

@[simp] lemma fiberCocone_inj_fst {R : CommRingCat.{u}} (u : Spec R ⟶ X) (y : fiberFun F R u) :
    ((fiberCocone F R).inj u y).fst = u :=
  rfl

@[simp] lemma fiberCocone_inj_snd {R : CommRingCat.{u}} (u : Spec R ⟶ X) (y : fiberFun F R u) :
    ((fiberCocone F R).inj u y).snd = y :=
  rfl

abbrev fiberCoconeIsColimit (R : CommRingCat.{u}) : IsColimit (fiberCocone F R) :=
  (Types.coproductColimitCocone (fiberFun F R)).isColimit

abbrev FiberObj (R : CommRingCat.{u}) : Type u :=
  (fiberCocone F R).pt

noncomputable def fiberMap {R S : CommRingCat.{u}} (φ : R ⟶ S) (j : FiberObj F R) :
    FiberObj F S :=
  (fiberCocone F S).inj (Spec.map φ ≫ j.fst) (F.map (homMk φ).op j.snd)

lemma fiberMap_snd {R S : CommRingCat.{u}} (φ : R ⟶ S) (j : FiberObj F R) :
    (fiberMap F φ j).snd = F.map (homMk φ).op j.snd := rfl

@[ext] lemma FiberObj.ext {R : CommRingCat.{u}} {j j' : FiberObj F R}
    (h₁ : j.fst = j'.fst) (h₂ : ∀ h : j.fst = j'.fst,
      F.map (homMk (𝟙 _) (by rw [Spec.map_id]; exact h)).op j.snd = j'.snd) :
    j = j' := by
  cases j; cases j'; subst h₁
  specialize h₂ rfl
  rw [homMk_id, op_id, F.map_id] at h₂
  subst h₂; rfl

lemma fiberMap_id (R : CommRingCat.{u}) (j : FiberObj F R) :
    fiberMap F (𝟙 R) j = j := by
  ext h
  · change Spec.map (𝟙 R) ≫ j.fst = j.fst
    rw [Spec.map_id, Category.id_comp]
  · rw [fiberMap_snd, ← FunctorToTypes.map_comp_apply, ← op_comp, homMk_comp_homMk]
    generalize_proofs h'; revert h'; rw [Category.id_comp]; intro h'
    rw [homMk_id, op_id, F.map_id, types_id_apply]

variable (X) in
abbrev Between (R : CommRingCat.{u}) : Type (u + 1) :=
  CostructuredArrow (forget X).leftOp R

abbrev Between.fst {R : CommRingCat.{u}} (j : Between X R) : OverScheme X :=
  j.left.unop

variable (X) in
@[simps!] noncomputable abbrev Between.proj (R : CommRingCat.{u}) :
    Between X R ⥤ (OverScheme X)ᵒᵖ :=
  CostructuredArrow.proj (forget X).leftOp R

abbrev Between.snd {R : CommRingCat.{u}} (j : Between X R) : j.fst.left.unop ⟶ R :=
  j.hom

noncomputable abbrev Between.specHom {R : CommRingCat.{u}} (j : Between X R) : Spec R ⟶ X :=
  Spec.map j.snd ≫ j.fst.hom

lemma Between.w {R : CommRingCat.{u}} {j k : Between X R} (f : j ⟶ k) :
    f.left.unop.left.unop ≫ k.snd = j.snd :=
  CostructuredArrow.w f

lemma Between.w' {R : CommRingCat.{u}} {j k : Between X R} (f : j ⟶ k) :
    Spec.map f.left.unop.left.unop ≫ j.fst.hom = k.fst.hom :=
  CostructuredArrow.w f.left.unop

lemma Between.specHom_congr {R : CommRingCat.{u}} {j k : Between X R} (f : j ⟶ k) :
    j.specHom = k.specHom := by
  rw [specHom, ← w f, Spec.map_comp, Category.assoc, specHom, ← w' f]

noncomputable def Between.mk {R S : CommRingCat.{u}} (f : Spec S ⟶ X) (g : S ⟶ R) : Between X R :=
  CostructuredArrow.mk (Y := op (OverScheme.mk f)) g

noncomputable def Between.sec {R : CommRingCat.{u}} (u : Spec R ⟶ X) : Between X R :=
  mk u (𝟙 R)

noncomputable def Between.homSec {R : CommRingCat.{u}} (b : Between X R) :
    b ⟶ sec b.specHom :=
  CostructuredArrow.homMk (homMk b.snd).op

@[simps!] noncomputable def kanCocone (R : CommRingCat.{u}) :
    Cocone (Between.proj X R ⋙ F) where
  pt := FiberObj F R
  ι :=
  { app j y := (fiberCocone F R).inj j.specHom (F.map (homMk j.snd).op y)
    naturality j k f := funext fun y ↦ by
      refine FiberObj.ext _ ?_ fun h : k.specHom = j.specHom ↦ ?_
      · simp [Between.specHom_congr f]
      · change F.map _ (F.map _ (F.map f.left _)) = F.map _ _
        rw [← hom_eta' f.left]
        simp_rw [← FunctorToTypes.map_comp_apply, ← op_comp, homMk_comp_homMk]
        congr! 3
        rw [Category.comp_id, Between.w f] }

noncomputable def kanCoconeIsColimit (R : CommRingCat.{u}) : IsColimit (kanCocone F R) where
  desc c j := c.ι.app (.sec j.fst) j.snd
  fac c b := c.ι.naturality b.homSec
  uniq c f w := funext fun ⟨j₁, j₂⟩ ↦ by
    have := congrFun (w (Between.sec j₁)) j₂
    simp at this

instance : (forget X).leftOp.HasPointwiseLeftKanExtension F := by
  intro R; unfold Functor.HasPointwiseLeftKanExtensionAt; infer_instance

#check (forget X).leftOp.pointwiseLeftKanExtension F

noncomputable def fiber : CommRingCat.{u} ⥤ Type u where
  obj R := (u : Spec R ⟶ X) × F.obj (op (mk u))
  map φ j := ⟨Spec.map φ ≫ j.fst, F.map (homMk φ).op j.snd⟩
  map_id R := funext fun j ↦ by cases j; simp_rw [Spec.map_id]
  map_comp := _

end OverScheme

end CommRingCat

/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import EllipticCurve.CategoryTheory.FiberColimit
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Limits.Types.Shapes

/-!

# Left Kan Extension of Presheaf on Costructured Arrow

Let `F : C ⥤ D` be a functor and `d : D`. Recall that the category `CostructuredArrow F d` is the
category of objects `c` in `C` equipped with a morphism `F.obj c ⟶ d`.

In this file we show that any functor `P : (CostructuredArrow F d)ᵒᵖ ⥤ Type u` has a left Kan
extension along the projection `CostructuredArrow F d ⥤ C` to form a functor `P' : Cᵒᵖ ⥤ Type u`.

In other words, any presheaf on `CostructuredArrow F d` can be extended to a presheaf on `C`.

Explicitly, `P'.obj (op c)` is defined to be `(u : F.obj c ⟶ d) × P.obj (op (mk u))`. In other
words, we just take all possible morphisms `u : F.obj c ⟶ d` and take the disjoint union of the
original functor `P` evaluated on those morphisms.
-/

universe w v v₁ v₂ v₃ u u₁ u₂ u₃

open CategoryTheory Opposite Limits Category

namespace CategoryTheory.CostructuredArrow

variable {C : Type u} {D : Type u₁} [Category.{v} C] [Category.{v₁} D] (F : C ⥤ D) (d : D)
  {T : Type u₂} [Category.{v₂} T]
  (coprod : ∀ {c : C} {d : D} {f : Discrete (F.obj c ⟶ d) → T}, ColimitCocone (Discrete.functor f))
  (P : (CostructuredArrow F d)ᵒᵖ ⥤ T)
  (d₁ d₂ d₃ : D) {c c₁ c₂ c₃ : C} (c' c₁' c₂' c₃' : Cᵒᵖ)
  (u : F.obj c ⟶ d)

variable {F d P}

variable (F d) in
/-- An intermediate category used for proving the Kan criterion.

An object of this category is given by `b : C` and two morphisms that fill in the diagram
`F.obj c ⟶ F.obj b ⟶ d`, where `c : C` and `d : D` are fixed.

Note that we need to take the opposite category so that `c ⟶ b` is in the correct direction.

This category can be partitioned into disjoint parts based on the "structural morphism"
`F.obj c ⟶ d` obtained (this is `Between.toHom`). This fact is witnessed by `Between.toHom_congr`
saying that the existence of any morphism at all between two objects forces the structural
morphisms to be equal, and also by `Between.sec` which provides an explicit representative in the
`Between` category given a structural morphism `F.obj c ⟶ d`. -/
abbrev Between : Type _ :=
  CostructuredArrow (proj F d).op c'

variable {c'} (b : Between F d c') {b₁ b₂ b₃ : Between F d c'}

/-- The projection that sends `F.obj c ⟶ F.obj b ⟶ d` to the arrow `F.obj b ⟶ d`. -/
abbrev Between.fst : CostructuredArrow F d :=
  b.left.unop

variable (F d c') in
/-- The projection `Between.fst` as a functor. This is the functor that is used in the criterion
of the existence of a Kan extension. -/
@[simps!] abbrev Between.proj : Between F d c' ⥤ (CostructuredArrow F d)ᵒᵖ :=
  CostructuredArrow.proj (CostructuredArrow.proj F d).op c'

/-- The projection that sends `F.obj c ⟶ F.obj b ⟶ d` to the arrow `c ⟶ b`. -/
abbrev Between.snd : c'.unop ⟶ b.fst.left :=
  b.hom.unop

/-- The structural morphism `F.obj c ⟶ d` determined by `b`. -/
abbrev Between.toHom : F.obj c'.unop ⟶ d :=
  F.map b.snd ≫ b.fst.hom

lemma Between.w (f : b₁ ⟶ b₂) :
    b₂.snd ≫ f.left.unop.left = b₁.snd :=
  congr($(CostructuredArrow.w f).unop)

lemma Between.w' (f : b₁ ⟶ b₂) :
    F.map f.left.unop.left ≫ b₁.fst.hom = b₂.fst.hom :=
  CostructuredArrow.w f.left.unop

/-- The functor from `Between` to a discrete category. -/
@[simps] abbrev Between.toDiscrete : Between F d c' ⥤ Discrete (F.obj c'.unop ⟶ d) where
  obj b := ⟨b.toHom⟩
  map {b₁ b₂} f := eqToHom <| congrArg _ <| by
    rw [toHom, ← w f, F.map_comp, assoc, w' f]

/-- A custom constructor for `Between` objects given `g : c ⟶ b` and `f : F.obj b ⟶ d`. -/
def Between.mk (f : F.obj c ⟶ d) (g : c'.unop ⟶ c) : Between F d c' :=
  CostructuredArrow.mk (Y := op (CostructuredArrow.mk f)) g.op

/-- An explicit representative of the disjoint partition given the structural morphism
`u : F.obj c ⟶ d`. -/
def Between.sec (u : Discrete (F.obj c'.unop ⟶ d)) : Between F d c' :=
  mk u.as (𝟙 c'.unop)

@[simp] lemma Between.sec_snd (u : Discrete (F.obj c'.unop ⟶ d)) : (sec u).snd = 𝟙 c'.unop := rfl

-- @[simp] lemma Between.sec_hom (u : F.obj c'.unop ⟶ d) : (sec u).hom = 𝟙 c' := rfl

@[simp] lemma Between.toHom_mk (f : F.obj c ⟶ d) (g : c'.unop ⟶ c) :
    (mk f g).toHom = F.map g ≫ f := rfl

@[simp] lemma Between.toDiscrete_obj_sec (u : Discrete (F.obj c'.unop ⟶ d)) :
    toDiscrete.obj (sec u) = u := by
  ext; simp [sec]

/-- The representative `sec` is terminal in its subcategory.

More rigorously, for any `b : Between`, the type of morphisms `b ⟶ sec b.toHom` is a subsingleton,
i.e. it is either empty or has a unique element. -/
def Between.homSec : b ⟶ sec (toDiscrete.obj b) :=
  homMk (homMk b.snd).op (comp_id _)

/-- Each fiber has an explicit terminal object. -/
def Between.terminalFiber (u : Discrete (F.obj c'.unop ⟶ d)) : Between.toDiscrete.Fiber u :=
  ⟨.sec u, toDiscrete_obj_sec u⟩

instance (u : Discrete (F.obj c'.unop ⟶ d)) : Subsingleton (b ⟶ Between.sec u) where
  allEq f g := hom_ext _ _ <| unop_injective <| hom_ext _ _ <| by
    simpa using (Between.w f).trans (Between.w g).symm

instance (u : Discrete (F.obj c'.unop ⟶ d)) (b) : Subsingleton (b ⟶ Between.terminalFiber u) where
  allEq _ _ := Functor.Fiber.hom_ext <| Subsingleton.elim (α := _ ⟶ Between.sec u) _ _

def Between.terminalFiberIsTerminal (u : Discrete (F.obj c'.unop ⟶ d)) :
    IsTerminal (Between.terminalFiber u) :=
  .ofUniqueHom (fun b ↦ Functor.fiberPreimage _ _ _ <| homSec b.1 ≫ eqToHom (congrArg sec b.2))
    fun _ _ ↦ Subsingleton.elim _ _

variable (P c')

/-- The cocone that is used in the criterion of the existence of a left Kan extension of `P`
to a sheaf `Cᵒᵖ ⥤ Type u`. -/
@[simps!] def kanCocone : Cocone (Between.proj F d c' ⋙ P) :=
  coconeOfFiber Between.toDiscrete _
    (fun u ↦ coconeOfDiagramTerminal (Between.terminalFiberIsTerminal u) _) coprod.cocone

/-- The cocone that is used in the criterion of the existence of a left Kan extension of `P`
to a sheaf `Cᵒᵖ ⥤ Type u` is a colimit. -/
def kanCoconeIsColimit : IsColimit (kanCocone coprod P c') :=
  colimitOfFiber _ _ _ _ (fun _ ↦ colimitOfDiagramTerminal _ _) coprod.isColimit

section
variable {C D H : Type*} [Category C] [Category D] [Category H] (L : C ⥤ D) (F : C ⥤ H)
  (cocone : ∀ Y, Cocone (proj L Y ⋙ F)) (colimit : ∀ Y, IsColimit (cocone Y))

open Functor

@[simps] def _root_.CategoryTheory.Functor.pointwiseLeftKanExtension' :
    D ⥤ H where
  obj Y := (cocone Y).pt
  map {Y₁ Y₂} f := (colimit Y₁).desc
    { pt := (cocone Y₂).pt
      ι :=
      { app := fun g ↦ (cocone Y₂).ι.app ((map f).obj g)
        naturality g₁ g₂ φ := by simpa using (cocone Y₂).w ((map f).map φ) } }
  map_id Y := (colimit Y).hom_ext fun g ↦ by
    dsimp
    simp only [IsColimit.fac, comp_id]
    congr
    exact map_id
  map_comp {Y₁ Y₂ Y₃} f g := (colimit Y₁).hom_ext fun b ↦ by
    dsimp
    simp only [IsColimit.fac, IsColimit.fac_assoc, Functor.comp_obj, CostructuredArrow.proj_obj]
    congr 1
    exact map_comp

@[simps] def _root_.CategoryTheory.Functor.pointwiseLeftKanExtensionUnit' :
    F ⟶ L ⋙ pointwiseLeftKanExtension' L F cocone colimit where
  app X := (cocone (L.obj X)).ι.app (mk (𝟙 (L.obj X)))
  naturality {X₁ X₂} f := by
    simp only [comp_obj, pointwiseLeftKanExtension'_obj, Functor.comp_map,
      pointwiseLeftKanExtension'_map, IsColimit.fac, CostructuredArrow.map_mk]
    rw [id_comp]
    let φ : CostructuredArrow.mk (L.map f) ⟶ CostructuredArrow.mk (𝟙 (L.obj X₂)) :=
      CostructuredArrow.homMk f
    exact (cocone (L.obj X₂)).w φ

def _root_.CategoryTheory.Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension' :
    LeftExtension.mk _ (pointwiseLeftKanExtensionUnit' L F cocone colimit)
      |>.IsPointwiseLeftKanExtension :=
  fun X => IsColimit.ofIsoColimit (colimit _) (Cocones.ext (Iso.refl _) (fun j => by
    dsimp
    simp only [comp_id, IsColimit.fac, CostructuredArrow.map_mk]
    congr 1
    rw [id_comp, ← CostructuredArrow.eq_mk]))

/-- The functor `pointwiseLeftKanExtension L F` is a left Kan extension of `F` along `L`. -/
def _root_.CategoryTheory.Functor.pointwiseLeftKanExtensionIsUniversal' :
    (LeftExtension.mk _ (pointwiseLeftKanExtensionUnit' L F cocone colimit)).IsUniversal :=
  (pointwiseLeftKanExtensionIsPointwiseLeftKanExtension' L F cocone colimit).isUniversal

end

@[simps!] def extension : Cᵒᵖ ⥤ T :=
  Functor.pointwiseLeftKanExtension' _ _ (kanCocone coprod P) (kanCoconeIsColimit coprod P)

@[simps!] def extensionUnit : P ⟶ (proj F d).op ⋙ extension coprod P :=
  Functor.pointwiseLeftKanExtensionUnit' _ _ (kanCocone coprod P) (kanCoconeIsColimit coprod P)

@[simps! hom_app right_map] def leftExtension : (proj F d).op.LeftExtension P :=
  .mk (extension coprod P) (extensionUnit coprod P)

def isPointwiseLeftKanExtension : (leftExtension coprod P).IsPointwiseLeftKanExtension :=
  Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension' _ _ (kanCocone coprod P)
    (kanCoconeIsColimit coprod P)

def isUniversalLeftExtension : (leftExtension coprod P).IsUniversal :=
  Functor.pointwiseLeftKanExtensionIsUniversal' _ _ (kanCocone coprod P)
    (kanCoconeIsColimit coprod P)

instance : (proj F d).op.HasPointwiseLeftKanExtension P :=
  fun c' ↦ (isPointwiseLeftKanExtension coprod P c').hasPointwiseLeftKanExtensionAt

section Types

/-! # Explicit coproducts for types -/

variable {C : Type u} {D : Type u₁} [Category.{v} C] [Category.{v₁} D] {F : C ⥤ D} {d : D}
  (P : (CostructuredArrow F d)ᵒᵖ ⥤ Type (max w v₁))

def Total (X : C) : Type (max w v₁) :=
  Σ x : F.obj X ⟶ d, P.obj (op (mk x))

namespace Total

variable {P}

@[simps] def mk {X : C} (x : F.obj X ⟶ d) (px : P.obj (op (mk x))) : Total P X := ⟨x, px⟩

@[ext (iff := false)] theorem ext {X : C} {x₁ x₂ : Total P X} (h₁ : x₁.1 = x₂.1)
    (h₂ : P.map (eqToHom (by rw [h₁])).op x₁.2 = x₂.2) : x₁ = x₂ := by
  cases x₁; cases x₂; dsimp at h₁; subst h₁; dsimp at h₂; subst h₂; simp

theorem ext_iff {X : C} {x₁ x₂ : Total P X} :
    x₁ = x₂ ↔ ∃ h : x₁.1 = x₂.1, P.map (eqToHom (by rw [h])).op x₁.2 = x₂.2 :=
  ⟨(by subst ·; simp), fun ⟨h₁, h₂⟩ ↦ ext h₁ h₂⟩

theorem ext_iff' {X : C} {x₁ x₂ : Total P X} :
    x₁ = x₂ ↔ ∃ h : x₁.1 = x₂.1, x₁.2 = P.map (eqToHom (by rw [h])).op x₂.2 :=
  ⟨(by subst ·; simp), fun ⟨h₁, h₂⟩ ↦ (ext h₁.symm h₂.symm).symm⟩

@[simps!] def comap {X Y : C} (f : X ⟶ Y) (t : Total P Y) : Total P X :=
  mk (F.map f ≫ t.1) (P.map (homMk f).op t.2)

lemma comap_id {X : C} : comap (P := P) (𝟙 X) = id := by
  refine funext fun p ↦ ext (by simp) ?_
  change P.map _ (P.map _ p.snd) = p.snd
  rw [← FunctorToTypes.map_comp_apply, ← op_comp]
  conv => enter [2]; exact (FunctorToTypes.map_id_apply P p.snd).symm
  exact congr_arg₂ _ (congr_arg _ (by simp)) rfl

lemma comap_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} :
    comap (P := P) (f ≫ g) = comap f ∘ comap g := by
  refine funext fun p ↦ ext (by simp) ?_
  change P.map _ (P.map _ p.snd) = P.map _ (P.map _ p.snd)
  simp_rw [← FunctorToTypes.map_comp_apply, ← op_comp]
  exact congr_arg₂ _ (congr_arg _ (by simp)) rfl

end Total

@[simps] def Types.extension : Cᵒᵖ ⥤ Type (max w v₁) where
  obj X := Total P X.unop
  map f := Total.comap f.unop
  map_id _ := Total.comap_id
  map_comp _ _ := Total.comap_comp

def Types.extensionUnit : P ⟶ (proj F d).op ⋙ Types.extension P where
  app X p := .mk X.unop.hom (P.map (eqToHom (by rw [← eq_mk])).op p)
  naturality X Y f := funext fun p ↦ Total.ext (by simp) <| by
    dsimp
    rw [← Quiver.Hom.op_unop f]
    simp_rw [← FunctorToTypes.map_comp_apply, ← op_id, ← op_comp]
    exact congr_arg₂ _ (congr_arg _ (by simp)) rfl

-- @[simps!] nonrec def Types.leftExtension : (proj F d).op.LeftExtension P :=
--   leftExtension (Types.coproductColimitCocone _) P

-- @[simps!] nonrec def Types.isPointwiseLeftKanExtension :
--     (Types.leftExtension F d P).IsPointwiseLeftKanExtension :=
--   isPointwiseLeftKanExtension _ _

-- @[simps!] nonrec def Types.isUniversalLeftExtension :
--     (Types.leftExtension F d P).IsUniversal :=
--   isUniversalLeftExtension _ _

end Types

-- noncomputable example := (proj F d).op.pointwiseLeftKanExtension P

-- #check proj F d ⋙ yoneda
-- #check yoneda (C := CostructuredArrow F d)

-- def leftExtensionYoneda : yoneda.LeftExtension (proj F d ⋙ yoneda) :=
--   .mk _ _

end CategoryTheory.CostructuredArrow

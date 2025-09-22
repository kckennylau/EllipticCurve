/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.PUnit

/-!

# Computing Colimits Fiberwise

In this file, we consider category `J` equipped with a functor `F : J ⥤ D` to a discrete category
`D`. Then the colimit of any diagram `diagram : J ⥤ C` can be computed fiberwise, using the
following algorithm:

1. For each `d : D`, construct a cocone over the restricted diagram `fiberInclusion F d ⋙ diagram`.
2. Take a cofan of the values of these cocones over all `d : D`.

## Main Results

- `colimitOfFiber`: As above, given colimits on each restriction, and coproduct of the values, this
  gives the colimit of the original diagram `diagram`.

-/

universe v u₁ v₁ v₂ u u₂

open CategoryTheory Functor Category Limits CategoricalPullback

variable {J : Type u} {D : Type u₁}
  [Category.{v} J] [Category.{v₁} D] [IsDiscrete D]
  (F : J ⥤ D)
  {C : Type u₂} [Category.{v₂} C] (diagram : J ⥤ C)

namespace CategoryTheory

namespace Functor

abbrev Fibre (d : D) : Type (max u v₁) :=
  CategoricalPullback F (fromPUnit.{0} d)

theorem fibreCongr {j₁ j₂ : J} (f : j₁ ⟶ j₂) : F.obj j₁ = F.obj j₂ :=
  IsDiscrete.eq_of_hom (F.map f)

abbrev fibreIncl (d : D) : F.Fibre d ⥤ J :=
  π₁ _ _

variable (d : D) (j j₁ j₂ : J)

variable {d j} in
theorem Fibre.eq (x : F.Fibre d) : F.obj x.1 = d :=
  IsDiscrete.eq_of_hom x.3.hom

abbrev Fibre.mk (h : F.obj j = d) : F.Fibre d where
  fst := j
  snd := default
  iso := eqToIso h

abbrev Fibre.mk' : F.Fibre (F.obj j) :=
  .mk _ _ _ rfl

/-- Casting a morphism in `J` to a morphism in the category `F.Fibre d`. -/
def homMk {d : D} {j₁ j₂ : F.Fibre d} (f : j₁.1 ⟶ j₂.1) : j₁ ⟶ j₂ where
  fst := f
  snd := eqToHom <| Subsingleton.elim _ _

/-- The inclusion functor from `F.Fibre d` to `J` is fully faithful when `D` is discrete. -/
def fullyFaithfulFibreIncl (d : D) : FullyFaithful (F.fibreIncl d) where
  preimage := F.homMk

instance (d : D) : Full (F.fibreIncl d) :=
  (fullyFaithfulFibreIncl F d).full

instance (d : D) : Faithful (F.fibreIncl d) :=
  (fullyFaithfulFibreIncl F d).faithful

@[elab_as_elim] lemma fibre_inductionOn {motive : ∀ {j₁ j₂ : J}, (j₁ ⟶ j₂) → Prop}
    {j₁ j₂ : J} (f : j₁ ⟶ j₂)
    (ih : ∀ d : D, ∀ {j₁ j₂ : F.Fibre d} (f : j₁ ⟶ j₂), motive f.1) :
    motive f :=
  ih (F.obj j₂) (F.homMk (j₁ := .mk F (F.obj j₂) j₁ (F.fibreCongr f)) (j₂ := .mk' F j₂) f)

variable {F d} in
@[elab_as_elim] lemma Fibre.mk_casesOn {motive : F.Fibre d → Prop}
    (x : F.Fibre d) (ih : ∀ (j : J) (h : F.obj j = d), motive (.mk F d j h)) :
    motive x := by
  obtain ⟨j, ⟨⟨⟩⟩, e⟩ := x
  convert ih j (IsDiscrete.eq_of_hom e.hom)
  subsingleton

end Functor

namespace Limits

open Functor

variable (fiberwiseCocone : ∀ d : D, Cocone (F.fibreIncl d ⋙ diagram))
  (cofan : Cofan fun d : D ↦ (fiberwiseCocone d).pt)

/-- Given a functor `F : J ⥤ D` to a discrete category `D`, and a diagram `diagram : J ⥤ C`,
we can construct a cocone over `diagram` using the following algorithm:

1. For each `d : D`, construct a cocone over the restricted diagram `fiberInclusion F d ⋙ diagram`.
2. Take a cofan of the values of these cocones over all `d : D`.
-/
@[simps] def coconeOfFiber : Cocone diagram where
  pt := cofan.pt
  ι :=
  { app j := (fiberwiseCocone (F.obj j)).ι.app (.mk' F j) ≫ cofan.inj (F.obj j)
    naturality j₁ j₂ f := by
      simp only [const_obj_obj, const_obj_map, comp_id]
      refine F.fibre_inductionOn f fun d j₁ j₂ f ↦ ?_
      rw [← (fiberwiseCocone (F.obj j₁.1)).w (F.homMk (j₁ := .mk' F j₁.1)
        (j₂ := .mk F _ _ (j₂.eq.trans j₁.eq.symm)) f.1), Functor.comp_map, assoc]
      congr 1
      suffices h : (fiberwiseCocone d).ι.app (.mk F d j₂.1 j₂.eq) ≫ cofan.inj d =
          (fiberwiseCocone d).ι.app (.mk F d j₂.1 j₂.eq) ≫ cofan.inj d by
        convert h using 1
        · refine j₂.mk_casesOn fun j₂ ↦ ?_
          rintro rfl; rfl
        · refine j₁.mk_casesOn fun j₁ ↦ ?_
          rintro rfl; rfl
      rfl }

variable (fiberwiseColimit : ∀ d : D, IsColimit (fiberwiseCocone d))
  (colimitCofan : IsColimit cofan)

/-- Given a functor `F : J ⥤ D` to a discrete category, the colimit of any diagram `J ⥤ C` can
be computed using this algorithm:

1. For each `d : D`, compute the colimit of the restricted diagram `fiberInclusion F d ⋙ diagram`.
2. Take the coproduct of these colimits over all `d : D`.
-/
@[simps] def colimitOfFiber : IsColimit (coconeOfFiber F diagram fiberwiseCocone cofan) where
  desc c := Cofan.IsColimit.desc colimitCofan fun d ↦ (fiberwiseColimit d).desc
    (c.whisker (F.fibreIncl d))
  uniq c s w := by
    refine Cofan.IsColimit.hom_ext colimitCofan _ _ fun d ↦
      (fiberwiseColimit d).hom_ext fun j ↦ ?_
    rw [Cofan.IsColimit.fac, IsColimit.fac, Cocone.whisker_ι, whiskerLeft_app, ← w,
      coconeOfFiber_ι_app, assoc]
    refine j.mk_casesOn fun j ↦ ?_
    rintro rfl; rfl

-- Not an instance because `D` cannot be inferred.
theorem hasColimit_of_fiber [∀ d, HasColimit (F.fibreIncl d ⋙ diagram)]
    [h : HasColimit (Discrete.functor fun d ↦
      colimit (F.fibreIncl d ⋙ diagram))] :
    HasColimit diagram :=
  ⟨⟨⟨_, colimitOfFiber F diagram _ _
    (fun d ↦ colimit.isColimit (F.fibreIncl d ⋙ diagram))
    (coproductIsCoproduct fun d ↦ colimit (F.fibreIncl d ⋙ diagram))⟩⟩⟩

-- Not an instance because `D` cannot be inferred.
theorem hasColimitOfShapes_of_fiber
    [∀ d, HasColimitsOfShape (F.Fibre d) C] [HasCoproductsOfShape D C] :
    HasColimitsOfShape J C :=
  ⟨fun diagram ↦ hasColimit_of_fiber F diagram⟩

end Limits

end CategoryTheory

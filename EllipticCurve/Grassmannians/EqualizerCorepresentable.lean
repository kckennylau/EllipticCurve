/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Yoneda

/-!
# Equalizer of Corepresentable Functors

In this file we show that the equalizer of two corepresentable functors is also corepresentable.
-/

universe v u w

open CategoryTheory in
/-- Any diagram from `WalkingParallelPair` is isomorphic to a `parallelPair`. -/
def CategoryTheory.Limits.parallelPair_eta {C : Type u} [Category.{v} C]
    (F : WalkingParallelPair ⥤ C) :
    F ≅ parallelPair (F.map WalkingParallelPairHom.left) (F.map WalkingParallelPairHom.right) :=
  parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp)

namespace CategoryTheory.Functor

open Limits Opposite Category

variable {C : Type u} [Category.{v} C] {F G : C ⥤ Type v} {X Y : C}
  (hf : F.CorepresentableBy X) (hg : G.CorepresentableBy Y)

/-- A natural transformation `F ⟶ G` between two corepresentable functors is itself corepresented
by a morphism `Y ⟶ X`. -/
abbrev CorepresentableBy.homOfNatTrans (u : F ⟶ G) : Y ⟶ X :=
  hg.homEquiv.symm (u.app X (hf.homEquiv (𝟙 X)))

lemma CorepresentableBy.homOfNatTrans_comp {Z : C} (u : F ⟶ G) (f : X ⟶ Z) :
    hf.homOfNatTrans hg u ≫ f = hg.homEquiv.symm (u.app Z (hf.homEquiv f)) := by
  rw [homOfNatTrans, homEquiv_symm_comp, ← FunctorToTypes.naturality, ← hf.homEquiv_comp, id_comp]

variable {u v : F ⟶ G} {E : Fork u v} (he : IsLimit E)

-- We're stuck with noncomputable here because `evaluation_preservesLimit` has the wrong proof.
/-- Recovers the concrete definition when `Z'` is `PUnit`. -/
noncomputable def _root_.CategoryTheory.Limits.IsLimit.punitPiEquiv (Z : C) (Z' : Type v) :
    (Z' → E.pt.obj Z) ≃ { x : Z' → F.obj Z // u.app Z ∘ x = v.app Z ∘ x } :=
  Fork.IsLimit.homIso ((IsLimit.postcomposeHomEquiv (parallelPair_eta _) _).symm
    (isLimitOfPreserves ((evaluation C (Type v)).obj Z) he)) Z'

/-- A limit in the copresheaf category satisfies this equation at each point. -/
@[simps apply_coe] noncomputable def _root_.CategoryTheory.Limits.IsLimit.objEquiv (Z : C) :
    E.pt.obj Z ≃ { x : F.obj Z // u.app Z x = v.app Z x } where
  toFun y := ⟨E.ι.app Z y, congrFun congr(NatTrans.app $(E.condition) Z) y⟩
  invFun y := (he.punitPiEquiv Z PUnit).symm ⟨fun _ ↦ y.1, funext fun _ ↦ y.2⟩ default
  left_inv y := congrFun ((he.punitPiEquiv Z PUnit).left_inv (fun _ ↦ y)) default
  right_inv y := have h := (he.punitPiEquiv Z PUnit).right_inv ⟨fun _ ↦ y.1, funext fun _ ↦ y.2⟩;
    Subtype.ext <| congrFun congr(Subtype.val $h) default

/-- Naturality of `objEquiv`. -/
lemma _root_.CategoryTheory.Limits.IsLimit.objEquiv_map {Z W : C} (f : Z ⟶ W) (y : E.pt.obj Z) :
    (he.objEquiv W (E.pt.map f y)).1 = F.map f (he.objEquiv Z y).1 := by
  rw [IsLimit.objEquiv_apply_coe, IsLimit.objEquiv_apply_coe]
  exact FunctorToTypes.naturality ..

/-- Naturality of `objEquiv`. -/
lemma _root_.CategoryTheory.Limits.IsLimit.map_objEquiv_symm {Z W : C} (f : Z ⟶ W)
    (y : { x : F.obj Z // u.app Z x = v.app Z x }) :
    E.pt.map f ((he.objEquiv Z).symm y) = (he.objEquiv W).symm ⟨F.map f y.1, by
        rw [FunctorToTypes.naturality, FunctorToTypes.naturality, y.2]⟩ := by
  rw [Equiv.eq_symm_apply, Subtype.ext_iff, IsLimit.objEquiv_map, Equiv.apply_symm_apply]

variable {E' : Cofork (hf.homOfNatTrans hg u) (hf.homOfNatTrans hg v)} (he' : IsColimit E')

/-- Let `F` and `G` be two corepresentable functors, corepresented by `X` and `Y` respectively.
Further let `u, v : F ⟶ G` be two natural transformations, corepresented by `u', v' : Y ⟶ X`
respectively. Finally let `E'` be a coequalizer of `u'` and `v'`. Then `E'` corepresents the
equalizer of `u` and `v`. -/
noncomputable def CorepresentableBy.equalizer : E.pt.CorepresentableBy E'.pt where
  homEquiv {Z} := calc
    (E'.pt ⟶ Z)
      ≃ { h : X ⟶ Z // hf.homOfNatTrans hg u ≫ h = hf.homOfNatTrans hg v ≫ h } :=
        Cofork.IsColimit.homIso he' Z
    _ ≃ { x : F.obj Z // u.app Z x = v.app Z x } := hf.homEquiv.subtypeEquiv fun f ↦ by
        rw [← hg.homEquiv.injective.eq_iff, hf.homOfNatTrans_comp, hf.homOfNatTrans_comp,
          Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    _ ≃ E.pt.obj Z := (he.objEquiv Z).symm
  homEquiv_comp {Z W} f x := by simp [he.map_objEquiv_symm, hf.homEquiv_comp]

end CategoryTheory.Functor

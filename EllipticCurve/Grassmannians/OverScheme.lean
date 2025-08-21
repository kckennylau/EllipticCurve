/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import EllipticCurve.Grassmannians.BigAffineZariski
import EllipticCurve.Grassmannians.PresheafCostructured

/-!
# The Category of Commutative Rings Over a Scheme

Fix a scheme `X`. We define the category of commutative rings `R` equipped with a morphism
`Spec R ⟶ X`.

We define a Grothendieck topology on `OverScheme X` and show that sheaves on `OverScheme X` extend
to sheaves on `CommRingCatᵒᵖ`.
-/

universe v v₁ v₂ u u₁ u₂

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

#print CommRingCat.sheafEquiv
#synth Scheme.Spec.IsCoverDense Scheme.zariskiTopology
#print IsCoverDense


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

variable {S T} in
def inducedTopology : GrothendieckTopology (CostructuredArrow S T) :=
  (proj S T).inducedTopologyEvil K

end CategoryTheory.CostructuredArrow

namespace CommRingCat

abbrev OverScheme (𝒮 : Scheme.{u}) : Type (u + 1) :=
  CostructuredArrow Scheme.Spec 𝒮

namespace OverScheme

variable (𝒮 : Scheme.{u})

@[simps!] noncomputable abbrev forget : OverScheme 𝒮 ⥤ CommRingCat.{u}ᵒᵖ :=
  CostructuredArrow.proj Scheme.Spec 𝒮

@[simps!] noncomputable nonrec
def zariskiTopology : GrothendieckTopology (OverScheme 𝒮) :=
  CostructuredArrow.inducedTopology zariskiTopology

end OverScheme

end CommRingCat

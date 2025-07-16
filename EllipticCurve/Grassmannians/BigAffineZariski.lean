/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology

/-!
# The Big Zariski Site on Affine Schemes

In this file we define the Zariski topology on the category of affine schemes.
-/

universe v u

open CategoryTheory Functor Opposite Category

namespace AlgebraicGeometry

namespace AffineScheme

open Scheme

instance : IsCoverDense forgetToScheme Scheme.zariskiTopology where
  is_cover X := ⟨.ofArrows X.affineCover.obj X.affineCover.map, ⟨X.affineCover, rfl⟩,
    fun _ u ⟨j⟩ ↦ ⟨⟨.of (X.affineCover.obj j), 𝟙 _, X.affineCover.map j, by rw [id_comp]⟩⟩⟩

/-- The Zariski topology on the category of affine schemes. -/
def zariskiTopology : GrothendieckTopology AffineScheme :=
  inducedTopology forgetToScheme Scheme.zariskiTopology

noncomputable def sheafEquiv :
    Sheaf AffineScheme.zariskiTopology (Type (u+1)) ≌
      Sheaf Scheme.zariskiTopology (Type (u+1)) :=
  sheafInducedTopologyEquivOfIsCoverDense _ _ _

end AffineScheme

end AlgebraicGeometry

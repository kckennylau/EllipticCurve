/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import EllipticCurve.ProjectiveSpace.TensorProduct.GradedAlgebra
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.GradedAlgebra.Basic

/-! # Proj of Tensor Product

In this file we show `Proj (S ⊗[R] 𝒜) ≅ Spec S ×_R Proj 𝒜` where `𝒜` is a graded `R`-algebra.
-/

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
  (S : Type u) [CommRing S] [Algebra R S]

namespace AlgebraicGeometry

open TensorProduct CategoryTheory Limits CommRingCat

-- def projTensorProduct : Proj (fun n ↦ (𝒜 n).baseChange S) ≅
--     pullback (Spec.map (ofHom (algebraMap R S))) (Spec.map (ofHom (algebraMap R A))) :=
--   _

end AlgebraicGeometry

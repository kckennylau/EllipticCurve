/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import EllipticCurve.ProjectiveSpace.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

/-!
# Models of Elliptic Curves over a Ring

We define elliptic curves over a ring from the Weierstrass equation. Note that not all "elliptic
curves" in the literature necessarily satisfy a Weierstrass cubic globally.

## Main definitions

* `FooBar`

-/

universe u

open CategoryTheory Module ProjectiveSpace SymmetricPower TensorProduct Ideal WeierstrassCurve

noncomputable section

namespace EllipticCurve.Ring

variable {R : CommRingCat.{u}} (W : Affine R)

/-- The "x-coordinate" as a section of `𝒪(1)` on `ℙ²`. -/
def X : Sym[R]^1 (Fin 3 → R) :=
  tprod R ![Pi.single 0 1]

def Y : Sym[R]^1 (Fin 3 → R) :=
  tprod R ![Pi.single 1 1]

def Z : Sym[R]^1 (Fin 3 → R) :=
  tprod R ![Pi.single 2 1]

section simp_lemmas

variable {M : Type*} [AddCommGroup M] [Module R M]

@[simp] lemma map_X (f : (Fin 3 → R) →ₗ[R] M) :
    SymmetricPower.map 1 f X = tprod R ![f (Pi.single 0 1)] := by
  simp only [X, Nat.succ_eq_add_one, map_tprod, ← Function.comp_def f, comp_vecCons, comp_vecEmpty]

@[simp] lemma map_Y (f : (Fin 3 → R) →ₗ[R] M) :
    SymmetricPower.map 1 f Y = tprod R ![f (Pi.single 1 1)] := by
  simp only [Y, Nat.succ_eq_add_one, map_tprod, ← Function.comp_def f, comp_vecCons, comp_vecEmpty]

@[simp] lemma map_Z (f : (Fin 3 → R) →ₗ[R] M) :
    SymmetricPower.map 1 f Z = tprod R ![f (Pi.single 2 1)] := by
  simp only [Z, Nat.succ_eq_add_one, map_tprod, ← Function.comp_def f, comp_vecCons, comp_vecEmpty]

end simp_lemmas

def _root_.WeierstrassCurve.Affine.asSym : Sym[R]^3 (Fin 3 → R) :=
  (Y ✱ Y ✱ Z + W.a₁ • X ✱ Y ✱ Z + W.a₃ • Y ✱ Z ✱ Z) -
  (X ✱ X ✱ X + W.a₂ • X ✱ X ✱ Z + W.a₄ • X ✱ Z ✱ Z + W.a₆ • Z ✱ Z ✱ Z)

-- To be replaced with scheme.
/-- We don't have the scheme yet, so we just use the functor `R-Alg ⥤ Type`. -/
def model : Under R ⥤ Type u :=
  zerosFunctor R (.of R (Fin 3 → R)) W.asSym

/-- The point at infinity -/
def infinity : zeros W.asSym :=
  zerosOfCoordinates _ ![0, 1, 0] ((eq_top_iff_one _).2 <| subset_span ⟨1, rfl⟩) <| by
    rw [evalSelf_coe']; simp [Affine.asSym]

end EllipticCurve.Ring

/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Projective Space as Scheme

## Main definitions

- `AlgebraicGeometry.ProjectiveSpace`: `ℙ(n; S)` is the projective `n`-space over a scheme `S`.

## TODO

- `AlgebraicGeometry.ProjectiveSpace.SpecIso`: `ℙ(n; Spec R) ≅ Proj R[n]`.
- `AlgebraicGeometry.ProjectiveSpace.openCover`: the canonical cover of `ℙ(n; S)` by `n` affine
  charts. The `i`ᵗʰ chart is `𝔸({k // k ≠ i}; S) ⟶ ℙ(n; S)`, and represents the open set where
  the function `Xᵢ` does not vanish.
- Functoriality of `ProjectiveSpace` on the `S` component.
- Show that a map `Spec A ⟶ ℙ(n; S)` corresponds to a map `p : Spec A ⟶ S` and a unique
  `A`-submodule `N` of `n →₀ A` such that `(n →₀ A) ⧸ N` is locally free of rank 1.
-/

-- Also see https://github.com/leanprover-community/mathlib4/pull/26061

universe u

open CategoryTheory Limits MvPolynomial HomogeneousLocalization

noncomputable section

namespace AlgebraicGeometry

variable (n : Type u) (S : Scheme.{u})

attribute [local instance] gradedAlgebra

/-- The structure of a graded algebra on `ℤ[n]`, i.e. on `MvPolynomial n (ULift.{u} ℤ)`. -/
local notation3 "ℤ[" n "].{" u "}" => homogeneousSubmodule n (ULift.{u} ℤ)

/-- `ℙ(n; S)` is the projective `n`-space over `S`.
Note that `n` is an arbitrary index type (e.g. `ULift (Fin m)`). -/
def ProjectiveSpace (n : Type u) (S : Scheme.{u}) : Scheme.{u} :=
  pullback (terminal.from S) (terminal.from (Proj ℤ[n].{u}))

@[inherit_doc] scoped notation "ℙ("n"; "S")" => ProjectiveSpace n S

namespace Proj

-- /-- The canonical affine open cover of `Proj (MvPolynomial σ R)`. The cover is indexed by `σ`,
-- and each `i : σ` corresponds to `Spec (MvPolynomial {k // k ≠ i} R)`. -/
-- @[simps!] def openCoverMvPolynomial (σ : Type*) (R : Type*) [CommRing R] :
--     (Proj (homogeneousSubmodule σ R)).AffineOpenCover :=
--   (openCoverOfISupEqTop
--       (homogeneousSubmodule σ R) .X (fun _ ↦ isHomogeneous_X _ _) (fun _ ↦ zero_lt_one)
--       (by rw [homogeneous_eq_span, Ideal.span_le, Set.range_subset_iff]; exact
--         fun i ↦ Ideal.subset_span <| Set.mem_range_self _)).copy
--     _ _ _
    -- (Equiv.refl σ) (.of <| MvPolynomial {k // k ≠ ·} R) (algEquivAway R · |>.toCommRingCatIso)

end Proj

-- /-- `ℙ(n; Spec R)` is isomorphic to `Proj R[n]`. -/
-- def SpecIso (R : Type u) [CommRing R] : ℙ(n; Spec (.of R)) ≅ Proj (homogeneousSubmodule n R) :=
--   _

end AlgebraicGeometry

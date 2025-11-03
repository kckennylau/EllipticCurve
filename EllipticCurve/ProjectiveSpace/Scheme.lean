/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import EllipticCurve.ProjectiveSpace.Graded.AlgEquiv
import EllipticCurve.ProjectiveSpace.TensorProduct.Proj
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.MvPolynomial.Homogeneous

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

open SpecOfNotation

variable (n : Type u) (S : Scheme.{u})

attribute [local instance] gradedAlgebra

/-- The structure of a graded algebra on `ℤ[n]`, i.e. on `MvPolynomial n (ULift.{u} ℤ)`. -/
local notation3 "ℤ[" n "].{" u "}" => homogeneousSubmodule n (ULift.{u} ℤ)

/-- `ℙ(n; S)` is the projective `n`-space over `S`.
Note that `n` is an arbitrary index type (e.g. `ULift (Fin m)`). -/
def ProjectiveSpace (n : Type u) (S : Scheme.{u}) : Scheme.{u} :=
  pullback (terminal.from S) (terminal.from (Proj ℤ[n].{u}))

@[inherit_doc] scoped notation "ℙ("n"; "S")" => ProjectiveSpace n S

instance _root_.ULift.algebraLeft {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] :
    Algebra (ULift R) A where
  algebraMap := (algebraMap R A).comp (ULift.ringEquiv (R := R))
  commutes' _ := Algebra.commutes _
  smul_def' _ := Algebra.smul_def _

@[simps] def _root_.CategoryTheory.Limits.pullback.mapIso {C : Type*} [Category C]
    {X₁ X₂ Y₁ Y₂ W₁ W₂ : C} {f₁ : X₁ ⟶ W₁} {g₁ : Y₁ ⟶ W₁} {f₂ : X₂ ⟶ W₂} {g₂ : Y₂ ⟶ W₂}
    [HasPullback f₁ g₁] [HasPullback f₂ g₂] (eX : X₁ ≅ X₂) (eY : Y₁ ≅ Y₂) (eW : W₁ ≅ W₂)
    (comm₁ : f₁ ≫ eW.hom = eX.hom ≫ f₂) (comm₂ : g₁ ≫ eW.hom = eY.hom ≫ g₂) :
    pullback f₁ g₁ ≅ pullback f₂ g₂ where
  hom := pullback.map _ _ _ _ eX.hom eY.hom eW.hom comm₁ comm₂
  inv := pullback.map _ _ _ _ eX.inv eY.inv eW.inv
    (by rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, comm₁])
    (by rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, comm₂])
  hom_inv_id := pullback.hom_ext (by simp) (by simp)
  inv_hom_id := pullback.hom_ext (by simp) (by simp)

def _root_.MvPolynomial.algebraTensorGAlgEquiv (R σ A : Type*)
    [CommRing R] [CommRing A] [Algebra R A] :
    (homogeneousSubmodule σ R).baseChange A ≃ₐᵍ[A] homogeneousSubmodule σ A where
  __ := MvPolynomial.algebraTensorAlgEquiv R A
  map_mem' {n x} hx := by
    obtain ⟨x, hx⟩ := Submodule.toBaseChange_surjective _ _ ⟨x, hx⟩
    replace hx := congr(($hx).val); subst hx
    simp only [AlgEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
      mem_homogeneousSubmodule]
    induction x with
    | zero => simp [isHomogeneous_zero]
    | add => simp [IsHomogeneous.add, *]
    | tmul a x => simpa [smul_eq_C_mul] using (x.2.map _).C_mul _

/-- `ℙ(n; Spec(R))` is isomorphic to `Proj R[n]`. -/
def SpecIso (R : Type u) [CommRing R] : ℙ(n; Spec(R)) ≅ Proj (homogeneousSubmodule n R) :=
  pullback.mapIso (Iso.refl _) (Iso.refl _) (terminalIsoIsTerminal specULiftZIsTerminal)
    (specULiftZIsTerminal.hom_ext ..) (specULiftZIsTerminal.hom_ext ..) ≪≫
  (projTensorProduct ℤ[n].{u} R).symm ≪≫
  Proj.congr (MvPolynomial.algebraTensorGAlgEquiv (ULift ℤ) n R)

end AlgebraicGeometry

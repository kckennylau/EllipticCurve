/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import EllipticCurve.Grassmannians.Basic
import EllipticCurve.ProjectiveSpace.TensorProduct.SymmetricPower

/-!
# Projective Space of a Module over a Ring

## Main definitions

* `ProjectiveSpace.functor`: the functor `R-Alg ⥤ Set` that sends `A` to `ℙ(A ⊗[R] M; A)`.
-/

universe u v w₁ w₂

namespace Module

namespace ProjectiveSpace

open CategoryTheory Grassmannian TensorProduct

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
  {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  [AddCommGroup M₃] [Module R M₃]
  (A : Type w₁) [CommRing A] [Algebra R A] (B : Type w₂) [CommRing B] [Algebra R B]
  (ι : Type*) [Fintype ι]

/-- The projective space corresponding to the module `M` is the space of submodules `N` such that
`M⧸N` is locally free of rank 1, i.e. invertible. -/
abbrev AsType := G(1, M; R)

@[inherit_doc] scoped notation "ℙ("M"; "R")" => AsType R M

/-- The functor `R-Alg ⥤ Set` that sends `A` to `ℙ(A ⊗[R] M; A)`. -/
noncomputable abbrev functor (R : CommRingCat.{u}) (M : ModuleCat.{v} R) :
    Under R ⥤ Type (max u v) :=
  Grassmannian.functor R M 1

variable {R M ι}

/-- The element of `ℙ(M; R)` given by a surjection `M →ₗ[R] R`.` -/
@[simps!] def ofSurjective (f : M →ₗ[R] R) (hf : Function.Surjective f) : ℙ(M; R) :=
  Grassmannian.ofSurjective ((LinearEquiv.funUnique (Fin 1) R R).symm ∘ₗ f) <| by
    exact (LinearEquiv.funUnique (Fin 1) R R).symm.surjective.comp hf

noncomputable def quotientOfSurjectiveLinearEquiv (f : M →ₗ[R] R) (hf : Function.Surjective f) :
    (M ⧸ (ofSurjective f hf).toSubmodule) ≃ₗ[R] R :=
  Submodule.quotEquivOfEq _ _ (by simp [ofSurjective]) ≪≫ₗ LinearMap.quotKerEquivOfSurjective f hf

@[simp] lemma quotientOfSurjectiveLinearEquiv_comp_mkQ
    (f : M →ₗ[R] R) (hf : Function.Surjective f) :
    (quotientOfSurjectiveLinearEquiv f hf) ∘ₗ (ofSurjective f hf).mkQ = f := by
  ext; simp [quotientOfSurjectiveLinearEquiv]


section ofCoordinates

variable (x : ι → R) (hx : Ideal.span (Set.range x) = ⊤)

/-- Special case for `ℙⁿ`: it suffices to give `n + 1` coordinates. -/
@[simps!] def ofCoordinates : ℙ(ι → R; R) :=
  ofSurjective (Fintype.linearCombination R x) <| by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, Ideal.submodule_span_eq, hx]

noncomputable def quotientOfCoordinatesLinearEquiv :
    ((ι → R) ⧸ (ofCoordinates x hx).toSubmodule) ≃ₗ[R] R :=
  quotientOfSurjectiveLinearEquiv _ _

@[simp] lemma quotientOfCoordinatesLinearEquiv_comp_mkQ :
    (quotientOfCoordinatesLinearEquiv x hx) ∘ₗ (ofCoordinates x hx).mkQ =
      Fintype.linearCombination R x :=
  quotientOfSurjectiveLinearEquiv_comp_mkQ _ _

end ofCoordinates


variable (R) in
/-- The affine chart indexed by `x : M`, consisting of those `N` such that there is an isomorphism
`M⧸N ≃ₗ[R] R`, sending `⟦x⟧` to `1`. Morally, this says "`x` is invertible". -/
abbrev chart (x : M) : Set ℙ(M; R) :=
  Grassmannian.chart R (fun _ ↦ x)

/-- Given `N ∈ chart R M x`, we have an isomorphism `M ⧸ N ≃ₗ[R] R` sending `x` to `1`. -/
noncomputable def equivOfChart (x : M) {N : ℙ(M; R)} (hn : N ∈ chart R x) :
    (M ⧸ N.toSubmodule) ≃ₗ[R] R :=
  Grassmannian.equivOfChart hn ≪≫ₗ LinearEquiv.funUnique (Fin 1) R R

lemma equivOfChart_apply (x : M) {N : ℙ(M; R)} (hn : N ∈ chart R x) :
    equivOfChart x hn (Submodule.Quotient.mk x) = 1 := by
  rw [equivOfChart, LinearEquiv.trans_apply, Grassmannian.equivOfChart_apply (i:=0)]; rfl

/-- "Division by `x`" is well-defined on the `chart` where "`x` is invertible". -/
noncomputable def div (y x : M) (p : chart R x) : R :=
  equivOfChart x p.2 (Submodule.Quotient.mk y)

lemma add_div (y z x : M) : div (R:=R) (y + z) x = div y x + div z x :=
  funext fun _ ↦ by rw [Pi.add_apply, div, div, div, Submodule.Quotient.mk_add, map_add]

lemma add_div_apply (y z x : M) (p) : div (R:=R) (y + z) x p = div y x p + div z x p :=
  congrFun (add_div ..) p

lemma smul_div (r : R) (y x : M) : div (R:=R) (r • y) x = r • div y x :=
  funext fun _ ↦ by rw [Pi.smul_apply, div, div, Submodule.Quotient.mk_smul, map_smul]

lemma smul_div_apply (r : R) (y x : M) (p) : div (R:=R) (r • y) x p = r * div y x p :=
  congrFun (smul_div ..) p

lemma div_smul_self (y x : M) (p) :
    div (R:=R) y x p • Submodule.Quotient.mk (p := p.1.toSubmodule) x = Submodule.Quotient.mk y :=
  (equivOfChart x p.2).injective <| by rw [map_smul, equivOfChart_apply, smul_eq_mul, mul_one, div]

lemma div_self (x : M) : div (R:=R) x x = 1 :=
  funext fun _ ↦ equivOfChart_apply ..

lemma div_self_apply (x : M) (p) : div (R:=R) x x p = 1 :=
  congrFun (div_self x) p

lemma div_mul_div_cancel (x y z : M) (p : Set.Elem (chart R y ∩ chart R z)) :
    div x y ⟨p.1, p.2.1⟩ * div y z ⟨p.1, p.2.2⟩ = div x z ⟨p.1, p.2.2⟩ := by
  nth_rw 2 [div]; rw [← smul_eq_mul, ← map_smul, div_smul_self, ← div]

lemma div_mul_div_symm (x y : M) (p : Set.Elem (chart R x ∩ chart R y)) :
    div x y ⟨p.1, p.2.2⟩ * div y x ⟨p.1, p.2.1⟩ = 1 := by
  rw [div_mul_div_cancel x y x ⟨p.1, p.2.2, p.2.1⟩, div_self_apply]

/-- `chart x` as a functor. `A` is sent to `chart A (A ⊗[R] M) (1 ⊗ₜ x)`. -/
noncomputable abbrev chartFunctor (R : CommRingCat.{u}) (M : ModuleCat.{v} R) (x : M) :
    Under R ⥤ Type (max u v) :=
  Grassmannian.chartFunctor R M 1 (fun _ ↦ x)

lemma chartFunctor_obj (R : CommRingCat.{u}) (M : ModuleCat.{v} R) (x : M) (A : Under R) :
    (chartFunctor R M x).obj A = chart A (1 ⊗ₜ x : A ⊗[R] M) :=
  rfl

/-- `chartFunctor` as a subfunctor of `ProjectiveSpace.functor`. -/
noncomputable abbrev chartToFunctor (R : CommRingCat.{u}) (M : ModuleCat.{v} R) (x : M) :
    chartFunctor R M x ⟶ functor R M :=
  Grassmannian.chartToFunctor R M 1 (fun _ ↦ x)

section zeros

open SymmetricPower

/-- `V(f)` the set of zeroes of the homogeneous polynomial `f` of degree `n`. -/
def zeros {n : ℕ} (f : Sym[R]^n M) : Set ℙ(M; R) :=
  { N | f.map n (Submodule.mkQ N.1) = 0 }

variable {n : ℕ} (f : Sym[R]^n M)

theorem zeros_def (p : ℙ(M; R)) : p ∈ zeros f ↔ f.map n (Submodule.mkQ p.1) = 0 := Iff.rfl

def zerosOfCoordinates {n : ℕ} (f : Sym[R]^n(ι → R))
    (x : ι → R) (hx : Ideal.span (Set.range x) = ⊤)
    (hfx : evalSelf R n (f.map n (Fintype.linearCombination R x)) = 0) : zeros f :=
  ⟨ofCoordinates x hx,
  (mapLinearEquiv n (quotientOfCoordinatesLinearEquiv x hx)).map_eq_zero_iff.1 <| by
    simp_all [-evalSelf_coe']⟩

variable {f}

lemma ofLinearEquiv_mem_zeros (e : M ≃ₗ[R] M₁) (p : ℙ(M; R)) (hp : p ∈ zeros f) :
    p.ofLinearEquiv e ∈ zeros (f.mapLinearEquiv n e) := by
  rw [zeros_def] at hp ⊢
  rw [mapLinearEquiv_coe', map_map_apply, coe_ofLinearEquiv,
    ← Submodule.mapQ_mkQ p (h := Submodule.le_comap_map e p), ← map_map_apply, hp, map_zero]

lemma baseChange_mem_zeros (p : ℙ(M; R)) (hp : p ∈ zeros f) :
    p.baseChange A ∈ zeros (f.toBaseChange R M A n) := by
  rw [zeros_def] at hp ⊢
  refine (mapLinearEquiv n (p.quotientBaseChangeEquiv A)).map_eq_zero_iff.1 ?_
  simp_rw [mapLinearEquiv_coe', map_map_apply, quotientBaseChangeEquiv, coe_baseChange,
    Submodule.quotientBaseChange_comp_baseChange_mkQ, map_toBaseChange_apply, hp, map_zero]

variable {A B} in
lemma map_mem_zeros (p : ℙ(A ⊗[R] M; A)) (hp : p ∈ zeros (f.toBaseChange R M A n)) (φ : A →ₐ[R] B) :
    p.map φ ∈ zeros (f.toBaseChange R M B n) := by
  letI : Algebra A B := φ.toAlgebra
  convert ofLinearEquiv_mem_zeros (AlgebraTensorModule.cancelBaseChange R A B B M) _
    (baseChange_mem_zeros B p hp)
  rw [mapLinearEquiv_coe', toBaseChange_apply_of_isScalarTower A]

variable {A B} in
@[simps] noncomputable def map_zeros (φ : A →ₐ[R] B) (p : zeros (f.toBaseChange R M A n)) :
    zeros (f.toBaseChange R M B n) :=
  ⟨p.1.map φ, map_mem_zeros p.1 p.2 φ⟩

/-- `zeros` as a functor. -/
@[simps] noncomputable
def zerosFunctor (R : CommRingCat.{u}) (M : ModuleCat.{v} R) {n : ℕ} (f : Sym[R]^n M) :
    Under R ⥤ Type (max u v) where
  obj A := zeros (toBaseChange R M A n f)
  map φ p := map_zeros (CommRingCat.toAlgHom φ) p
  map_id A := by ext; simp [Grassmannian.map_id]
  map_comp φ₁ φ₂ := by ext; simp [Grassmannian.map_comp]

end zeros

end ProjectiveSpace

end Module

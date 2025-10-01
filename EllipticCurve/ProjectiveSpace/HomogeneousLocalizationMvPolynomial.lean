/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Homogeneous Localization of MvPolynomial

In this file we show that the homogeneous localization of `MvPolynomial σ R` away from `X i` is
isomorphic to `MvPolynomial {k // k ≠ i} R`.
-/

namespace HomogeneousLocalization

@[simp]
lemma val_fromZeroRingHom {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι]
      [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (S : Submonoid A) (r : R) :
    (fromZeroRingHom 𝒜 S (algebraMap _ _ r)).val = algebraMap _ _ r :=
  rfl

instance {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι] [AddCommMonoid ι]
      (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (S : Submonoid A) :
    Algebra R (HomogeneousLocalization 𝒜 S) where
  algebraMap := (fromZeroRingHom 𝒜 S).comp (algebraMap R (𝒜 0))
  commutes' r x := mul_comm ..
  smul_def' r x := by ext; rw [val_smul, val_mul, Algebra.smul_def]; rfl

instance {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι] [AddCommMonoid ι]
      (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (S : Submonoid A) :
    IsScalarTower R (𝒜 0) (HomogeneousLocalization 𝒜 S) :=
  .of_algebraMap_eq' rfl

instance {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι] [AddCommMonoid ι]
      (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (S : Submonoid A) :
    IsScalarTower R (𝒜 0) (Localization S) :=
  .of_algebraMap_eq' rfl

instance {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι] [AddCommMonoid ι]
      (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (S : Submonoid A) :
    IsScalarTower R (HomogeneousLocalization 𝒜 S) (Localization S) :=
  .of_algebraMap_eq' rfl

instance {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι] [AddCommMonoid ι]
      (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (S : Submonoid A) :
    IsScalarTower (𝒜 0) (HomogeneousLocalization 𝒜 S) (Localization S) :=
  .of_algebraMap_eq' rfl

@[simp] lemma algebraMap_eq' {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι]
      [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (S : Submonoid A) :
    algebraMap R (HomogeneousLocalization 𝒜 S) = (fromZeroRingHom 𝒜 S).comp (algebraMap _ _) := rfl

theorem algebraMap_apply' {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι]
      [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (S : Submonoid A) (f : R) :
    algebraMap R (HomogeneousLocalization 𝒜 S) f = mk ⟨0, algebraMap _ _ f, 1, one_mem _⟩ := rfl

theorem val_sum {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {𝒜 : ι → Submodule R A}
      {x : Submonoid A} [AddCommMonoid ι] [DecidableEq ι] [GradedAlgebra 𝒜]
      {σ : Type*} {S : Finset σ} {f : σ → HomogeneousLocalization 𝒜 x} :
    (∑ s ∈ S, f s).val = ∑ s ∈ S, (f s).val :=
  map_sum (algebraMap (HomogeneousLocalization 𝒜 x) _) _ _

theorem val_prod {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {𝒜 : ι → Submodule R A}
      {x : Submonoid A} [AddCommMonoid ι] [DecidableEq ι] [GradedAlgebra 𝒜]
      {σ : Type*} {S : Finset σ} {f : σ → HomogeneousLocalization 𝒜 x} :
    (∏ s ∈ S, f s).val = ∏ s ∈ S, (f s).val :=
  map_prod (algebraMap (HomogeneousLocalization 𝒜 x) _) _ _

namespace Away

theorem mk_smul {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι]
      [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] {f d hf n x} (hx) {r : R} :
    r • Away.mk 𝒜 (f:=f) hf (d:=d) n x hx = .mk 𝒜 hf n (r • x) (Submodule.smul_mem _ _ hx) := rfl

theorem algebraMap_apply {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι]
      [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (f : A) (d hf) (r : R) :
    algebraMap R (Away 𝒜 f) r = .mk 𝒜 (d:=d) hf 0 (algebraMap R A r)
      (by rw [zero_nsmul]; exact SetLike.algebraMap_mem_graded ..) := by
  ext; simp [fromZeroRingHom]

/-- If `f = g`, then `Away 𝒜 f ≅ Away 𝒜 g`. -/
@[simps! apply] noncomputable
def congr {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι]
      [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (f g : A)
      {d : ι} (hf : f ∈ 𝒜 d) (h : f = g) :
    Away 𝒜 f ≃ₐ[R] Away 𝒜 g := by
  refine .ofRingEquiv (f := .ofRingHom (awayMap 𝒜 (SetLike.one_mem_graded ..) (by simp [h]))
    (awayMap 𝒜 (SetLike.one_mem_graded ..) (by simp [h]))
    (RingHom.ext fun x ↦ ?_) (RingHom.ext fun x ↦ ?_)) (fun x ↦ ?_)
  · subst h; rcases Away.mk_surjective 𝒜 hf x with ⟨n, a, ha, rfl⟩; simp
  · subst h; rcases Away.mk_surjective 𝒜 hf x with ⟨n, a, ha, rfl⟩; simp
  · subst h; ext; simp [awayMap_fromZeroRingHom]

lemma congr_mk {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι]
      [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (f g : A)
      {d : ι} (hf : f ∈ 𝒜 d) (h : f = g) (n x hx) :
    congr 𝒜 f g hf h (.mk 𝒜 hf n x hx) = .mk 𝒜 (by rwa [← h]) n x hx := by
  simp_rw [congr_apply, awayMap_mk, one_pow, mul_one, add_zero]

@[simp] lemma congr_symm {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι]
      [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (f g : A)
      {d : ι} (hf : f ∈ 𝒜 d) (h : f = g) :
    (congr 𝒜 f g hf h).symm = congr 𝒜 g f (by rwa [← h]) h.symm :=
  rfl

end Away

end HomogeneousLocalization


namespace MvPolynomial

open Classical in
/-- Dehomogenisation of a polynomial, e.g. `X²+2XY+3Y² ↦ X²+2X+3`. The variable to be removed
is specified. -/
noncomputable def dehomogenise {σ R : Type*} [CommSemiring R] (i : σ) :
    MvPolynomial σ R →ₐ[R] MvPolynomial { k // k ≠ i } R :=
  aeval fun j ↦ if H : j = i then 1 else X ⟨j, H⟩

theorem dehomogenise_C {σ R : Type*} [CommSemiring R] (i : σ) (r : R) :
    dehomogenise i (C r) = C r :=
  aeval_C ..

theorem dehomogenise_X_self {σ R : Type*} [CommSemiring R] (i : σ) :
    dehomogenise (R:=R) i (X i) = 1 := by
  rw [dehomogenise, aeval_X, dif_pos rfl]

@[simp] theorem dehomogenise_X_of_ne {σ R : Type*} [CommSemiring R] {i j : σ} (h : j ≠ i) :
    dehomogenise (R:=R) i (X j) = X ⟨j, h⟩ := by
  rw [dehomogenise, aeval_X, dif_neg]

@[simp] theorem dehomogenise_X {σ R : Type*} [CommSemiring R] {i : σ} (j : {k // k ≠ i}) :
    dehomogenise (R:=R) i (X j) = X j := by
  simp [j.2]

@[simp] theorem dehomogenise_of_mem_X_powers {σ R : Type*} [CommSemiring R] {i : σ} {d}
    (hd : d ∈ Submonoid.powers (X (R := R) i)) : dehomogenise (R:=R) i d = 1 := by
  rcases hd with ⟨_, _, rfl⟩; rw [map_pow, dehomogenise_X_self, one_pow]

theorem dehomogenise_X_powers {σ R : Type*} [CommSemiring R] (i : σ)
    (d : Submonoid.powers (X (R := R) i)) : dehomogenise (R:=R) i d = 1 :=
  dehomogenise_of_mem_X_powers d.2

/-- Functoriality. -/
theorem map_comp_dehomogenise {σ R S : Type*} [CommSemiring R] [CommSemiring S]
      (f : R →+* S) (i : σ) :
    (map f).comp (RingHomClass.toRingHom (dehomogenise (R:=R) i)) =
      (RingHomClass.toRingHom (dehomogenise (R:=S) i)).comp (map f) :=
  ringHom_ext (by simp) fun k ↦ by by_cases h : k = i <;> simp [h]

/-- Functoriality. -/
theorem map_dehomogenise {σ R S : Type*} [CommSemiring R] [CommSemiring S]
      (f : R →+* S) (i : σ) (p : MvPolynomial σ R) :
    map f (dehomogenise i p) = dehomogenise i (map f p) :=
  RingHom.congr_fun (map_comp_dehomogenise f i) p

attribute [local instance] gradedAlgebra

open HomogeneousLocalization

variable {σ R : Type*} [CommRing R] (i : σ)

/-- Map `Xⱼ/Xᵢ` to `Xⱼ`, contracting away the variable `Xᵢ`. -/
noncomputable def contract {σ : Type*} (R : Type*) [CommRing R] (i : σ) :
    Away (homogeneousSubmodule σ R) (X i) →ₐ[R] MvPolynomial { k // k ≠ i } R where
  toFun p := Quotient.liftOn p (fun q ↦ q.num.val.dehomogenise i) fun q₁ q₂ hq ↦
    let ⟨x, hx⟩ := Localization.r_iff_exists.1 (Localization.mk_eq_mk_iff.1 hq)
    have := congr_arg (dehomogenise i) hx
    by simpa only [ne_eq, map_mul, SetLike.coe_mem, dehomogenise_of_mem_X_powers, q₂.den_mem,
      one_mul, q₁.den_mem] using this
  map_one' := map_one _
  map_mul' p₁ p₂ := Quotient.inductionOn₂ p₁ p₂ fun q₁ q₂ ↦ map_mul ..
  map_zero' := map_zero _
  map_add' p₁ p₂ := Quotient.inductionOn₂ p₁ p₂ fun q₁ q₂ ↦ show dehomogenise _ (_ + _) = _ by
    rw [map_add, map_mul, map_mul, dehomogenise_of_mem_X_powers q₁.den_mem,
      dehomogenise_of_mem_X_powers q₂.den_mem, one_mul, one_mul, add_comm]; rfl
  commutes' r := algHom_C ..

@[simp] theorem contract_mk {σ : Type*} (R : Type*) [CommRing R] (i : σ) (hx) (n : ℕ) (f)
    (hf : f.IsHomogeneous _) :
  contract R i (.mk _ (d:=1) hx n f hf) = f.dehomogenise i := rfl

@[simp] theorem contract_mk' {σ : Type*} (R : Type*) [CommRing R] (i : σ) (q) :
  contract R i (mk q) = q.num.val.dehomogenise i := rfl

/-- Map `Xⱼ` to `Xⱼ/Xᵢ`, expanding to the variable `Xᵢ`. -/
noncomputable def expand {σ : Type*} (R : Type*) [CommRing R] (i : σ) :
    MvPolynomial { k // k ≠ i } R →ₐ[R] Away (homogeneousSubmodule σ R) (X i) :=
  aeval fun j ↦ .mk _ (isHomogeneous_X ..) 1 (X j) (isHomogeneous_X ..)

@[simp] theorem expand_C {σ R : Type*} [CommRing R] (i : σ) (r : R) :
    expand R i (C r) = .mk _ (isHomogeneous_X ..) 0 (C r) (isHomogeneous_C ..) :=
  algHom_C ..

@[simp] theorem expand_X {σ R : Type*} [CommRing R] (i : σ) (j) :
    expand R i (X j) = .mk _ (isHomogeneous_X ..) 1 (X j) (isHomogeneous_X ..) :=
  aeval_X ..

theorem expand_dehomogenise_monomial_one {σ R : Type*} [CommRing R] (i : σ) {d : ℕ} {c : σ →₀ ℕ}
    (hc : c.degree = d • 1) :
    expand R i ((monomial c 1).dehomogenise i) =
      .mk _ (isHomogeneous_X ..) d (monomial c 1) (isHomogeneous_monomial _ hc) := by
  ext : 1
  rw [Away.val_mk]
  rw [nsmul_one, Nat.cast_id] at hc
  cases hc; induction c using Finsupp.induction with
  | zero =>
      rw [monomial_zero', C_1, map_one, map_one, val_one, ← Localization.mk_one,
        Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      exact ⟨1, by simp⟩
  | single_add c n b hc hn ih =>
      classical
      rw [monomial_single_add, map_mul, map_mul, val_mul, ih,
        map_pow, map_pow]
      by_cases hci : c = i
      · rw [hci, dehomogenise_X_self, map_one, one_pow, val_one, one_mul,
          Localization.mk_eq_mk_iff, Localization.r_iff_exists]
        exact ⟨1, by simp; ring⟩
      · rw [dehomogenise_X_of_ne hci, expand_X, val_pow, Away.val_mk,
          Localization.mk_pow, Localization.mk_mul,
          Localization.mk_eq_mk_iff, Localization.r_iff_exists]
        exact ⟨1, by simp [add_comm]; ring⟩

theorem expand_dehomogenise_monomial {σ R : Type*} [CommRing R] (i : σ) {d : ℕ} {c : σ →₀ ℕ}
      (hc : c.degree = d • 1) (r : R) :
    expand R i ((monomial c r).dehomogenise i) =
      .mk _ (isHomogeneous_X ..) d (monomial c r) (isHomogeneous_monomial _ hc) := by
  have : monomial c r = r • monomial c 1 := by rw [smul_monomial, smul_eq_mul, mul_one]
  conv_lhs => rw [this, map_smul, map_smul, expand_dehomogenise_monomial_one _ hc, Away.mk_smul]
  congr 1; exact this.symm

@[simp] theorem expand_dehomogenise_of_homogeneous {σ R : Type*} [CommRing R] (i : σ) {n : ℕ}
      {p : MvPolynomial σ R} (hp : p.IsHomogeneous n) :
    expand R i (p.dehomogenise i) =
      .mk _ (isHomogeneous_X ..) n p (by rwa [nsmul_one]) := by
  ext
  rw [Away.val_mk, ← support_sum_monomial_coeff p, map_sum, map_sum, Localization.mk_sum, val_sum]
  congr 1; ext s; rw [expand_dehomogenise_monomial _ (by rw [nsmul_one, Nat.cast_id]), Away.val_mk]
  by_cases hs : s.degree = n
  · rw [hs]
  · rw [hp.coeff_eq_zero hs, monomial_zero, Localization.mk_zero, Localization.mk_zero]

@[simps!] noncomputable def algEquivAway (i : σ) :
    Away (homogeneousSubmodule σ R) (X i) ≃ₐ[R] MvPolynomial { k // k ≠ i } R where
  __ := contract R i
  invFun := expand R i
  left_inv p := by
    change expand R i (contract R i p) = p
    rcases Away.mk_surjective _ (isHomogeneous_X ..) p with ⟨d, r, hr, rfl⟩
    rw [contract_mk, expand_dehomogenise_of_homogeneous _ (by rwa [nsmul_one, Nat.cast_id] at hr)]
  right_inv p := by
    change contract R i (aeval _ p) = p
    induction p using induction_on
    · rw [aeval_C, algebraMap_apply', contract_mk',
        SetLike.GradeZero.coe_algebraMap, algebraMap_eq, dehomogenise_C]
    · simp only [map_add, *]
    · simp only [map_mul, *, aeval_X, contract_mk, dehomogenise_X]

end MvPolynomial

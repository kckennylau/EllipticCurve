import EllipticCurve.ProjectiveSpace.Graded.HomogeneousLocalization
import EllipticCurve.ProjectiveSpace.TensorProduct.GradedAlgebra

-- experimental

structure Graded (ι σ : Type*) where toFun : ι → σ

namespace Graded

instance (ι σ : Type*) : FunLike (Graded ι σ) ι σ where
  coe := toFun
  coe_injective' := by rintro ⟨_⟩ ⟨_⟩ h; congr

section Algebra
variable {ι R A : Type*} [DecidableEq ι] [AddMonoid ι]
  [CommSemiring R] [Semiring A] [Algebra R A]

protected abbrev Algebra (𝒜 : Graded ι (Submodule R A)) : Type _ :=
  GradedAlgebra 𝒜

variable (𝒜 : Graded ι (Submodule R A)) --[𝒜.Algebra]

variable (S : Type*) [CommSemiring S] [Algebra R S]

open TensorProduct

def baseChange : Graded ι (Submodule S (S ⊗[R] A)) :=
  ⟨fun i ↦ (𝒜 i).baseChange S⟩

instance [𝒜.Algebra] : (𝒜.baseChange S).Algebra :=
  inferInstanceAs <| GradedAlgebra fun i ↦ (𝒜 i).baseChange S

end Algebra

section Away
variable {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
  (𝒜 : Graded ι (Submodule R A))

def Away (f : A) : Type _ :=
  HomogeneousLocalization.Away 𝒜 f

variable [𝒜.Algebra] (f : A)

instance : CommRing (𝒜.Away f) := inferInstanceAs <| CommRing <| HomogeneousLocalization.Away 𝒜 f

variable (R₀ : Type*) [CommSemiring R₀] [Algebra R₀ R] [Algebra R₀ A] [IsScalarTower R₀ R A]

instance : Algebra R₀ (𝒜.Away f) :=
  HomogeneousLocalization.instAlgebraSubmodule_ellipticCurve ..

instance : Algebra (𝒜.Away f) (Localization.Away f) :=
  inferInstanceAs (Algebra (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f))

instance : IsScalarTower R (𝒜.Away f) (Localization.Away f) :=
  .of_algebraMap_eq' rfl

end Away

end Graded

#min_imports

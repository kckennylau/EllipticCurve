/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import EllipticCurve.ProjectiveSpace.Graded.Homogeneous
import EllipticCurve.ProjectiveSpace.Graded.Irrelevant
import EllipticCurve.ProjectiveSpace.Graded.RingEquiv

/-! # Admissible maps

I made up this name because I could not find it in the literature at all.

-/

open HomogeneousIdeal

variable {ι σ τ ψ A B C : Type*} [Semiring A] [Semiring B] [Semiring C]
  [DecidableEq ι] [AddCommMonoid ι] [PartialOrder ι] [CanonicallyOrderedAdd ι]
  [SetLike σ A] [AddSubmonoidClass σ A] [SetLike τ B] [AddSubmonoidClass τ B]
  [SetLike ψ C] [AddSubmonoidClass ψ C]
  {𝒜 : ι → σ} {ℬ : ι → τ} {𝒞 : ι → ψ}
  [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
  {F : Type*} [GradedFunLike F 𝒜 ℬ] [RingHomClass F A B]

namespace GradedRingHom

@[mk_iff] structure Admissible (f : F) : Prop where
  admissible : ℬ₊ ≤ 𝒜₊.map f

namespace Admissible

theorem id : Admissible (id 𝒜) where
  admissible := by simp

theorem comp {f : ℬ →+*ᵍ 𝒞} {g : 𝒜 →+*ᵍ ℬ} (hf : Admissible f) (hg : Admissible g) :
    Admissible (f.comp g) where
  admissible := hf.1.trans <| by rw [map_comp]; exact map_mono f hg.1

theorem coe {f : F} (hf : Admissible f) : Admissible (f : 𝒜 →+*ᵍ ℬ) := ⟨hf.1⟩

theorem of_coe {f : F} (hf : Admissible (f : 𝒜 →+*ᵍ ℬ)) : Admissible f := ⟨hf.1⟩

end Admissible

theorem admissible_coe_iff {f : F} : Admissible (f : 𝒜 →+*ᵍ ℬ) ↔ Admissible f := by
  simp_rw [admissible_iff]; rfl

end GradedRingHom

open GradedRingHom

theorem GradedRingEquiv.admissible (e : 𝒜 ≃+*ᵍ ℬ) : Admissible e where
  admissible := (irrelevant_le _).mpr fun i hi x hx ↦ by
    rw [← e.apply_symm_apply x] at hx ⊢
    exact Ideal.mem_map_of_mem _ <| mem_irrelevant_of_mem _ hi <| mem_of_map_mem e hx

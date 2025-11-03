/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

-- #30336

namespace HomogeneousIdeal

variable {ι σ A : Type*}
variable [Semiring A]
variable [DecidableEq ι]
variable [AddCommMonoid ι] [PartialOrder ι] [CanonicallyOrderedAdd ι]
variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]

scoped notation 𝒜"₊" => irrelevant 𝒜

lemma mem_irrelevant_of_mem {x : A} {i : ι} (hi : 0 < i) (hx : x ∈ 𝒜 i) : x ∈ 𝒜₊ := by
  rw [mem_irrelevant_iff, GradedRing.proj_apply, DirectSum.decompose_of_mem _ hx,
    DirectSum.of_eq_of_ne _ _ _ (by aesop), ZeroMemClass.coe_zero]

/-- `irrelevant 𝒜 = ⨁_{i>0} 𝒜ᵢ` -/
lemma irrelevant_eq_iSup : 𝒜₊.toAddSubmonoid = ⨆ i > 0, .ofClass (𝒜 i) := by
  refine le_antisymm (fun x hx ↦ ?_) <| iSup₂_le fun i hi x hx ↦ mem_irrelevant_of_mem _ hi hx
  classical rw [← DirectSum.sum_support_decompose 𝒜 x]
  refine sum_mem fun j hj ↦ ?_
  by_cases hj₀ : j = 0
  · classical exact (DFinsupp.mem_support_iff.mp hj <| hj₀ ▸ (by simpa using hx)).elim
  · exact AddSubmonoid.mem_iSup_of_mem j <| AddSubmonoid.mem_iSup_of_mem (pos_of_ne_zero hj₀) <|
      Subtype.prop _

open AddSubmonoid Set in
lemma irrelevant_eq_closure : 𝒜₊.toAddSubmonoid = .closure (⋃ i > 0, 𝒜 i) := by
  rw [irrelevant_eq_iSup]
  exact le_antisymm (iSup_le fun i ↦ iSup_le fun hi _ hx ↦ subset_closure <| mem_biUnion hi hx) <|
    closure_le.mpr <| iUnion_subset fun i ↦ iUnion_subset fun hi ↦ le_biSup (ofClass <| 𝒜 ·) hi

open AddSubmonoid Set in
lemma irrelevant_eq_span : 𝒜₊.toIdeal = .span (⋃ i > 0, 𝒜 i) :=
  le_antisymm ((irrelevant_eq_closure 𝒜).trans_le <| closure_le.mpr Ideal.subset_span) <|
    Ideal.span_le.mpr <| iUnion_subset fun _ ↦ iUnion_subset fun hi _ hx ↦
    mem_irrelevant_of_mem _ hi hx

lemma irrelevant_toAddSubmonoid_le {P : AddSubmonoid A} :
    𝒜₊.toAddSubmonoid ≤ P ↔ ∀ i > 0, .ofClass (𝒜 i) ≤ P := by
  rw [irrelevant_eq_iSup, iSup₂_le_iff]

lemma irrelevant_toIdeal_le {I : Ideal A} :
    𝒜₊.toIdeal ≤ I ↔ ∀ i > 0, .ofClass (𝒜 i) ≤ I.toAddSubmonoid :=
  irrelevant_toAddSubmonoid_le _

lemma irrelevant_le {P : HomogeneousIdeal 𝒜} :
    𝒜₊ ≤ P ↔ ∀ i > 0, .ofClass (𝒜 i) ≤ P.toAddSubmonoid :=
  irrelevant_toIdeal_le _

end HomogeneousIdeal

/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import EllipticCurve.Lemmas
import EllipticCurve.ProjectiveSpace.TensorProduct.SymmetricMap
import Mathlib.LinearAlgebra.TensorPower.Basic

/-!
# Symmetric tensor power of a semimodule over a commutative semiring

We define the `n`th symmetric tensor power of `M` as the `TensorPower` quotiented by the relation
that the `tprod` of `n` elements is equal to the `tprod` of the same elements permuted by a
permutation of `Fin n`. We denote this space by `Sym[R]^n M`, and the canonical multilinear map
from `M ^ n` to `Sym[R]^n M` by `⨂ₛ[R] i, f i`.

## Main definitions:

* `SymmetricPower.module`: the symmetric tensor power is a module over `R`.

## TODO:

* Grading: show that there is a map `Sym[R]^i M × Sym[R]^j M → Sym[R]^(i + j) M` that is
  associative and commutative, and that `n ↦ Sym[R]^n M` is a graded (semi)ring and algebra.
* Universal property: linear maps from `Sym[R]^n M` to `N` correspond to symmetric multilinear
  maps `M ^ n` to `N`.
* Relate to homogneous (multivariate) polynomials of degree `n`.

-/

suppress_compilation

universe u v w

open TensorProduct Equiv SymmetricMap Function

variable (R : Type u) [CommSemiring R] (M : Type v) [AddCommMonoid M] [Module R M]
  (N : Type w) [AddCommMonoid N] [Module R N] (n : ℕ)

/-- The relation on the `n`ᵗʰ tensor power of `M` that two tensors are equal if they are related by
a permutation of `Fin n`. -/
inductive SymmetricPower.Rel : ⨂[R]^n M → ⨂[R]^n M → Prop
  | perm : (e : Perm (Fin n)) → (f : Fin n → M) → Rel (⨂ₜ[R] i, f i) (⨂ₜ[R] i, f (e i))

/-- The symmetric tensor power of a semimodule `M` over a commutative semiring `R`
is the quotient of the `n`ᵗʰ tensor power by the relation that two tensors are equal
if they are related by a permutation of `Fin n`. -/
def SymmetricPower : Type max u v :=
  (addConGen (SymmetricPower.Rel R M n)).Quotient

@[inherit_doc] scoped[TensorProduct] notation:max "Sym[" R "]^" n:arg M:arg => SymmetricPower R M n

namespace SymmetricPower

instance : AddCommMonoid (Sym[R]^n M) := AddCon.addCommMonoid _

instance (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) :
    AddCommGroup (Sym[R]^n M) := AddCon.addCommGroup _

variable {R M n} in
lemma smul (r : R) (x y : ⨂[R]^n M) (h : addConGen (Rel R M n) x y) :
    addConGen (Rel R M n) (r • x) (r • y) := by
  induction h with
  | of x y h => cases h with
    | perm e f => cases n with
      | zero => convert (addConGen (Rel R M 0)).refl _
      | succ n =>
          convert AddConGen.Rel.of _ _ (Rel.perm (R := R) e (Function.update f 0 (r • f 0)))
          · rw [MultilinearMap.map_update_smul, Function.update_eq_self]
          · simp_rw [Function.update_apply_equiv_apply, MultilinearMap.map_update_smul,
              ← Function.update_comp_equiv, Function.update_eq_self]; rfl
  | refl => exact AddCon.refl _ _
  | symm => apply AddCon.symm; assumption
  | trans => apply AddCon.trans <;> assumption
  | add => rw [smul_add, smul_add]; apply AddCon.add <;> assumption

instance module : Module R (Sym[R]^n M) where
  smul r := AddCon.lift _ ((AddCon.mk' _).comp (AddMonoidHom.smulLeft r)) fun x y h ↦
    Quotient.sound (smul r x y h)
  one_smul x := AddCon.induction_on x <| fun x ↦ congr_arg _ <| one_smul R x
  mul_smul r s x := AddCon.induction_on x <| fun x ↦ congr_arg _ <| mul_smul r s x
  zero_smul x := AddCon.induction_on x <| fun x ↦ congr_arg _ <| zero_smul R x
  add_smul r s x := AddCon.induction_on x <| fun x ↦ congr_arg _ <| add_smul r s x
  smul_zero _ := map_zero _
  smul_add _ := map_add _

/-- The canonical map from the `n`ᵗʰ tensor power to the `n`ᵗʰ symmetric tensor power. -/
def mk : ⨂[R]^n M →ₗ[R] Sym[R]^n M where
  map_smul' _ _ := rfl
  __ := AddCon.mk' _

variable {M n} in
/-- The multilinear map that takes `n` elements of `M` and returns their symmetric tensor product.
Denoted `⨂ₛ[R] i, f i`. -/
def tprod : M [Σ^Fin n]→ₗ[R] Sym[R]^n M :=
  ⟨(mk R M n).compMultilinearMap (PiTensorProduct.tprod R), fun x e ↦
    Eq.symm <| Quot.sound <| AddConGen.Rel.of _ _ <| Rel.perm e x⟩

unsuppress_compilation in
@[inherit_doc tprod]
notation3:100 "⨂ₛ["R"] "(...)", "r:(scoped f => tprod R f) => r

variable {R M n} in
@[simp] lemma tprod_perm_apply (e : Perm (Fin n)) (f : Fin n → M) :
    (⨂ₛ[R] i, f (e i)) = tprod R f :=
  (tprod R).2 f e

theorem range_mk : LinearMap.range (mk R M n) = ⊤ :=
  LinearMap.range_eq_top_of_surjective _ AddCon.mk'_surjective

/-- The pure tensors (i.e. the elements of the image of `SymmetricPower.tprod`) span the symmetric
tensor product. -/
theorem span_tprod_eq_top : Submodule.span R (Set.range (tprod R (M := M) (n := n))) = ⊤ := by
  rw [tprod, coe_mk, LinearMap.coe_compMultilinearMap, Set.range_comp, Submodule.span_image,
    PiTensorProduct.span_tprod_eq_top, Submodule.map_top, range_mk]

variable {R M n} in
@[elab_as_elim] lemma inductionOn {C : Sym[R]^n M → Prop} (x : Sym[R]^n M)
    (zero : C 0) (smul_tprod : ∀ (r : R) x, C (r • tprod R x))
    (add : ∀ x y, C x → C y → C (x + y)) : C x := by
  obtain ⟨x, rfl⟩ := AddCon.mk'_surjective x
  obtain ⟨x, rfl⟩ := AddCon.mk'_surjective x
  refine FreeAddMonoid.inductionOn x zero (fun ⟨r, x⟩ ↦ ?_) fun _ _ ↦ add _ _
  simpa [tprod, ← map_smul, ← PiTensorProduct.tprodCoeff_eq_smul_tprod] using smul_tprod r x

variable {R M N n} in
omit [Module R N] in
@[ext] lemma addHom_ext {f g : Sym[R]^n M →+ N}
    (h : ∀ (r : R) (x : Fin n → M), f (r • tprod R x) = g (r • tprod R x)) :
    f = g :=
  DFunLike.ext _ _ fun x ↦ inductionOn x (by simp) h (by intros; simp [*])

variable {R M N n} in
@[ext] lemma hom_ext {f g : Sym[R]^n M →ₗ[R] N}
    (h : ∀ x : Fin n → M, f (tprod R x) = g (tprod R x)) :
    f = g :=
  LinearMap.toAddMonoidHom_injective <| addHom_ext fun r x ↦ by simp [map_smul, h]

variable {R M N n} in
def liftAux (f : M [Σ^Fin n]→ₗ[R] N) : Sym[R]^n M →ₗ[R] N where
  __ := AddCon.lift _ (AddMonoidHomClass.toAddMonoidHom <| PiTensorProduct.lift f) <|
    AddCon.addConGen_le fun _ _ h ↦ h.rec fun e x ↦ by simp
  map_smul' c x := AddCon.induction_on x <| by convert (PiTensorProduct.lift f.1).map_smul c

variable {R M N n} in
@[simp] lemma liftAux_tprod (f : M [Σ^Fin n]→ₗ[R] N) (x : Fin n → M) :
    liftAux f (tprod R x) = f x := by
  change liftAux f (AddCon.mk' _ _) = _; simp [liftAux]

def lift : M [Σ^Fin n]→ₗ[R] N ≃ₗ[R] (Sym[R]^n M →ₗ[R] N) where
  toFun f := liftAux f
  invFun f := f.compSymmetricMap (tprod R)
  left_inv f := by ext; simp
  right_inv f := by ext; simp
  map_add' f g := hom_ext fun x ↦ by simp
  map_smul' c f := hom_ext fun x ↦ by simp

variable {R M N n} in
@[simp] lemma lift_tprod (f : M [Σ^Fin n]→ₗ[R] N) (x : Fin n → M) :
    lift R M N n f (tprod R x) = f x :=
  liftAux_tprod f x

variable {R M N n} in
@[simp] lemma lift_symm_coe (f : Sym[R]^n M →ₗ[R] N) :
    ⇑((lift R M N n).symm f) = ⇑f ∘ ⇑(tprod R) := rfl

variable {R M N} in
def map (f : M →ₗ[R] N) : Sym[R]^n M →ₗ[R] Sym[R]^n N :=
  lift _ _ _ _ <| (tprod R).compLinearMap f

def mul (i j : ℕ) : Sym[R]^i M →ₗ[R] Sym[R]^j M →ₗ[R] Sym[R]^(i + j) M :=
  lift _ _ _ _ <|
  { toFun f := lift _ _ _ _ <|
    { toFun g := tprod R <| Fin.append f g
      map_update_add' g c x y := by simp
      map_update_smul' g c r x := by simp
      map_perm_apply' g e := by
        convert (tprod_perm_apply (Fin.permAdd 1 e) _) using 2
        ext x; exact x.addCases (by simp) (by simp) }
    map_update_add' f c x y := hom_ext fun g ↦ by simp
    map_update_smul' f c r x := hom_ext fun g ↦ by simp
    map_perm_apply' f e := hom_ext fun g ↦ by
      simp only [lift_tprod, coe_mk, MultilinearMap.coe_mk]
      convert (tprod_perm_apply (Fin.permAdd e 1) _) using 2
      ext x; exact x.addCases (by simp) (by simp) }

def zero_equiv : Sym[R]^0 M ≃ₗ[R] R where
  __ := lift R M R 0 ((ofIsEmpty R M R (Fin 0)).symm 1)
  invFun r := r • tprod R ![]
  left_inv x := by
    induction x using SymmetricPower.inductionOn with
    | zero => simp
    | smul_tprod r x => simp [Subsingleton.elim x ![]]
    | add x y hx hy => simp_all [add_smul]
  right_inv r := by simp

def one_equiv : Sym[R]^1 M ≃ₗ[R] M where
  __ := lift R M M 1 ((ofSubsingleton R M M 0).symm 1)
  invFun m := tprod R ![m]
  left_inv x := by
    induction x using SymmetricPower.inductionOn with
    | zero => simp [(tprod R).map_coord_zero (g := ![(0 : M)]) 0]
    | smul_tprod r x =>
        convert (tprod R).map_update_smul x 0 r (x 0) <;>
        exact funext <| Fin.forall_fin_one.2 <| by simp
    | add x y hx hy =>
        have (m₁ m₂ : M) : tprod R ![m₁ + m₂] = tprod R ![m₁] + tprod R ![m₂] := by
          convert (tprod R).map_update_add ![0] 0 m₁ m₂ using 3 <;>
          exact funext <| Fin.forall_fin_one.2 <| by simp
        conv => enter [2]; rw [← hx, ← hy]
        simp [this]
  right_inv m := by simp

scoped infix:70 "✱" => SymmetricPower.mul _ _

end SymmetricPower


import Catlib4.Algebra.Bimodule.Tensor
import Catlib4.Algebra.Bimodule.LeftHomSpace

namespace Algebra.Bimodule

variable {K : Field} {A B C : Algebra K} {M : Bimod A B} {N : Bimod B C} {E : Bimod A C}

def currify_l (f : M ⊗ N ⟶ E) : (N ⟶ left_hom_space M E) where
  f x :=
    ⟨ λ y => f (y ⊗ x)
    , by simp
    , by simp
    , by simp
    , by simp ⟩
  map_add _ _ := by
    apply LeftLinearMap.ext
    simp
  map_zero := by
    apply LeftLinearMap.ext
    simp
  map_smul _ _ := by
    apply LeftLinearMap.ext
    simp
  map_lmul _ _ := by
    apply LeftLinearMap.ext
    simp [Tensor.map_mmul]
  map_rmul _ _ := by
    apply LeftLinearMap.ext
    simp

def decurrify_l (f : N ⟶ left_hom_space M E) : M ⊗ N ⟶ E where
  f := tensor_factor
    ⟨ λ x y => f y x
    , by simp
    , by simp
    , by simp
    , by simp
    , by simp
    , by simp
    , by simp
    , by simp
    , by simp ⟩
  map_add := by simp
  map_zero := by simp
  map_smul := by simp
  map_lmul := by simp
  map_rmul := by simp

@[simp] theorem currify_l_val (f : M ⊗ N ⟶ E) (x : M) (y : N)
  : currify_l f y x = f (x ⊗ y) := rfl

@[simp] theorem decurrify_l_val (f : N ⟶ left_hom_space M E) (x : M) (y : N)
  : decurrify_l f (x ⊗ y) = f y x := tensor_sound _ _ _

def inverse_left (f : N ⟶ left_hom_space M E) : currify_l (decurrify_l f) = f := by
  apply BimoduleMorphism.ext
  intro x
  apply LeftLinearMap.ext
  intro y
  simp

def inverse_right (f : M ⊗ N ⟶ E) : decurrify_l (currify_l f) = f := by
  apply tensor_ind
  intro x y
  simp

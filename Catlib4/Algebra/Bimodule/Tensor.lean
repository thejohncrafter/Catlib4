
import Catlib4.Notation
import Catlib4.Algebra.Bimodule.Basic

namespace Algebra.Bimodule

section

variable {K : Field} {A B C : Algebra K} (M : Bimod A B) (N : Bimod B C) (E : Bimod A C)

structure BilinearMap where
  f : M → N → E
  map_smul_l : ∀ x y (μ : K), f (μ • x) y = μ • f x y
  map_smul_r : ∀ x y (μ : K), f x (μ • y) = μ • f x y
  map_add_l : ∀ x y z, f (x + y) z = f x z + f y z
  map_add_r : ∀ x y z, f x (y + z) = f x y + f x z
  map_zero_l : ∀ y, f 0 y = 0
  map_zero_r : ∀ x, f x 0 = 0
  map_lmul : ∀ x y (a : A), f (a •ₗ x) y = a •ₗ f x y
  map_rmul : ∀ x y (c : C), f x (y •ᵣ c) = f x y •ᵣ c
  map_mmul : ∀ x y (b : B), f (x •ᵣ b) y = f x (b •ₗ y)

attribute [simp] BilinearMap.map_smul_l
attribute [simp] BilinearMap.map_zero_l
attribute [simp] BilinearMap.map_smul_r
attribute [simp] BilinearMap.map_add_l
attribute [simp] BilinearMap.map_add_r
attribute [simp] BilinearMap.map_zero_r
attribute [simp] BilinearMap.map_lmul
attribute [simp] BilinearMap.map_rmul
attribute [simp] BilinearMap.map_mmul

instance : CoeFun (BilinearMap M N E) (fun _ => M → N → E) where
  coe φ := φ.f

end

section

variable {K : Field} {A B C : Algebra K} {M : Bimod A B} {N : Bimod B C} {E : Bimod A C}

theorem BilinearMap.eq :
  ∀ {f g : BilinearMap M N E}, f.f = g.f → f = g
  | ⟨ _, _, _, _, _, _, _, _, _, _ ⟩, ⟨ _, _, _, _, _, _, _, _, _, _ ⟩, rfl => rfl

theorem BilinearMap.ext {f g : BilinearMap M N E} (h : ∀ x y, f x y = g x y) : f = g :=
  eq <| funext λ x => funext λ y => h x y

def BilinearMap.comp {F : Bimod A C} (f : E ⟶ F) (g : BilinearMap M N E)
  : BilinearMap M N F where
  f x y := f (g x y)
  map_smul_l := by simp
  map_smul_r := by simp
  map_add_l := by simp
  map_add_r := by simp
  map_zero_l := by simp
  map_zero_r := by simp
  map_lmul := by simp
  map_rmul := by simp
  map_mmul := by simp

def BilinearMap.congrFun : ∀ {f g : BilinearMap M N E}, f = g → ∀ x y, f x y = g x y :=
  λ h _ _ => h ▸ rfl

end

section

private structure TensorInterface
  {K : Field} {A B C : Algebra K} (M : Bimod A B) (N : Bimod B C)
  where
  tensor_space : Bimod A C
  tensor_obj : BilinearMap M N tensor_space
  tensor_factor {E : Bimod A C} (f : BilinearMap M N E) : tensor_space ⟶ E
  tensor_sound {E : Bimod A C} (f : BilinearMap M N E)
    : BilinearMap.comp (tensor_factor f) tensor_obj = f
  tensor_ind {E : Bimod A C} {f g : tensor_space ⟶ E}
    (h : BilinearMap.comp f tensor_obj = BilinearMap.comp g tensor_obj)
    : f = g

private opaque tensor_interface {K : Field} {A B C : Algebra K}
  (M : Bimod A B) (N : Bimod B C) : TensorInterface M N := sorry

private def tensor_space {K : Field} {A B C : Algebra K} (M : Bimod A B) (N : Bimod B C)
  : Bimod A C := (tensor_interface M N).tensor_space

instance {K : Field} {A B C : Algebra K} : HasTensor (Bimod A B) (Bimod B C) (Bimod A C) where
  tensor M N := tensor_space M N

def tensor_obj {K : Field} {A B C : Algebra K} {M : Bimod A B} {N : Bimod B C}
  : BilinearMap M N (M ⊗ N) := (tensor_interface M N).tensor_obj

instance {K : Field} {A B C : Algebra K} (M : Bimod A B) (N : Bimod B C) :
  HasTensor M N (M ⊗ N) where
  tensor x y := tensor_obj x y

section

variable {K : Field} {A B C : Algebra K} {M : Bimod A B} {N : Bimod B C} {E : Bimod A C}

@[simp] theorem Tensor.map_smul_l : ∀ (x : M) (y : N) (μ : K), μ • x ⊗ y = μ • (x ⊗ y)
  := tensor_obj.map_smul_l

@[simp] theorem Tensor.map_smul_r : ∀ (x : M) (y : N) (μ : K), x ⊗ μ • y = μ • (x ⊗ y)
  := tensor_obj.map_smul_r

@[simp] theorem Tensor.map_add_l : ∀ (x y : M) (z : N), (x + y) ⊗ z = x ⊗ z + y ⊗ z
  := tensor_obj.map_add_l

@[simp] theorem Tensor.map_add_r : ∀ (x : M) (y z : N), x ⊗ (y + z) = x ⊗ y + x ⊗ z
  := tensor_obj.map_add_r

@[simp] theorem Tensor.map_zero_l : ∀ (y : N), (0 : M) ⊗ y = 0
  := tensor_obj.map_zero_l

@[simp] theorem Tensor.map_zero_r : ∀ (x : M), x ⊗ (0 : N) = 0
  := tensor_obj.map_zero_r

@[simp] theorem Tensor.map_lmul : ∀ (x : M) (y : N) (a : A), a •ₗ x ⊗ y = a •ₗ (x ⊗ y)
  := tensor_obj.map_lmul

@[simp] theorem Tensor.map_rmul : ∀ (x : M) (y : N) (c : C), x ⊗ y •ᵣ c = (x ⊗ y) •ᵣ c
  := tensor_obj.map_rmul

theorem Tensor.map_mmul : ∀ (x : M) (y : N) (b : B), x •ᵣ b ⊗ y = x ⊗ b •ₗ y
  := tensor_obj.map_mmul

end

def tensor_factor {K : Field} {A B C : Algebra K} {M : Bimod A B} {N : Bimod B C}
  {E : Bimod A C} (f : BilinearMap M N E) : (M ⊗ N) ⟶ E
  := (tensor_interface M N).tensor_factor f

theorem tensor_sound {K : Field} {A B C : Algebra K} {M : Bimod A B} {N : Bimod B C}
  {E : Bimod A C} (f : BilinearMap M N E)
  : ∀ x y, tensor_factor f (x ⊗ y) = f x y
  := BilinearMap.congrFun <| (tensor_interface M N).tensor_sound f

theorem tensor_ind {K : Field} {A B C : Algebra K} {M : Bimod A B} {N : Bimod B C}
  {E : Bimod A C} {f g : M ⊗ N ⟶ E}
  (h : ∀ (x : M) (y : N), f (x ⊗ y) = g (x ⊗ y))
  : f = g
  := (tensor_interface M N).tensor_ind <| BilinearMap.ext h

end

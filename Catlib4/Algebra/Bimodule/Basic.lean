
import Catlib4.Algebra.VectorSpace
import Catlib4.Algebra.Algebra

import Catlib4.Category.Category

namespace Algebra.Bimodule

structure BimoduleStructure {K : Field} (L R : Algebra K) where
  α : Type u
  add : α → α → α
  neg : α → α
  zero : α
  smul : K → α → α
  lmul : L → α → α
  rmul : α → R → α

instance {K : Field} {L R : Algebra K} : CoeSort (BimoduleStructure L R) (Type u) where
  coe A := A.α

instance {K : Field} {L R : Algebra K} (M : BimoduleStructure L R) : Add M where
  add := M.add

instance {K : Field} {L R : Algebra K} (M : BimoduleStructure L R) : Neg M where
  neg := M.neg

instance {K : Field} {L R : Algebra K} (M : BimoduleStructure L R) : OfNat M (nat_lit 0) where
  ofNat := M.zero

instance {K : Field} {L R : Algebra K} (M : BimoduleStructure L R) : SMul K M where
  smul := M.smul

instance {K : Field} {L R : Algebra K} (A : BimoduleStructure L R) : LSMul L A where
  lmul := A.lmul

instance {K : Field} {L R : Algebra K} (A : BimoduleStructure L R) : RSMul A R where
  rmul := A.rmul

structure Bimodule {K : Field} (L R : Algebra K) extends BimoduleStructure L R where
  -- An additive group
  add_zero : ∀ x : α, x + 0 = x
  zero_add : ∀ x : α, 0 + x = x
  add_assoc : ∀ x y z : α, x + (y + z) = x + y + z
  add_comm : ∀ x y : α, x + y = y + x
  add_neg : ∀ x : α, x + -x = 0
  -- That is also a vector space
  smul_smul : ∀ x y : K, ∀ z : α, x • y • z = (x * y) • z
  smul_add : ∀ x : K, ∀ y z : α, x • (y + z) = x • y + x • z
  smul_zero : ∀ x : K, x • (0 : α) = 0
  add_smul : ∀ x y : K, ∀ z : α, (x + y) • z = x • z + y • z
  zero_smul : ∀ x : α, (0 : K) • x = 0
  one_smul : ∀ x : α, (1 : K) • x = x
  -- With an action of L on the left
  lmul_lmul : ∀ x y : L, ∀ z : α, x •ₗ y •ₗ z = (x * y) •ₗ z
  lmul_add : ∀ x : L, ∀ y z : α, x •ₗ (y + z) = x •ₗ y + x •ₗ z
  lmul_zero : ∀ x : L, x •ₗ (0 : α) = 0
  add_lmul : ∀ x y : L, ∀ z : α, (x + y) •ₗ z = x •ₗ z + y •ₗ z
  zero_lmul : ∀ x : α, (0 : L) •ₗ x = 0
  one_lmul : ∀ x : α, (1 : L) •ₗ x = x
  -- And an action of R on the right
  rmul_rmul : ∀ x : α, ∀ y z : R, x •ᵣ y •ᵣ z = x •ᵣ (y * z)
  add_rmul : ∀ x y : α, ∀ z : R, (x + y) •ᵣ z = x •ᵣ z + y •ᵣ z
  zero_rmul : ∀ x : R, (0 : α) •ᵣ x = 0
  rmul_add : ∀ x : α, ∀ y z : R, x •ᵣ (y + z) = x •ᵣ y + x •ᵣ z
  rmul_zero : ∀ x : α, x •ᵣ (0 : R) = 0
  rmul_one : ∀ x : α, x •ᵣ (1 : R) = x
  -- And these actions are compatible
  lmul_rmul : ∀ x : α, ∀ μ : L, ∀ ν : R, (μ •ₗ x) •ᵣ ν = μ •ₗ (x •ᵣ ν)
  lmul_linear : ∀ x : α, ∀ y : L, ∀ μ : K, (μ • y) •ₗ x = μ • y •ₗ x
  rmul_linear : ∀ x : α, ∀ y : R, ∀ μ : K, x •ᵣ (μ • y) = μ • x •ᵣ y
  lmul_linear' : ∀ x : α, ∀ y : L, ∀ μ : K, y •ₗ μ • x = μ • y •ₗ x
  rmul_linear' : ∀ x : α, ∀ y : R, ∀ μ : K, (μ • x) •ᵣ y = μ • x •ᵣ y

instance {K : Field} {L R : Algebra K} : CoeSort (Bimodule L R) (Type u) where
  coe M := M.α

section

variable {K : Field} {L R : Algebra K} (M : Bimodule L R)

attribute [simp] Bimodule.add_zero
attribute [simp] Bimodule.zero_add
attribute [simp] Bimodule.add_assoc
-- attribute [simp] Bimodule.add_comm -- Don't @[simp]: causes infinite loops!
attribute [simp↓] Bimodule.add_neg
attribute [simp] Bimodule.smul_smul
attribute [simp] Bimodule.smul_add
attribute [simp] Bimodule.smul_zero
attribute [simp] Bimodule.add_smul
attribute [simp] Bimodule.zero_smul
attribute [simp] Bimodule.one_smul
attribute [simp] Bimodule.lmul_lmul
attribute [simp] Bimodule.lmul_add
attribute [simp] Bimodule.lmul_zero
attribute [simp] Bimodule.add_lmul
attribute [simp] Bimodule.zero_lmul
attribute [simp] Bimodule.one_lmul
attribute [simp] Bimodule.rmul_rmul
attribute [simp] Bimodule.rmul_add
attribute [simp] Bimodule.rmul_zero
attribute [simp] Bimodule.add_rmul
attribute [simp] Bimodule.zero_rmul
attribute [simp] Bimodule.lmul_rmul
attribute [simp] Bimodule.lmul_linear
attribute [simp] Bimodule.rmul_linear
attribute [simp] Bimodule.lmul_linear'
attribute [simp] Bimodule.rmul_linear'

@[simp] theorem Bimodule.neg_eq_neg_one_smul : ∀ u : M, -u = -(1 : K) • u := by
  sorry

@[simp] theorem Bimodule.add_mul_neg_one :
  ∀ x : M, x + (-1 : K) • x = 0 :=
  λ _ => neg_eq_neg_one_smul _ _ ▸ add_neg _ _

@[simp] theorem Bimodule.smul_add_neg_one_mul_smul :
  ∀ x : M, ∀ μ : K, μ • x + ((-1) * μ) • x = 0 :=
  λ _ _ => (smul_smul _ _ _ _) ▸ add_mul_neg_one _ _

theorem Bimodule.neg_eq_neg_one_lmul : ∀ u : M, -u = -(1 : L) •ₗ u := by
  sorry

theorem Bimodule.neg_eq_rmul_neg_one : ∀ u : M, -u = u •ᵣ -(1 : R) := by
  sorry

@[simp] theorem Bimodule.add_neg_one_lmul :
  ∀ x : M, x + (-1 : L) •ₗ x = 0 :=
  λ _ => neg_eq_neg_one_lmul _ _ ▸ add_neg _ _

@[simp] theorem Bimodule.add_rmul_neg_one :
  ∀ x : M, x + x •ᵣ (-1 : R) = 0 :=
  λ _ => neg_eq_rmul_neg_one _ _ ▸ add_neg _ _

@[simp] theorem Bimodule.smul_add_neg_one_mul_lmul :
  ∀ x : M, ∀ μ : L, μ •ₗ x + ((-1) * μ) •ₗ x = 0 :=
  λ _ _ => (lmul_lmul _ _ _ _) ▸ add_neg_one_lmul _ _

@[simp] theorem Bimodule.smul_add_rmul_neg_one_mul :
  ∀ x : M, ∀ μ : R, x •ᵣ μ + x •ᵣ (μ * (-1)) = 0 :=
  λ _ _ => (rmul_rmul _ _ _ _) ▸ add_rmul_neg_one _ _

theorem Bimodule.eq_of_sum_zero :
  ∀ x y : M, x + -y = 0 → x = y := sorry

end

structure BimoduleMorphism {K : Field} {L R : Algebra K} (M N : Bimodule L R) where
  f : M → N
  map_add : ∀ x y : M, f (x + y) = f x + f y
  map_zero : f 0 = 0
  map_smul : ∀ x : M, ∀ μ : K, f (μ • x) = μ • f x
  map_lmul : ∀ x : M, ∀ μ : L, f (μ •ₗ x) = μ •ₗ f x
  map_rmul : ∀ x : M, ∀ μ : R, f (x •ᵣ μ) = f x •ᵣ μ

attribute [simp] BimoduleMorphism.map_add
attribute [simp] BimoduleMorphism.map_zero
attribute [simp] BimoduleMorphism.map_smul
attribute [simp] BimoduleMorphism.map_lmul
attribute [simp] BimoduleMorphism.map_rmul

instance {K : Field} {L R : Algebra K} (M N : Bimodule L R)
  : CoeFun (BimoduleMorphism M N) (fun _ => M → N) where
  coe := BimoduleMorphism.f

def BimoduleMorphism.identity {K : Field} {L R : Algebra K} (M : Bimodule L R)
  : BimoduleMorphism M M where
  f := id
  map_add := by simp
  map_zero := by simp
  map_smul := by simp
  map_lmul := by simp
  map_rmul := by simp

def BimoduleMorphism.zero {K : Field} {A B : Algebra K} (U V : Bimodule A B)
  : BimoduleMorphism U V where
  f := λ _ => 0
  map_add := by simp
  map_zero := by simp
  map_smul := by simp
  map_lmul := by simp
  map_rmul := by simp

def BimoduleMorphism.comp {K : Field} {L R : Algebra K} {M₁ M₂ M₃ : Bimodule L R}
  (f : BimoduleMorphism M₂ M₃) (g : BimoduleMorphism M₁ M₂) :
  BimoduleMorphism M₁ M₃ where
  f := f ∘ g
  map_add := by simp
  map_zero := by simp
  map_smul := by simp
  map_lmul := by simp
  map_rmul := by simp

def Bimod {K : Field} (L R : Algebra K) : CategoryTheory.Category where
  α := Bimodule L R
  hom M N := BimoduleMorphism M N
  comp f g := BimoduleMorphism.comp g f
  id M := BimoduleMorphism.identity M
  id_comp' := by intros; rfl
  comp_id' := by intros; rfl
  assoc' := by intros; rfl

instance {K : Field} (L R : Algebra K) : CoeSort (Bimod L R) (Type u)
  := inferInstanceAs (CoeSort (Bimodule L R) (Type u))

instance {K : Field} {L R : Algebra K} (M N : Bimod L R)
  : CoeFun (M ⟶ N) (fun _ => M → N) :=
  inferInstanceAs (CoeFun (BimoduleMorphism M N) (fun _ => M → N))

theorem BimoduleMorphism.eq {K : Field} {L R : Algebra K} {M N : Bimod L R}
  : ∀ {f g : M ⟶ N}, f.f = g.f → f = g
  | ⟨ _, _, _, _, _, _ ⟩, ⟨ _, _, _, _, _, _ ⟩, rfl => rfl

theorem BimoduleMorphism.ext {K : Field} {L R : Algebra K} {M N : Bimod L R}
  : ∀ {f g : M ⟶ N}, (∀ x, f x = g x) → f = g :=
  eq ∘ funext

def Bimodule.to_vector_space {K : Field} {L R : Algebra K} (M : Bimodule L R) : KVect K where
  α := M
  add := M.add
  neg := M.neg
  zero := M.zero
  smul := M.smul
  add_zero := M.add_zero
  zero_add := M.zero_add
  add_assoc := M.add_assoc
  add_comm := M.add_comm
  add_neg := M.add_neg
  smul_smul := M.smul_smul
  smul_add := M.smul_add
  smul_zero := M.smul_zero
  add_smul := M.add_smul
  zero_smul := M.zero_smul
  one_smul := M.one_smul


import Catlib4.Algebra.VectorSpace
import Catlib4.Algebra.Ring

import Catlib4.Category.Category

structure AlgebraStructure (K : Field) where
  α : Type u
  add : α → α → α
  neg : α → α
  zero : α
  mul : α → α → α
  one : α
  smul : K → α → α

instance {K : Field} : CoeSort (AlgebraStructure K) (Type u) where
  coe A := A.α

instance {K : Field} (A : AlgebraStructure K) : Add A where
  add := A.add

instance {K : Field} (A : AlgebraStructure K) : Neg A where
  neg := A.neg

instance {K : Field} (A : AlgebraStructure K) : Mul A where
  mul := A.mul

instance {K : Field} (A : AlgebraStructure K) : OfNat A (nat_lit 0) where
  ofNat := A.zero

instance {K : Field} (A : AlgebraStructure K) : OfNat A (nat_lit 1) where
  ofNat := A.one

instance {K : Field} (A : AlgebraStructure K) : SMul K A where
  smul := A.smul

structure Algebra (K : Field) extends AlgebraStructure K where
  -- An algebra
  add_zero : ∀ x : α, x + 0 = x
  zero_add : ∀ x : α, 0 + x = x
  add_assoc : ∀ x y z : α, x + (y + z) = x + y + z
  add_comm : ∀ x y : α, x + y = y + x
  add_neg : ∀ x : α, x + -x = 0
  mul_one : ∀ x : α, x * 1 = x
  one_mul : ∀ x : α, 1 * x = x
  mul_assoc : ∀ x y z : α, x * (y * z) = x * y * z
  mul_add : ∀ x y z : α, x * (y + z) = x * y + x * z
  smul_smul : ∀ x y : K, ∀ z : α, x • y • z = (x * y) • z
  smul_add : ∀ x : K, ∀ y z : α, x • (y + z) = x • y + x • z
  smul_zero : ∀ x : K, x • (0 : α) = 0
  add_smul : ∀ x y : K, ∀ z : α, (x + y) • z = x • z + y • z
  zero_smul : ∀ x : α, (0 : K) • x = 0
  one_smul : ∀ x : α, (1 : K) • x = x

instance {K : Field} : CoeSort (Algebra K) (Type u) where
  coe V := V.α

section

variable {K : Field} (V : Algebra K)

attribute [simp] Algebra.add_zero
attribute [simp] Algebra.zero_add
attribute [simp] Algebra.add_assoc
-- attribute [simp] Algebra.add_comm -- Don't @[simp]: causes infinite loops!
attribute [simp↓] Algebra.add_neg
attribute [simp] Algebra.smul_smul
attribute [simp] Algebra.smul_add
attribute [simp] Algebra.smul_zero
attribute [simp] Algebra.add_smul
attribute [simp] Algebra.zero_smul
attribute [simp] Algebra.one_smul

@[simp] theorem Algebra.neg_eq_neg_one_smul : ∀ u : V, -u = -(1 : K) • u := by
  sorry

@[simp] theorem Algebra.add_mul_neg_one :
  ∀ x : V, x + (-1 : K) • x = 0 :=
  λ _ => neg_eq_neg_one_smul _ _ ▸ add_neg _ _

@[simp] theorem Algebra.smul_add_neg_one_mul_smul :
  ∀ x : V, ∀ μ : K, μ • x + ((-1) * μ) • x = 0 :=
  λ _ _ => (smul_smul _ _ _ _) ▸ add_mul_neg_one _ _

theorem Algebra.eq_of_sum_zero :
  ∀ x y : V, x + -y = 0 → x = y := sorry

end

structure AlgebraMorphism {K : Field} (A B : Algebra K) where
  f : A → B
  map_add : ∀ x y : A, f (x + y) = f x + f y
  map_mul : ∀ x y : A, f (x * y) = f x * f y
  map_zero : f 0 = 0
  map_one : f 1 = 1
  map_smul : ∀ x : A, ∀ μ : K, f (μ • x) = μ • f x

attribute [simp] AlgebraMorphism.map_add
attribute [simp] AlgebraMorphism.map_mul
attribute [simp] AlgebraMorphism.map_zero
attribute [simp] AlgebraMorphism.map_one
attribute [simp] AlgebraMorphism.map_smul

instance {K : Field} (A B : Algebra K) : CoeFun (AlgebraMorphism A B) (fun _ => A → B) where
  coe := AlgebraMorphism.f

def AlgebraMorphism.identity {K : Field} (A : Algebra K) : AlgebraMorphism A A where
  f := id
  map_add := by simp
  map_mul := by simp
  map_zero := by simp
  map_one := by simp
  map_smul := by simp

def AlgebraMorphism.comp {K : Field} {A B C : Algebra K}
  (f : AlgebraMorphism B C) (g : AlgebraMorphism A B) :
  AlgebraMorphism A C where
  f := f ∘ g
  map_add := by simp
  map_mul := by simp
  map_zero := by simp
  map_one := by simp
  map_smul := by simp

def KAlg (K : Field) : CategoryTheory.Category where
  α := Algebra K
  hom A B := AlgebraMorphism A B
  comp f g := AlgebraMorphism.comp g f
  id A := AlgebraMorphism.identity A
  comp_id' := by intros; rfl
  id_comp' := by intros; rfl
  assoc' := by intros; rfl

instance {K : Field} : CoeSort (KAlg K) (Type u)
  := inferInstanceAs (CoeSort (Algebra K) (Type u))

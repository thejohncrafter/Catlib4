
import Catlib4.Algebra.Notation

section Algebra

structure RingStructure where
  α : Type u
  add : α → α → α
  neg : α → α
  mul : α → α → α
  zero : α
  one : α

instance : CoeSort RingStructure (Type u) where
  coe R := R.α

instance (R : RingStructure) : Add R where
  add := R.add

instance (R : RingStructure) : Neg R where
  neg := R.neg

instance (R : RingStructure) : Mul R where
  mul := R.mul

instance (R : RingStructure) : OfNat R (nat_lit 0) where
  ofNat := R.zero

instance (R : RingStructure) : OfNat R (nat_lit 1) where
  ofNat := R.one

structure FieldStructure extends RingStructure where
  inv : (x : α) → x ≠ 0 → α

structure Ring extends RingStructure where
  add_zero : ∀ x : α, x + 0 = x
  zero_add : ∀ x : α, 0 + x = x
  add_assoc : ∀ x y z : α, x + (y + z) = x + y + z
  add_comm : ∀ x y : α, x + y = y + x
  add_neg : ∀ x : α, x + -x = 0
  mul_one : ∀ x : α, x * 1 = x
  one_mul : ∀ x : α, 1 * x = x
  mul_assoc : ∀ x y z : α, x * (y * z) = x * y * z
  mul_add : ∀ x y z : α, x * (y + z) = x * y + x * z

instance : CoeSort Ring (Type u) where
  coe R := R.α

attribute [simp] Ring.add_zero
attribute [simp] Ring.zero_add
attribute [simp] Ring.add_assoc
-- attribute [simp] Ring.add_com -- Don't @[simp]: causes infinite loops!
attribute [simp↓] Ring.add_neg
attribute [simp] Ring.mul_one
attribute [simp] Ring.one_mul
attribute [simp] Ring.mul_assoc
attribute [simp] Ring.mul_add

@[simp] theorem Ring.mul_zero (A : Ring) :
  ∀ x : A, x * 0 = 0 := by
  sorry

@[simp] theorem Ring.add_mul (A : Ring) :
  ∀ x y z : A, (x + y) * z = x * z + y * z := by
  sorry

@[simp] theorem Ring.zero_mul (A : Ring) :
  ∀ x : A, 0 * x = 0 := by
  sorry

-- Don't @[simp]: causes infinite loops!
theorem Ring.neg_eq_neg_one_mul (A : Ring) :
  ∀ x : A, -x = -1 * x := by
  sorry

@[simp] theorem Ring.neg_one_mul_neg_one (A : Ring) : (-1 : A) * (-1 : A) = (1 : A) := by
  sorry

structure RingMorphism (A B : Ring) where
  φ : A → B
  map_add' : ∀ x y : A, φ (x + y) = φ x + φ y
  map_neg' : ∀ x : A, φ (-x) = - φ x
  map_mul' : ∀ x y : A, φ (x * y) = φ x * φ y
  map_zero' : φ 0 = 0
  map_one' : φ 1 = 1

instance (A B : Ring) : CoeFun (RingMorphism A B) (fun _ => A → B) where
  coe φ := φ.φ

@[simp]
theorem RingMorphism.map_add {A B : Ring} (φ : RingMorphism A B) :
  ∀ x y : A, φ (x + y) = φ x + φ y := φ.map_add'

@[simp] theorem RingMorphism.map_neg {A B : Ring} (φ : RingMorphism A B) :
  ∀ x : A, φ (-x) = - φ x := φ.map_neg'

@[simp] theorem RingMorphism.map_mul {A B : Ring} (φ : RingMorphism A B) :
  ∀ x y : A, φ (x * y) = φ x * φ y := φ.map_mul'

@[simp] theorem RingMorphism.map_zero {A B : Ring} (φ : RingMorphism A B) :
  φ 0 = 0 := φ.map_zero'

@[simp] theorem RingMorphism.map_one {A B : Ring} (φ : RingMorphism A B) :
  φ 1 = 1 := φ.map_one'

def Ring.idF (A : Ring) : RingMorphism A A where
  φ := id
  map_add' := by intros; rfl
  map_neg' := by intros; rfl
  map_mul' := by intros; rfl
  map_zero' := by intros; rfl
  map_one' := by intros; rfl

def Ring.compF {A B C : Ring}
  (f : RingMorphism A B) (g : RingMorphism B C) : RingMorphism A C where
  φ := g.φ ∘ f.φ
  map_add' := by simp
  map_neg' := by simp
  map_mul' := by simp
  map_zero' := by simp
  map_one' := by simp

structure Field extends Ring, FieldStructure where
  inv_cancel' : ∀ x : α, (nz : x ≠ 0) → x * inv x nz = 1
  mul_comm' : ∀ x y : α, y * x = x * y
  nonzero' : (1 : α) ≠ (0 : α)

instance : CoeSort Field (Type u) where
  coe F := F.α

@[simp] theorem Field.inv_cancel (F : Field) :
  ∀ x : F, (nz : x ≠ 0) → x * F.inv x nz = 1 := F.inv_cancel'

-- Don't @[simp]: causes infinite loops!
theorem Field.mul_comm (F : Field) :
  ∀ x y : F, y * x = x * y := F.mul_comm'

@[simp] theorem Field.nonzero (F : Field) : (1 : F) ≠ (0 : F) := F.nonzero'

end Algebra

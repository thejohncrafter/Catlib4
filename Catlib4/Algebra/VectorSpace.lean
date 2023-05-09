
import Catlib4.Algebra.Ring

import Catlib4.Category.Category

structure VectStructure (K : Field) where
  α : Type u
  add : α → α → α
  neg : α → α
  zero : α
  smul : K → α → α

instance {K : Field} : CoeSort (VectStructure K) (Type u) where
  coe M := M.α

instance {K : Field} (M : VectStructure K) : Add M where
  add := M.add

instance {K : Field} (M : VectStructure K) : Neg M where
  neg := M.neg

instance {K : Field} (M : VectStructure K) : SMul K M where
  smul := M.smul

instance {K : Field} (M : VectStructure K) : OfNat M (nat_lit 0) where
  ofNat := M.zero

structure VectorSpace (K : Field) extends VectStructure K where
  add_zero : ∀ x : α, x + 0 = x
  zero_add : ∀ x : α, 0 + x = x
  add_assoc : ∀ x y z : α, x + (y + z) = x + y + z
  add_comm : ∀ x y : α, x + y = y + x
  add_neg : ∀ x : α, x + -x = 0
  smul_smul : ∀ x y : K, ∀ z : α, x • y • z = (x * y) • z
  smul_add : ∀ x : K, ∀ y z : α, x • (y + z) = x • y + x • z
  smul_zero : ∀ x : K, x • (0 : α) = 0
  add_smul : ∀ x y : K, ∀ z : α, (x + y) • z = x • z + y • z
  zero_smul : ∀ x : α, (0 : K) • x = 0
  one_smul : ∀ x : α, (1 : K) • x = x

instance {K : Field} : CoeSort (VectorSpace K) (Type u) where
  coe V := V.α

section

variable {K : Field} (V : VectorSpace K)

attribute [simp] VectorSpace.add_zero
attribute [simp] VectorSpace.zero_add
attribute [simp] VectorSpace.add_assoc
-- attribute [simp] VectorSpace.add_comm -- Don't @[simp]: causes infinite loops!
attribute [simp↓] VectorSpace.add_neg
attribute [simp] VectorSpace.smul_smul
attribute [simp] VectorSpace.smul_add
attribute [simp] VectorSpace.smul_zero
attribute [simp] VectorSpace.add_smul
attribute [simp] VectorSpace.zero_smul
attribute [simp] VectorSpace.one_smul

@[simp] theorem VectorSpace.neg_eq_neg_one_smul : ∀ u : V, -u = -(1 : K) • u := by
  sorry

@[simp] theorem VectorSpace.add_mul_neg_one :
  ∀ x : V, x + (-1 : K) • x = 0 :=
  λ _ => neg_eq_neg_one_smul _ _ ▸ add_neg _ _

@[simp] theorem VectorSpace.smul_add_neg_one_mul_smul :
  ∀ x : V, ∀ μ : K, μ • x + ((-1) * μ) • x = 0 :=
  λ _ _ => (smul_smul _ _ _ _) ▸ add_mul_neg_one _ _

theorem VectorSpace.eq_of_sum_zero :
  ∀ x y : V, x + -y = 0 → x = y := sorry

end

structure LinearMap {K : Field} (V W : VectorSpace K) where
  f : V → W
  map_smul : ∀ μ : K, ∀ v : V, f (μ • v) = μ • f v
  map_add : ∀ v w : V, f (v + w) = f v + f w

section

variable {K : Field} {V W : VectorSpace K}

instance : CoeFun (LinearMap V W) (fun _ => V → W) where
  coe f := f.f

attribute [simp] LinearMap.map_smul
attribute [simp] LinearMap.map_add

theorem LinearMap.eq :
  ∀ {f g : LinearMap V W}, f.f = g.f → f = g
  | ⟨ _, _, _ ⟩, ⟨ _, _, _ ⟩, rfl => rfl

theorem LinearMap.ext : ∀ {f g : LinearMap V W}, (∀ x, f x = g x) → f = g :=
  LinearMap.eq ∘ funext

theorem LinearMap.congrFun : ∀ {f g : LinearMap V W}, f = g → ∀ x, f x = g x :=
  λ h _ => h ▸ rfl

variable (f : LinearMap V W)

@[simp] theorem LinearMap.map_zero : f 0 = 0 := by
  sorry

@[simp] theorem LinearMap.map_neg : ∀ x, f (-x) = - f x := by
  sorry

@[simp] theorem LinearMap.map_neg_one_smul : ∀ x, f ((-1 : K) • x) = (-1 : K) • f x := by
  sorry

end

def LinearMap.identity {K : Field} (V : VectorSpace K) : LinearMap V V where
  f x := x
  map_smul := by simp
  map_add := by simp

def LinearMap.zero {K : Field} (U V : VectorSpace K) : LinearMap U V where
  f _ := 0
  map_smul := by simp
  map_add := by simp

def LinearMap.compose {K : Field} {U V W : VectorSpace K}
  (f : LinearMap V W) (g : LinearMap U V) : LinearMap U W where
  f := f ∘ g
  map_smul := by simp
  map_add := by simp

def KVect (K : Field) : CategoryTheory.Category where
  α := VectorSpace K
  hom V W := LinearMap V W
  id := LinearMap.identity
  comp f g := LinearMap.compose g f
  id_comp' := by intros; rfl
  comp_id' := by intros; rfl
  assoc' := by intros; rfl

instance (K : Field) : HasHom (VectorSpace K) := inferInstanceAs (HasHom (KVect K))
instance (K : Field) : HasIdentity (VectorSpace K) := inferInstanceAs (HasIdentity (KVect K))
instance (K : Field) : HasComp (VectorSpace K) := inferInstanceAs (HasComp (KVect K))

instance {K : Field} : CoeSort (KVect K) (Type u) := inferInstanceAs (CoeSort (VectorSpace K) (Type u))

instance {K : Field} (V W : KVect K) : CoeFun (V ⟶ W) (fun _ => V → W) where
  coe f := f.f

def hom_space {K : Field} (V W : KVect K) : VectorSpace K where
  α := V ⟶ W
  add := λ ⟨ f, p, q ⟩ ⟨ g, p', q' ⟩ =>
    ⟨ λ x => f x + g x
    , by simp [p, q, p', q']
    , by
      intro v w
      suffices r : f v + f w + g v + g w = f v + g v + f w + g w by
        simp [p, q, p', q', r]
      rw [← W.add_assoc (f v) (g v), W.add_comm (g v) (f w), W.add_assoc] ⟩
  neg := λ ⟨ f, p, q ⟩ =>
    ⟨ λ x => - f x
    , by simp [p, q, K.mul_comm (-1)]
    , by simp [p, q] ⟩
  zero := ⟨ λ _ => 0, by simp, by simp ⟩
  smul := λ μ ⟨ f, p, q ⟩ =>
    ⟨ λ x => μ • f x
    , by intro ν v; simp [p, q, K.mul_comm μ ν]
    , by simp [p, q] ⟩
  add_zero _ := by
    apply LinearMap.ext
    exact λ _ => W.add_zero _
  zero_add _ := by
    apply LinearMap.ext
    exact λ _ => W.zero_add _
  add_assoc _ _ _ := by
    apply LinearMap.ext
    exact λ _ => W.add_assoc _ _ _
  add_comm _ _ := by
    apply LinearMap.ext
    exact λ _ => W.add_comm _ _
  add_neg _ := by
    apply LinearMap.ext
    exact λ _ => W.add_neg _
  smul_smul _ _ _ := by
    apply LinearMap.ext
    exact λ _ => W.smul_smul _ _ _
  smul_add _ _ _ := by
    apply LinearMap.ext
    exact λ _ => W.smul_add _ _ _
  smul_zero _ := by
    apply LinearMap.ext
    exact λ _ => W.smul_zero _
  add_smul _ _ _ := by
    apply LinearMap.ext
    exact λ _ => W.add_smul _ _ _
  zero_smul _ := by
    apply LinearMap.ext
    exact λ _ => W.zero_smul _
  one_smul _ := by
    apply LinearMap.ext
    exact λ _ => W.one_smul _

instance {K : Field} (V W : KVect K) : Add (V ⟶ W)
  := inferInstanceAs (Add (hom_space V W))
instance {K : Field} (V W : KVect K) : Neg (V ⟶ W)
  := inferInstanceAs (Neg (hom_space V W))
instance {K : Field} (V W : KVect K) : SMul K (V ⟶ W)
  := inferInstanceAs (SMul K (hom_space V W))
instance {K : Field} (V W : KVect K) : OfNat (V ⟶ W) (nat_lit 0)
  := inferInstanceAs (OfNat (hom_space V W) (nat_lit 0))

instance {K : Field} (V : KVect K) : OfNat (V ⟶ V) (nat_lit 1) where
  ofNat := LinearMap.identity V

@[simp] theorem LinearMap.identity_val {K : Field} {U : KVect K} (x : U) :
  𝟙 U x = x := rfl

@[simp] theorem LinearMap.zero_val {K : Field} {U : KVect K} (x : U) (V : KVect K) :
  (0 : U ⟶ V) x = 0 := rfl

@[simp] theorem LinearMap.compose_val {K : Field} {U V W : KVect K}
  (f : V ⟶ W) (g : U ⟶ V) (x : U) : (g ≫ f) x = f (g x) := rfl

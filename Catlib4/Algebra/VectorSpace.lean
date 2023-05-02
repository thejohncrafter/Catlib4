
import Catlib4.Algebra.Notation
import Catlib4.Algebra.Ring

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
  add_zero' : ∀ x : α, x + 0 = x
  zero_add' : ∀ x : α, 0 + x = x
  add_assoc' : ∀ x y z : α, x + (y + z) = x + y + z
  add_comm' : ∀ x y : α, x + y = y + x
  add_neg' : ∀ x : α, x + -x = 0
  smul_smul' : ∀ x y : K, ∀ z : α, x • y • z = (x * y) • z
  smul_add' : ∀ x : K, ∀ y z : α, x • (y + z) = x • y + x • z
  smul_zero' : ∀ x : K, x • (0 : α) = 0
  add_smul' : ∀ x y : K, ∀ z : α, (x + y) • z = x • z + y • z
  zero_smul' : ∀ x : α, (0 : K) • x = 0
  one_smul' : ∀ x : α, (1 : K) • x = x

instance {K : Field} : CoeSort (VectorSpace K) (Type u) where
  coe V := V.α

@[simp] theorem VectorSpace.add_zero {K : Field} (V : VectorSpace K) :
  ∀ x : V, x + 0 = x := V.add_zero'

@[simp] theorem VectorSpace.zero_add {K : Field} (V : VectorSpace K) :
  ∀ x : V, 0 + x = x := V.zero_add'

@[simp] theorem VectorSpace.add_assoc {K : Field} (V : VectorSpace K) :
  ∀ x y z : V, x + (y + z) = x + y + z := V.add_assoc'

-- Don't @[simp]: causes infinite loops!
theorem VectorSpace.add_comm {K : Field} (V : VectorSpace K) :
  ∀ x y : V, x + y = y + x := V.add_comm'

@[simp] theorem VectorSpace.add_neg {K : Field} (V : VectorSpace K) :
  ∀ x : V, x + -x = 0 := V.add_neg'

@[simp] theorem VectorSpace.smul_smul {K : Field} (V : VectorSpace K) :
  ∀ x y : K, ∀ z : V, x • y • z = (x * y) • z := V.smul_smul'

@[simp] theorem VectorSpace.smul_add {K : Field} (V : VectorSpace K) :
  ∀ x : K, ∀ y z : V, x • (y + z) = x • y + x • z := V.smul_add'

@[simp] theorem VectorSpace.smul_zero {K : Field} (V : VectorSpace K) :
  ∀ x : K, x • (0 : V) = 0 := V.smul_zero'

@[simp] theorem VectorSpace.add_smul {K : Field} (V : VectorSpace K) :
  ∀ x y : K, ∀ z : V, (x + y) • z = x • z + y • z := V.add_smul'

@[simp] theorem VectorSpace.zero_smul {K : Field} (V : VectorSpace K) :
  ∀ x : V, (0 : K) • x = 0 := V.zero_smul'

@[simp] theorem VectorSpace.one_smul {K : Field} (V : VectorSpace K) :
  ∀ x : V, (1 : K) • x = x := V.one_smul'

structure LinearMap {K : Field} (V W : VectorSpace K) where
  f : V → W
  map_smul : ∀ μ : K, ∀ v : V, f (μ • v) = μ • f v
  map_add : ∀ v w : V, f (v + w) = f v + f w

theorem LinearMap.eq {K : Field} {V W : VectorSpace K} :
  ∀ {f g : LinearMap V W}, f.f = g.f → f = g
  | ⟨ _, _, _ ⟩, ⟨ _, _, _ ⟩, rfl => rfl

@[simp] theorem neg_eq_neg_one_smul {V : VectorSpace K} : ∀ u : V, -u = -(1 : K) • u := by
  sorry

def hom_space_struct {K : Field} (V W : VectorSpace K) : VectStructure K where
  α := LinearMap V W
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

def hom_space {K : Field} (V W : VectorSpace K) : VectorSpace K where
  toVectStructure := hom_space_struct V W
  add_zero' _ := by
    apply LinearMap.eq ∘ funext
    exact λ _ => W.add_zero _
  zero_add' _ := by
    apply LinearMap.eq ∘ funext
    exact λ _ => W.zero_add _
  add_assoc' _ _ _ := by
    apply LinearMap.eq ∘ funext
    exact λ _ => W.add_assoc _ _ _
  add_comm' _ _ := by
    apply LinearMap.eq ∘ funext
    exact λ _ => W.add_comm' _ _
  add_neg' _ := by
    apply LinearMap.eq ∘ funext
    exact λ _ => W.add_neg _
  smul_smul' _ _ _ := by
    apply LinearMap.eq ∘ funext
    exact λ _ => W.smul_smul' _ _ _
  smul_add' _ _ _ := by
    apply LinearMap.eq ∘ funext
    exact λ _ => W.smul_add _ _ _
  smul_zero' _ := by
    apply LinearMap.eq ∘ funext
    exact λ _ => W.smul_zero _
  add_smul' _ _ _ := by
    apply LinearMap.eq ∘ funext
    exact λ _ => W.add_smul _ _ _
  zero_smul' _ := by
    apply LinearMap.eq ∘ funext
    exact λ _ => W.zero_smul _
  one_smul' _ := by
    apply LinearMap.eq ∘ funext
    exact λ _ => W.one_smul _

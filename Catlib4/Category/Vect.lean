
import Catlib4.Algebra.Vector.Tensor
import Catlib4.Category.Product

open Classical
noncomputable section

namespace CategoryTheory

def KVect (K : Field) : Category where
  α := VectorSpace K
  hom V W := LinearMap V W
  id := LinearMap.identity
  comp f g := LinearMap.compose g f
  id_comp' := by intros; rfl
  comp_id' := by intros; rfl
  assoc' := by intros; rfl

def map_tensor_space {V W V' W' : VectorSpace K}
  (f : LinearMap V V') (g : LinearMap W W') :
  BilinearMap V W (tensor_space V' W') where
  f x y := tensorα (f x) (g y)
  map_smul_l' := by simp
  map_smul_r' := by simp
  map_add_l' := by simp
  map_add_r' := by simp

@[simp] theorem map_tensor_space_val {V W V' W' : VectorSpace K}
  (f : LinearMap V V') (g : LinearMap W W')
  (v : V) (w : W) : map_tensor_space f g v w = tensorα (f v) (g w) := rfl

theorem TensorMap.ext {K : Field} {U V W : VectorSpace K}
  {f g : LinearMap (tensor_space U V) W}
  (h : ∀ u v, f (tensorα u v) = g (tensorα u v)) : f = g :=
  map_tensor_ext <| BilinearMap.ext h

def tensor_bifunctor (K : Field) : KVect K ×c KVect K ⟶ KVect K where
  obj := λ (V, W) => tensor_space V W
  map := λ (f, g) => tensor_factor <| map_tensor_space f g
  map_id' := by
    intro (V, W)
    show tensor_factor (map_tensor_space
      (LinearMap.identity V)
      (LinearMap.identity W)) = LinearMap.identity _
    apply TensorMap.ext
    simp
  map_comp' := by
    intro (V, W) (V', W') (V'', W'') (f, g) (f', g')
    show tensor_factor
        (map_tensor_space
          (LinearMap.compose f' f)
          (LinearMap.compose g' g))
      = LinearMap.compose
          (tensor_factor <| map_tensor_space f' g')
          (tensor_factor <| map_tensor_space f g)
    apply TensorMap.ext
    simp

def tensor_unit (K : Field) : VectorSpace K where
  α := K
  add := K.add
  neg := K.neg
  zero := K.zero
  smul := K.mul
  add_zero' := K.add_zero
  zero_add' := K.zero_add
  add_assoc' := K.add_assoc
  add_comm' := K.add_comm
  add_neg' := K.add_neg
  smul_smul' := K.mul_assoc
  smul_add' := K.mul_add
  smul_zero' := K.mul_zero
  add_smul' := K.add_mul
  zero_smul' := K.zero_mul
  one_smul' := K.one_mul

structure Linear {K : Field} {V W : VectorSpace K} (f : V → W) where
  map_smul' : ∀ μ : K, ∀ v : V, f (μ • v) = μ • f v
  map_add' : ∀ v w : V, f (v + w) = f v + f w

inductive BinaryTree (α : Type u) where
  | leaf (a : α) : BinaryTree α
  | node_left (l : BinaryTree α) (V : α) : BinaryTree α
  | node_right (U : α) (r : BinaryTree α) : BinaryTree α

def prod_set {K : Field} : BinaryTree (VectorSpace K) → Type
  | .leaf U => U
  | .node_left l V => prod_set l × V
  | .node_right U r => U × prod_set r

def prod_tensor {K : Field} : BinaryTree (VectorSpace K) → VectorSpace K
  | .leaf U => U
  | .node_left l V => tensor_space (prod_tensor l) V
  | .node_right U r => tensor_space U (prod_tensor r)

def prod_tensorα {K : Field} {l : BinaryTree (VectorSpace K)} (x : prod_set l)
  : prod_tensor l := match l with
  | .leaf _ => x
  | .node_left _ _ => tensorα (prod_tensorα x.1) x.2
  | .node_right _ _ => tensorα x.1 (prod_tensorα x.2)

@[simp] theorem prod_tensorα_val_leaf {K : Field} {U : VectorSpace K} (u : U) :
  @prod_tensorα K (.leaf U) u = u := rfl

@[simp] theorem prod_tensorα_val_node_left {K : Field}
  {l : BinaryTree (VectorSpace K)} (x : prod_set l)
  {V : VectorSpace K} (v : V)
  : @prod_tensorα K (.node_left l V) (x, v) = tensorα (prod_tensorα x) v := rfl

@[simp] theorem prod_tensorα_val_node_right {K : Field}
  {U : VectorSpace K} (u : U)
  {r : BinaryTree (VectorSpace K)} (y : prod_set r)
  : @prod_tensorα K (.node_right U r) (u, y) = tensorα u (prod_tensorα y) := rfl

inductive Multilinear {K : Field} (W : VectorSpace K)
  : (l : BinaryTree (VectorSpace K)) → (prod_set l → W) → Type _ where
  | one {U : VectorSpace K} (f : U → W)
    (map_smul : ∀ μ : K, ∀ v : U, f (μ • v) = μ • f v)
    (map_add : ∀ v w : U, f (v + w) = f v + f w)
    : Multilinear W (.leaf U) f
  | cons_left
    {l : BinaryTree (VectorSpace K)}
    {V : VectorSpace K}
    (f : prod_set l × V → W)
    (map_smul : ∀ x : prod_set l, ∀ μ : K, ∀ v : V, f (x, μ • v) = μ • f (x, v))
    (map_add : ∀ x : prod_set l, ∀ v w : V, f (x, v + w) = f (x, v) + f (x, w))
    (linear : ∀ v : V, Multilinear W l λ x => f (x, v))
    : Multilinear W (.node_left l V) f
  | cons_right
    {U : VectorSpace K}
    {r : BinaryTree (VectorSpace K)}
    (f : U × prod_set r → W)
    (map_smul : ∀ x : prod_set r, ∀ μ : K, ∀ v : U, f (μ • v, x) = μ • f (v, x))
    (map_add : ∀ x : prod_set r, ∀ v w : U, f (v + w, x) = f (v, x) + f (w, x))
    (linear : ∀ u : U, Multilinear W r λ x => f (u, x))
    : Multilinear W (.node_right U r) f

def linear_leaf {K : Field} {U V : VectorSpace K} (f : U → V) (h : Multilinear V (.leaf U) f)
  : LinearMap U V where
  f := f
  map_smul' := by cases h with | one _ map_smul map_add => exact map_smul
  map_add' := by cases h with | one _ map_smul map_add => exact map_add

def linear_node_right {K : Field} (U V W : VectorSpace K)
  (f : U → LinearMap V W)
  (map_smul : ∀ x : V, ∀ μ : K, ∀ v : U, f (μ • v) x = μ • f v x)
  (map_add : ∀ x : V, ∀ v w : U, f (v + w) x = f v x + f w x)
  : BilinearMap U V W where
  f := λ u v => f u v
  map_smul_l' _ _ _ := map_smul _ _ _
  map_add_l' _ _ _ := map_add _ _ _
  map_smul_r' := by simp
  map_add_r' := by simp

@[simp]
theorem linear_node_right_val {K : Field} (U V W : VectorSpace K)
  (f : U → LinearMap V W)
  (map_smul : ∀ x : V, ∀ μ : K, ∀ v : U, f (μ • v) x = μ • f v x)
  (map_add : ∀ x : V, ∀ v w : U, f (v + w) x = f v x + f w x)
  (u : U) (x : V)
  : linear_node_right U V W f map_smul map_add u x = f u x := rfl

def linear_node_left {K : Field} (U V W : VectorSpace K)
  (f : V → LinearMap U W)
  (map_smul : ∀ x : U, ∀ μ : K, ∀ v : V, f (μ • v) x = μ • f v x)
  (map_add : ∀ x : U, ∀ v w : V, f (v + w) x = f v x + f w x)
  : BilinearMap U V W where
  f := λ u v => f v u
  map_smul_l' := by simp
  map_add_l' := by simp
  map_smul_r' _ _ _ := map_smul _ _ _
  map_add_r' _ _ _ := map_add _ _ _

@[simp]
theorem linear_node_left_val {K : Field} (U V W : VectorSpace K)
  (f : V → LinearMap U W)
  (map_smul : ∀ x : U, ∀ μ : K, ∀ v : V, f (μ • v) x = μ • f v x)
  (map_add : ∀ x : U, ∀ v w : V, f (v + w) x = f v x + f w x)
  (u : U) (x : V)
  : linear_node_left U V W f map_smul map_add u x = f x u := rfl

theorem prod_tensor_eq {K : Field} {V : VectorSpace K} {l : BinaryTree (VectorSpace K)}
  (f g : LinearMap (prod_tensor l) V)
  (h : ∀ x : prod_set l, f (prod_tensorα x) = g (prod_tensorα x)) : f = g := by
  sorry

instance {K : Field} (V W : VectorSpace K) : SMul K (LinearMap V W)
  := inferInstanceAs (SMul K (hom_space V W))

instance {K : Field} (V W : VectorSpace K) : Add (LinearMap V W)
  := inferInstanceAs (Add (hom_space V W))

def build_step_left {K : Field} {W V : VectorSpace K} {l : BinaryTree (VectorSpace K)}
  (f : prod_set (.node_left l V) → W)
  (map_smul : ∀ x : prod_set l, ∀ μ : K, ∀ v : V, f (x, μ • v) = μ • f (x, v))
  (map_add : ∀ x : prod_set l, ∀ v w : V, f (x, v + w) = f (x, v) + f (x, w))
  (recursive : (v : V) → { lin : LinearMap (prod_tensor l) W // ∀ x, lin (prod_tensorα x) = f (x, v) })
  : { lin : LinearMap (prod_tensor (.node_left l V)) W // ∀ x, lin (prod_tensorα x) = f x } :=
  ⟨ by
    apply tensor_factor
    apply linear_node_left _ _ _ λ u => recursive u
    focus
      intro x μ v
      let ⟨ r₁, p₁ ⟩ := recursive (μ • v)
      let ⟨ r₂, p₂ ⟩ := recursive v
      suffices p : r₁ = μ • r₂ from congrFun (congrArg LinearMap.f p) x
      apply prod_tensor_eq
      intro x
      conv => rhs; change μ • r₂ (prod_tensorα x)
      rw [p₁, p₂]
      exact map_smul _ _ _
    focus
      intro x v w
      let ⟨ r₁, p₁ ⟩ := recursive (v + w)
      let ⟨ r₂, p₂ ⟩ := recursive v
      let ⟨ r₃, p₃ ⟩ := recursive w
      suffices p : r₁ = r₂ + r₃ from congrFun (congrArg LinearMap.f p) x
      apply prod_tensor_eq
      intro x
      conv => rhs; change r₂ (prod_tensorα x) + r₃ (prod_tensorα x)
      rw [p₁, p₂, p₃]
      exact map_add _ _ _
  , by
    intro (x, v)
    simp [(recursive v).2] ⟩

def build_step_right {K : Field} {W U : VectorSpace K} {r : BinaryTree (VectorSpace K)}
  (f : prod_set (.node_right U r) → W)
  (map_smul : ∀ x : prod_set r, ∀ μ : K, ∀ v : U, f (μ • v, x) = μ • f (v, x))
  (map_add : ∀ x : prod_set r, ∀ v w : U, f (v + w, x) = f (v, x) + f (w, x))
  (recursive : (u : U) → { l : LinearMap (prod_tensor r) W // ∀ x, l (prod_tensorα x) = f (u, x) })
  : { l : LinearMap (prod_tensor (.node_right U r)) W // ∀ x, l (prod_tensorα x) = f x } :=
  ⟨ by
    apply tensor_factor
    apply linear_node_right _ _ _ λ u => recursive u
    focus
      intro x μ v
      let ⟨ r₁, p₁ ⟩ := recursive (μ • v)
      let ⟨ r₂, p₂ ⟩ := recursive v
      suffices p : r₁ = μ • r₂ from congrFun (congrArg LinearMap.f p) x
      apply prod_tensor_eq
      intro x
      conv => rhs; change μ • r₂ (prod_tensorα x)
      rw [p₁, p₂]
      exact map_smul _ _ _
    focus
      intro x v w
      let ⟨ r₁, p₁ ⟩ := recursive (v + w)
      let ⟨ r₂, p₂ ⟩ := recursive v
      let ⟨ r₃, p₃ ⟩ := recursive w
      suffices p : r₁ = r₂ + r₃ from congrFun (congrArg LinearMap.f p) x
      apply prod_tensor_eq
      intro x
      conv => rhs; change r₂ (prod_tensorα x) + r₃ (prod_tensorα x)
      rw [p₁, p₂, p₃]
      exact map_add _ _ _
  , by
    intro (u, x)
    simp [(recursive u).2] ⟩

private opaque tensor_multifactor_ind {K : Field} {V : VectorSpace K} (l : BinaryTree (VectorSpace K))
  (f : prod_set l → V) (h : Multilinear V l f)
  : { l : LinearMap (prod_tensor l) V // ∀ x, l (prod_tensorα x) = f x } := match l with
  | .leaf U =>
    ⟨ linear_leaf f h
    , λ _ => rfl ⟩
  | .node_left l V => by cases h with | cons_left _ map_smul map_add linear =>
      exact build_step_left f map_smul map_add
        λ u => tensor_multifactor_ind l (λ x => f (x, u)) (linear u)
  | .node_right U r => by cases h with | cons_right _ map_smul map_add linear =>
      exact build_step_right f map_smul map_add
        λ u => tensor_multifactor_ind r (λ x => f (u, x)) (linear u)

def tensor_multifactor {K : Field} {V : VectorSpace K} (l : BinaryTree (VectorSpace K))
  (f : prod_set l → V) (h : Multilinear V l f) : LinearMap (prod_tensor l) V :=
  (tensor_multifactor_ind l f h).1

def tensor_multifactor_val {K : Field} {V : VectorSpace K} (l : BinaryTree (VectorSpace K))
  (f : prod_set l → V) (h : Multilinear V l f) :
  ∀ x, tensor_multifactor l f h (prod_tensorα x) = f x :=
  (tensor_multifactor_ind l f h).2

theorem eq₃ {K : Field} {U V W E : VectorSpace K}
  (f g : LinearMap (tensor_space (tensor_space U V) W) E)
  (h : ∀ u v w, f (tensorα (tensorα u v) w) = g (tensorα (tensorα u v) w))
  : f = g := sorry

def assoc (K : Field) :
  ((tensor_bifunctor K ×c Category.identity (KVect K))
    ≫ tensor_bifunctor K) ⟶
  (Category.Product.assoc _ _ _ ≫
    (Category.identity (KVect K) ×c tensor_bifunctor K)
      ≫ tensor_bifunctor K)
  where
  map := λ ((U, V), W) => tensor_multifactor
      (.node_left (.node_left (.leaf U) V) W)
      (λ ((u, v), w) => tensorα u (tensorα v w))
    <| by
    apply Multilinear.cons_left
    intro (u, x) μ v; simp
    intro (u, x) v w; simp
    intro u₁
    apply Multilinear.cons_left
    intro u μ v; simp
    intro u v w; simp
    intro u₂
    apply Multilinear.one
    intro μ u; simp
    intro v w; simp
  naturality := by
    --intro ((U, V), W) ((U', V'), W') ((f, g), h)
    --apply eq₃
    sorry

def assoc_inv (K : Field) :
  (Category.Product.assoc _ _ _ ≫
    (Category.identity (KVect K) ×c tensor_bifunctor K)
      ≫ tensor_bifunctor K) ⟶ 
  ((tensor_bifunctor K ×c Category.identity (KVect K))
    ≫ tensor_bifunctor K)
  where
  map := λ ((U, V), W) => tensor_multifactor
      (.node_right U (.node_right V (.leaf W)))
      (λ (u, (v, w)) => tensorα (tensorα u v) w)
  <| by
    apply Multilinear.cons_right
    intro (u, x) μ v; simp
    intro (u, x) v w; simp
    intro u₁
    apply Multilinear.cons_right
    intro u μ v; simp
    intro u v w; simp
    intro u₂
    apply Multilinear.one
    intro μ u; simp
    intro v w; simp
  naturality := by
    /-intro ((U, V), W) ((U', V'), W') ((f, g), h)
    apply eq₃
    intro u v w
    simp-/
    sorry

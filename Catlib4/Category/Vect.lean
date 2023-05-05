
import Catlib4.Algebra.Vector.Multilinear
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

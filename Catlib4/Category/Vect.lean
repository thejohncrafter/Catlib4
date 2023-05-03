
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

private theorem map_id {V W : VectorSpace K} :
  tensor_factor (map_tensor_space
    (LinearMap.identity V)
    (LinearMap.identity W)) = LinearMap.identity _ := by
  apply map_tensor_ext
  apply BilinearMap.ext
  intro u v
  simp

private theorem map_comp {V W V' W' V'' W'' : VectorSpace K}
  {f : LinearMap V V'} {f' : LinearMap V' V''}
  {g : LinearMap W W'} {g' : LinearMap W' W''} :
  tensor_factor
    (map_tensor_space
      (LinearMap.compose f' f)
      (LinearMap.compose g' g))
  = LinearMap.compose
      (tensor_factor <| map_tensor_space f' g')
      (tensor_factor <| map_tensor_space f g) := by
  apply map_tensor_ext
  apply BilinearMap.ext
  intro u v
  simp

def tensor_bifunctor (K : Field) : KVect K ×c KVect K ⥤ KVect K where
  obj := λ (V, W) => tensor_space V W
  map := λ (f, g) => tensor_factor <| map_tensor_space f g
  map_id' := by
    intro (V, W)
    apply map_id
  map_comp' := by
    intro (V, W) (V', W') (V'', W'') (f, g) (f', g')
    apply map_comp

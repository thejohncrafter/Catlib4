
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

def tensor_bifunctor (K : Field) : KVect K ×c KVect K ⟶ KVect K where
  obj := λ (V, W) => tensor_space V W
  map := λ (f, g) => tensor_factor <| map_tensor_space f g
  map_id' := by
    intro (V, W)
    apply map_id
  map_comp' := by
    intro (V, W) (V', W') (V'', W'') (f, g) (f', g')
    apply map_comp

def c {K : Field} (U V W : VectorSpace K) (w : W) :
  BilinearMap U V (tensor_space U (tensor_space V W)) where
  f u v := tensorα u (tensorα v w)
  map_smul_l' := by simp
  map_smul_r' := by simp
  map_add_l' := by simp
  map_add_r' := by simp

def b {K : Field} (U V W : VectorSpace K) (w : W) :
  LinearMap (tensor_space U V) (tensor_space U (tensor_space V W)) :=
  tensor_factor (c U V W w)

@[simp] theorem b_parameter_smul {K : Field} {U V W : VectorSpace K}
  (μ : K) {w : W} {x : tensor_space U V} :
  b U V W (μ • w) x = μ • b U V W w x := by
  sorry

def a {K : Field} (U V W : VectorSpace K) :
  LinearMap (tensor_space (tensor_space U V) W) (tensor_space U (tensor_space V W)) :=
  tensor_factor
    { f := λ x w => b U V W w x
    , map_smul_l' := by simp
    , map_smul_r' := by simp
    , map_add_l' := by simp
    , map_add_r' := by
        sorry }

theorem a_eq {K : Field} {U V W : VectorSpace K} (u : U) (v : V) (w : W) :
  a U V W (tensorα (tensorα u v) w) = tensorα u (tensorα v w) := by
  simp [a, b, c]

theorem eq₃ {K : Field} {U V W E : VectorSpace K}
  (f g : LinearMap (tensor_space (tensor_space U V) W) E)
  (h : ∀ u v w, f (tensorα (tensorα u v) w) = g (tensorα (tensorα u v) w))
  : f = g := sorry

set_option trace.Meta.isDefEq true in
set_option maxHeartbeats 10000 in
def assoc (K : Field) :
  ((tensor_bifunctor K ×c Category.identity (KVect K)) ≫ tensor_bifunctor K) ⟶
    (Category.Product.assoc _ _ _
      ≫ (Category.identity (KVect K) ×c tensor_bifunctor K)
      ≫ tensor_bifunctor K) where
map := λ ((U, V), W) => a U V W
naturality := by
  intro ((U, V), W) ((U', V'), W') ((f, g), h) -- Tries to unfold `LinearMap.cokernel`
  sorry

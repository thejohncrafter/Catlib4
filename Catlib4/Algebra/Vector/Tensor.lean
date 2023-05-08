
import Catlib4.Algebra.VectorSpace
import Catlib4.Algebra.Vector.Linearized
import Catlib4.Algebra.Vector.Product
import Catlib4.Algebra.Vector.Quotient

open Classical

noncomputable section

structure BilinearMap {K : Field} (U V W : VectorSpace K) where
  f : U → V → W
  map_smul_l' : ∀ μ : K, ∀ u : U, ∀ v : V, f (μ • u) v = μ • f u v
  map_smul_r' : ∀ μ : K, ∀ u : U, ∀ v : V, f u (μ • v) = μ • f u v
  map_add_l' : ∀ v w : U, ∀ t : V, f (v + w) t = f v t + f w t
  map_add_r' : ∀ v : U, ∀ w t : V, f v (w + t) = f v w + f v t

instance {K : Field} (U V W : VectorSpace K) :
  CoeFun (BilinearMap U V W) (fun _ => U → V → W) where
  coe f := f.f

section

variable {K : Field} {U V W : VectorSpace K} (f : BilinearMap U V W)

@[simp] theorem BilinearMap.map_smul_l :
  ∀ μ : K, ∀ u : U, ∀ v : V, f (μ • u) v = μ • f u v := f.map_smul_l'

@[simp] theorem BilinearMap.map_smul_r :
  ∀ μ : K, ∀ u : U, ∀ v : V, f u (μ • v) = μ • f u v := f.map_smul_r'

@[simp] theorem BilinearMap.map_add_l :
  ∀ v w : U, ∀ t : V, f (v + w) t = f v t + f w t := f.map_add_l'

@[simp] theorem BilinearMap.map_add_r :
  ∀ v : U, ∀ w t : V, f v (w + t) = f v w + f v t := f.map_add_r'

end

theorem BilinearMap.eq {K : Field} {U V W : VectorSpace K} :
  ∀ {f g : BilinearMap U V W}, f.f = g.f → f = g
  | ⟨ _, _, _, _, _ ⟩, ⟨ _, _, _, _, _ ⟩, rfl => rfl

theorem BilinearMap.ext {K : Field} {U V W : VectorSpace K}
  {f g : BilinearMap U V W} (h : ∀ x y, f x y = g x y) : f = g :=
  BilinearMap.eq <| funext λ x => funext λ y => h x y

def BilinearMap.compose {K : Field} {U V W E : VectorSpace K}
  (f : LinearMap W E) (g : BilinearMap U V W) : BilinearMap U V E where
  f u v := f (g u v)
  map_smul_l' := by simp
  map_smul_r' := by simp
  map_add_l' := by simp
  map_add_r' := by simp

@[simp] theorem BilinearMap.compose_val {K : Field} {U V W E : VectorSpace K}
  (f : LinearMap W E) (g : BilinearMap U V W)
  (u : U) (v : V) : BilinearMap.compose f g u v = f (g u v) := rfl

def vanish_map_smul_l {K : Field} {U V : VectorSpace K} (u : U) (v : V) :
  LinearMap (linearized K K) (linearized K <| U × V) :=
  linearizeF λ μ => μ • l[(u, v)] + -l[(μ • u, v)]

def vanish_map_smul_r {K : Field} {U V : VectorSpace K} (u : U) (v : V) :
  LinearMap (linearized K K) (linearized K <| U × V) :=
  linearizeF λ μ => μ • l[(u, v)] + -l[(u, μ • v)]

def vanish_map_add_l {K : Field} (U : VectorSpace K) {V : VectorSpace K} (w : V) :
  LinearMap (linearized K <| U × U) (linearized K <| U × V) :=
  linearizeF λ (u, v) => l[(u + v, w)] + -l[(u, w)] + -l[(v, w)]

def vanish_map_add_r {K : Field} {U : VectorSpace K} (u : U) (V : VectorSpace K) :
  LinearMap (linearized K <| V × V) (linearized K <| U × V) :=
  linearizeF λ (v, w) => l[(u, v + w)] + -l[(u, v)] + -l[(u, w)]

def bilinear_as_from_linearized {K : Field} {U V W : VectorSpace K}
  (f : BilinearMap U V W) : LinearMap (linearized K <| U × V) W where
  f := linearizeF λ (u, v) => f u v
  map_smul' := by simp
  map_add' := by simp

theorem factor_vanish_map_smul_l {K : Field} {U V W : VectorSpace K}
  {u : U} {v : V} {f : BilinearMap U V W} :
  LinearMap.compose (bilinear_as_from_linearized f) (vanish_map_smul_l u v)
    = LinearMap.zero (linearized K K) W := by
  apply factor_of_vanish
  simp [bilinear_as_from_linearized]

theorem factor_vanish_map_smul_r {K : Field} {U V W : VectorSpace K}
  {u : U} {v : V} {f : BilinearMap U V W} :
  LinearMap.compose (bilinear_as_from_linearized f) (vanish_map_smul_r u v)
    = LinearMap.zero (linearized K K) W := by
  apply factor_of_vanish
  simp [bilinear_as_from_linearized]

theorem factor_vanish_map_add_l {K : Field} {U V W : VectorSpace K}
  {w : V} {f : BilinearMap U V W} :
  LinearMap.compose (bilinear_as_from_linearized f) (vanish_map_add_l U w)
    = LinearMap.zero _ W := by
  apply factor_of_vanish
  intro ⟨ u, v ⟩
  suffices f (u + v) w + (-1 : K) • f u w + (-1 : K) • f v w = 0 by
    simp_all [bilinear_as_from_linearized]
  conv =>
    enter [1]
    rw [← W.add_assoc]
    enter [2]
    rw [← W.smul_add, ← f.map_add_l
      , ← W.neg_eq_neg_one_smul]
  simp

theorem factor_vanish_map_add_r {K : Field} {U V W : VectorSpace K}
  {u : U} {f : BilinearMap U V W} :
  LinearMap.compose (bilinear_as_from_linearized f) (vanish_map_add_r u V)
    = LinearMap.zero _ W := by
  apply factor_of_vanish
  intro ⟨ v, w ⟩
  suffices f u (v + w) + (-1 : K) • f u v + (-1 : K) • f u w = 0 by
    simp_all [bilinear_as_from_linearized]
  conv =>
    enter [1]
    rw [← W.add_assoc]
    enter [2]
    rw [← W.smul_add, ← f.map_add_r
      , ← W.neg_eq_neg_one_smul]
  simp

inductive ProdSupport {K : Field} (U V : VectorSpace K) where
  | smul_l (u : U) (v : V)
  | smul_r (u : U) (v : V)
  | add_l (w : V)
  | add_r (u : U)

def diagram_space {K : Field} (U V : VectorSpace K) :
  ProdSupport U V → VectorSpace K
  | .smul_l _ _ => linearized K K
  | .smul_r _ _ => linearized K K
  | .add_l _ => linearized K (U × U)
  | .add_r _ => linearized K (V × V)

def diagram_map {K : Field} (U V : VectorSpace K) :
  LinearMap (VectorSpace.product (diagram_space U V)) (linearized K <| U × V) :=
  VectorSpace.map_product λ x => match x with
  | .smul_l u v => vanish_map_smul_l u v
  | .smul_r u v => vanish_map_smul_r u v
  | .add_l w => vanish_map_add_l U w
  | .add_r u => vanish_map_add_r u V

theorem factor_vanish_diagram {K : Field} {U V W : VectorSpace K} (f : BilinearMap U V W) :
  LinearMap.compose (bilinear_as_from_linearized f) (diagram_map U V)
    = LinearMap.zero _ W := by
  apply Product.factor_of_vanish
  intro a
  match a with
  | .smul_l u v => apply factor_vanish_map_smul_l
  | .smul_r u v => apply factor_vanish_map_smul_r
  | .add_l w => apply factor_vanish_map_add_l
  | .add_r u => apply factor_vanish_map_add_r

def tensor_space {K : Field} (U V : VectorSpace K) : VectorSpace K :=
  (diagram_map U V).cokernel

def projectorF {K : Field} (U V : VectorSpace K) :=
  (diagram_map U V).cokernel_projector

def from_linearized_as_bilinear {K : Field} {U V W : VectorSpace K}
  (f : LinearMap (linearized K <| U × V) W)
  (h : LinearMap.compose f (diagram_map U V) = LinearMap.zero _ _)
  : BilinearMap U V W where
  f u v := f l[(u, v)]
  map_smul_l' := by
    intro μ u v
    suffices p : f (μ • l[(u, v)] + - l[(μ • u, v)]) = 0 by
      rw [f.map_add, f.map_neg, f.map_smul] at p
      simp [W.eq_of_sum_zero _ _ p]
    have p := congrFun (congrArg LinearMap.f h) (Product.pure_elem _ (ProdSupport.smul_l u v) l[μ])
    revert p
    simp [diagram_map, vanish_map_smul_l]
    exact id -- weird proof pattern
  map_smul_r' := by
    intro μ u v
    suffices p : f (μ • l[(u, v)] + - l[(u, μ • v)]) = 0 by
      rw [f.map_add, f.map_neg, f.map_smul] at p
      simp [W.eq_of_sum_zero _ _ p]
    have p := congrFun (congrArg LinearMap.f h) (Product.pure_elem _ (ProdSupport.smul_r u v) l[μ])
    revert p
    simp [diagram_map, vanish_map_smul_r]
    exact id -- weird proof pattern
  map_add_l' := by
    intro u v w
    suffices p : f (l[(u + v, w)] + - l[(u, w)] + -l[(v, w)]) = 0 by
      sorry
    have p := congrFun (congrArg LinearMap.f h) (Product.pure_elem _ (ProdSupport.add_l w) l[(u, v)])
    revert p
    simp [diagram_map, vanish_map_add_l]
    exact id -- weird proof pattern
  map_add_r' := by
    intro u v w
    suffices p : f (l[(u, v + w)] + - l[(u, v)] + -l[(u, w)]) = 0 by
      sorry
    have p := congrFun (congrArg LinearMap.f h) (Product.pure_elem _ (ProdSupport.add_r u) l[(v, w)])
    revert p
    simp [diagram_map, vanish_map_add_r]
    exact id -- weird proof pattern

theorem bilinear_as_from_linearized_eq {K : Field} {U V W : VectorSpace K}
  (f g : BilinearMap U V W)
  (h : bilinear_as_from_linearized f = bilinear_as_from_linearized g)
  : f = g := by
  have h' := congrArg LinearMap.f h
  simp only [bilinear_as_from_linearized] at h'
  apply BilinearMap.ext
  intro x y
  let p := congrFun h' l[(x, y)]
  simp only [linearize_val] at p
  exact p

theorem bilinear_as_from_linearized_map {K : Field} {U V W E : VectorSpace K}
  (f : LinearMap W E) (g : BilinearMap U V W) :
  bilinear_as_from_linearized (BilinearMap.compose f g) =
    LinearMap.compose f (bilinear_as_from_linearized g) := by
  apply LinearMap.ext
  intro x
  induction x using linearize.inductionOn with
  | pure x => simp [bilinear_as_from_linearized, BilinearMap.compose]
  | smul μ x hx => simp [hx]
  | add x y hx hy => simp [hx, hy]
  | zero => simp

theorem linearize_bilinearize {K : Field} {U V W : VectorSpace K}
  (f : LinearMap (linearized K <| U × V) W)
  (h : LinearMap.compose f (diagram_map U V) = LinearMap.zero _ _) :
  bilinear_as_from_linearized (from_linearized_as_bilinear f h) = f := by
  apply LinearMap.ext
  intro x
  induction x using linearize.inductionOn with
  | pure x => simp [from_linearized_as_bilinear, bilinear_as_from_linearized]
  | smul μ x hx => simp [hx]
  | add x y hx hy => simp [hx, hy]
  | zero => simp

def tensor_factor {K : Field} {U V W : VectorSpace K} (f : BilinearMap U V W) :
  LinearMap (tensor_space U V) W :=
  (diagram_map U V).cokernel_factor
    (bilinear_as_from_linearized f)
    (factor_vanish_diagram f)

def tensorα {K : Field} {U V : VectorSpace K} : BilinearMap U V (tensor_space U V) :=
  from_linearized_as_bilinear (diagram_map U V).cokernel_projector cokernel_vanish

theorem tensor_factor_sound {K : Field} {U V W : VectorSpace K} (f : BilinearMap U V W) :
  f = BilinearMap.compose (tensor_factor f) tensorα := by
  let p := @factor_sound _ _ _ (diagram_map U V) _ (bilinear_as_from_linearized f) (factor_vanish_diagram f)
  apply bilinear_as_from_linearized_eq
  rw [p, tensor_factor, tensorα]
  rw [bilinear_as_from_linearized_map, linearize_bilinearize]

@[simp] theorem tensor_factor_val {K : Field} {U V W : VectorSpace K} (f : BilinearMap U V W) :
  ∀ {x y}, tensor_factor f (tensorα x y) = f x y := by
  intro x y
  conv => rhs; rw [tensor_factor_sound f]

theorem map_tensor_ext {K : Field} {U V W : VectorSpace K}
  {f g : LinearMap (tensor_space U V) W}
  (h : BilinearMap.compose f tensorα = BilinearMap.compose g tensorα)
  : f = g := by
  apply eq_from_eq_compose_proj
  apply LinearMap.ext
  intro x
  induction x using linearize.inductionOn with
  | pure x =>
    let (u, v) := x
    let p := congrFun (congrFun (congrArg BilinearMap.f h) u) v
    exact p
  | smul μ x hx =>
    simp only [LinearMap.map_smul]
    rw [hx]
  | add x y hx hy =>
    simp only [LinearMap.map_add]
    rw [hx, hy]
  | zero => simp

theorem TensorMap.ext {K : Field} {U V W : VectorSpace K}
  {f g : LinearMap (tensor_space U V) W}
  (h : ∀ u v, f (tensorα u v) = g (tensorα u v)) : f = g :=
  map_tensor_ext <| BilinearMap.ext h

attribute [irreducible] tensor_space

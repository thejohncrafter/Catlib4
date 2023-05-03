
import Catlib4.Algebra.VectorSpace
import Catlib4.Algebra.Vector.FiniteSupport

open Classical

noncomputable section

def fspace {K : Field} {α : Type} (Φ : α → VectorSpace K) := (a : α) → Φ a

def fsupport {K : Field} {α : Type} {Φ : α → VectorSpace K} (f : fspace Φ) :=
  { x : α // f x ≠ 0 }

def finite_fspace {K : Field} {α : Type} (Φ : α → VectorSpace K) :=
  { f : fspace Φ // finite (fsupport f) }

def finite_fspace.sum_support {K : Field} {α : Type} {Φ : α → VectorSpace K}
  {V : VectorSpace K} (f : finite_fspace Φ) (g : (a : α) → LinearMap (Φ a) V) :=
  finite_sum f.2 λ ⟨ x, _ ⟩ => g x (f.1 x)

def VectorSpace.product {K : Field} {α : Type} (Φ : α → VectorSpace K) : VectorSpace K where
  α := finite_fspace Φ
  add := λ ⟨ f, p ⟩ ⟨ g, q ⟩ =>
    ⟨ λ a => f a + g a
    , sorry ⟩
  neg := λ ⟨ f, p ⟩ =>
    ⟨ λ a => - f a
    , sorry ⟩
  zero := ⟨ λ _ => 0, sorry ⟩
  smul μ := λ ⟨ f, p ⟩ =>
    ⟨ λ a => μ • f a
    , sorry ⟩
  add_zero' := sorry
  zero_add' := sorry
  add_assoc' := sorry
  add_comm' := sorry
  add_neg' := sorry
  smul_smul' := sorry
  smul_add' := sorry
  smul_zero' := sorry
  add_smul' := sorry
  zero_smul' := sorry
  one_smul' := sorry

def VectorSpace.map_product {K : Field} {α : Type} {Φ : α → VectorSpace K} {V : VectorSpace K}
  (φ : (a : α) → LinearMap (Φ a) V) : LinearMap (product Φ) V where
  f f := f.sum_support φ
  map_smul' := sorry
  map_add' := sorry

theorem Product.factor_of_vanish {K : Field} {α : Type} {V W : VectorSpace K}
  {Φ : α → VectorSpace K} (φ : (a : α) → LinearMap (Φ a) V) {g : LinearMap V W}
  (h : ∀ a : α, LinearMap.compose g (φ a) = LinearMap.zero _ _) :
  LinearMap.compose g (VectorSpace.map_product φ)
    = LinearMap.zero (VectorSpace.product Φ) W := by
  sorry

def Product.pure_elem {K : Field} {α : Type} (Φ : α → VectorSpace K)
  (x : α) (v : Φ x) : VectorSpace.product Φ :=
  ⟨ λ y => if p : x = y then p ▸ v else 0
  , sorry ⟩

def pure_elem_support_nz {K : Field} {α : Type} (Φ : α → VectorSpace K)
  (x : α) (v : Φ x) (h : v ≠ 0) : Fintype (fsupport (Product.pure_elem Φ x v).1) where
  elems :=
    { val := Quotient.mk _ [⟨ x, by simp [Product.pure_elem, h] ⟩]
    , nodup := sorry }
  complete := by
    sorry

def pure_elem_support {K : Field} {α : Type} (Φ : α → VectorSpace K)
  (x : α) (v : Φ x) : Fintype (fsupport (Product.pure_elem Φ x v).1) :=
  if p : v = 0 then
    { elems :=
      { val := Quotient.mk _ []
      , nodup := sorry }
    , complete := by 
        sorry }
  else pure_elem_support_nz Φ x v p

@[simp]
theorem map_pure_elem {K : Field} {α : Type} {Φ : α → VectorSpace K} {V : VectorSpace K}
  (φ : (a : α) → LinearMap (Φ a) V) (x : α) (v : Φ x)
  : VectorSpace.map_product φ (Product.pure_elem Φ x v) = φ x v := by
  simp only [VectorSpace.map_product, Product.pure_elem, finite_fspace.sum_support]
  rw [finite_sum_val (pure_elem_support Φ x v)]
  sorry

--theorem map_product_zero_of_maps_zero {K : Field} {α : Type} {Φ : α → VectorSpace K} {V : VectorSpace K}
--  {φ : (a : α) → LinearMap (Φ a) V}
--  (h : ∀ a : α, )

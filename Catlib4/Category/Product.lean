
import Catlib4.Basic
import Catlib4.Category.Category
import Catlib4.Category.Remarkable

namespace CategoryTheory.Category

universe u v

def product_category (C D : Category.{u,v+1}) : Category.{u,v+1} where
  α := C × D
  hom a b := (a.1 ⟶ b.1) × (a.2 ⟶ b.2)
  id a := (𝟙 a.1, 𝟙 a.2)
  comp f g := (f.1 ≫ g.1, f.2 ≫ g.2)
  id_comp' _ := Prod.ext' (C.id_comp _) (D.id_comp _)
  comp_id' _ := Prod.ext' (C.comp_id _) (D.comp_id _)
  assoc' _ _ _ := Prod.ext' (C.assoc _ _ _) (D.assoc _ _ _)

instance : HasCatProduct Category Category Category where
  catProduct := product_category

instance {C D : Category.{u,v+1}} : HasHom (C.α × D.α) :=
  inferInstanceAs (HasHom (C ×c D))

unif_hint (C D : Category) (c : C) (d d' : D) (x : C ×c D) where
  x =?= (c, d)
  ⊢ d' =?= x.2

unif_hint (C D : Category) (c c' : C) (d : D) (x : C ×c D) where
  x =?= (c, d)
  ⊢ c' =?= x.1

namespace Product

def assoc (A B C : Category) : ((A ×c B) ×c C) ⟶ (A ×c (B ×c C)) where
  obj := λ ((a, b), c) => (a, (b, c))
  map := λ ((f, g), h) => (f, (g, h))
  map_id' := λ _ => rfl
  map_comp' := λ _ _ => rfl

@[simp] theorem assoc_obj {A B C : Category} (a : A) (b : B) (c : C) :
  (assoc A B C).obj ((a, b), c) = (a, (b, c)) := rfl

@[simp] theorem assoc_map {A B C : Category}
  {a a' : A} {b b' : B} {c c' : C}
  (f : a ⟶ a') (g : b ⟶ b') (h : c ⟶ c') :
  (assoc A B C).map ((f, g), h) = (f, (g, h)) := rfl

def assoc_inv (A B C : Category) : (A ×c (B ×c C)) ⟶ ((A ×c B) ×c C) where
  obj := λ (a, b, c) => ((a, b), c)
  map := λ (f, g, h) => ((f, g), h)
  map_id' := λ _ => rfl
  map_comp' := λ _ _ => rfl

@[simp] theorem assoc_inv_obj {A B C : Category} (a : A) (b : B) (c : C) :
  (assoc_inv A B C).obj (a, (b, c)) = ((a, b), c) := rfl

def symm (A B : Category) : (A ×c B) ⟶ (B ×c A) where
  obj := λ (a, b) => (b, a)
  map := λ (f, g) => (g, f)
  map_id' := λ _ => rfl
  map_comp' := λ _ _ => rfl

@[simp] theorem symm_obj {A B : Category} (a : A) (b : B) :
  (symm A B).obj (a, b) = (b, a) := rfl

set_option trace.Meta.isDefEq true in
@[simp] theorem symm_map {A B : Category.{u,v+1}}
  {a a' : A} {b b' : B}
  (f : a ⟶ a') (g : b ⟶ b') : (symm A B).map (f, g) = (g, f) := rfl

theorem symmetric (A B : Category) : symm A B ≫ symm B A = 𝟙 (A ×c B) := rfl

def functor_product {A B C D : Category} (F : A ⟶ C) (G : B ⟶ D) : A ×c B ⟶ C ×c D where
  obj := λ (x, y) => (F.obj x, G.obj y)
  map f := (F.map f.1, G.map f.2)
  map_id' _ := Prod.ext' (F.map_id _) (G.map_id' _)
  map_comp' _ _ := Prod.ext' (F.map_comp _ _) (G.map_comp _ _)

instance {A B C D : Category} : HasCatProduct (A ⟶ C) (B ⟶ D) (A ×c B ⟶ C ×c D) where
  catProduct := functor_product

@[simp] theorem functor_product_obj {A B C D : Category} (F : A ⟶ C) (G : B ⟶ D)
  (a : A) (b : B) : (F ×c G).obj (a, b) = (F.obj a, G.obj b) := rfl

@[simp] theorem functor_product_map {A B C D : Category} (F : A ⟶ C) (G : B ⟶ D)
  {a a' : A} {b b' : B} (f : a ⟶ a') (g : b ⟶ b') :
  (F ×c G).map (f, g) = (F.map f, G.map g) := by
    simp [HasCatProduct.catProduct, functor_product]

def unit_left (C : Category) : (1 : Category) ×c C ⟶ C where
  obj := λ (_, a) => a
  map := λ (_, f) => f
  map_id' _ := rfl
  map_comp' _ _ := rfl

def unit_left_inv (C : Category) : C ⟶ (1 : Category) ×c C where
  obj := λ a => (PUnit.unit, a)
  map := λ f => (PUnit.unit, f)
  map_id' _ := rfl
  map_comp' _ _ := rfl

def unit_right (C : Category) : C ×c (1 : Category) ⟶ C where
  obj := λ (a, _) => a
  map := λ (f, _) => f
  map_id' _ := rfl
  map_comp' _ _ := rfl

def unit_right_inv (C : Category) : C ⟶ C ×c (1 : Category) where
  obj := λ a => (a, PUnit.unit)
  map := λ f => (f, PUnit.unit)
  map_id' _ := rfl
  map_comp' _ _ := rfl

end Product

end CategoryTheory.Category

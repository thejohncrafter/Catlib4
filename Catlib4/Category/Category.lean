
import Catlib4.Basic

namespace CategoryTheory

namespace Category

def identity' (C : Category) : C ⥤ C where
  obj := id
  map := id
  map_id' _ := rfl
  map_comp' := λ _ _ => rfl

def compose {A B C : Category} (F : A ⥤ B) (G : B ⥤ C) : A ⥤ C where
  obj a := G.obj (F.obj a)
  map f := G.map (F.map f)
  map_id' := by simp [F.map_id, G.map_id]
  map_comp' {x y z f g} := by
    simp only []
    rw [F.map_comp, G.map_comp]

def category_category : Category.{max u v + 1, max u v + 1} where
  α := Category.{u,v}
  hom C D := C ⥤ D
  id := identity'
  comp := compose
  id_comp' {_ _ _} := rfl
  comp_id' {_ _ _} := rfl
  assoc' {_ _ _ _ _ _ _} := rfl

instance : HasHom Category := inferInstanceAs (HasHom category_category.α)
instance : HasIso Category := inferInstanceAs (HasIso category_category.α)
instance : HasComp Category := inferInstanceAs (HasComp category_category.α)
instance : HasIdentity Category := inferInstanceAs (HasIdentity category_category.α)
instance (C D : Category) : HasHom (C ⟶ D) := inferInstanceAs (HasHom (C ⥤ D))
instance (C D : Category) : HasIso (C ⟶ D) := inferInstanceAs (HasIso (C ⥤ D))

def identity (C : Category) : C ⟶ C := identity' C

@[simp] theorem identity_obj {C : Category} (c : C) :
  (identity C).obj c = c := rfl

@[simp] theorem identity_map {C : Category} {c d : C} (f : c ⟶ d) :
  (identity C).map f = f := rfl

end Category

def Functor.constant (C : Category) {D : Category} (a : D) : C ⟶ D := Functor.constant' C a

@[simp] theorem Functor.comp_obj {A B C : Category}
  (F : A ⟶ B) (G : B ⟶ C) (x : A) : (F ≫ G).obj x = G.obj (F.obj x) := rfl

@[simp] theorem Functor.comp_map {A B C : Category}
  {a a' : A} (F : A ⟶ B) (G : B ⟶ C)
  (f : a ⟶ a') : (F ≫ G).map f = G.map (F.map f) := rfl

@[simp] theorem Functor.constant_obj (C : Category) {D : Category} (a : D) :
  ∀ x : C, (Functor.constant C a).obj x = a := λ _ => rfl

end CategoryTheory

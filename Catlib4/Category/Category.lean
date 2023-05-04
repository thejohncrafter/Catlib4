
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

end Category

def Functor.constant (C : Category) {D : Category} (a : D) : C ⟶ D := Functor.constant' C a

end CategoryTheory

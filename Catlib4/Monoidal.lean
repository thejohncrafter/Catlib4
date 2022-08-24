
import Catlib4.Basic
import Catlib4.Category.Category
import Catlib4.Category.Product

namespace CategoryTheory

universe u v

structure MonoidalStructure : Type (max (u+1) (v+2)) where
  C : Category.{u,v+1}
  M : C ×c C ⥤ C
  I : C

instance : Coe MonoidalStructure Category where
  coe C := C.C

instance : CoeSort MonoidalStructure (Type u) where
  coe C := C.C.α

instance (C : MonoidalStructure.{u,v}) : HasTensor C C C where
  tensor a b := C.M.obj (a, b)

instance (C : MonoidalStructure.{u,v}) {x₁ y₁ x₂ y₂ : C} :
  HasTensor (x₁ ⟶ y₁) (x₂ ⟶ y₂) (x₁ ⊗ x₂ ⟶ y₁ ⊗ y₂)
where tensor f g := C.M.map (f, g)

instance (C : MonoidalStructure.{u,v}) : HasTensorUnit C C where
  unit := C.I

structure MonoidalCategory extends MonoidalStructure where
  associator : ((M ×c Category.identity C) ≫ M) ≅
    (Category.Product.assoc _ _ _ ≫ (Category.identity C ×c M) ≫ M)
  left_unitor :
    (Category.Product.unit_left_inv C
    ≫ (Functor.constant (1 : Category) I ×c Category.identity C)
    ≫ M) ≅ (Category.identity C)
  right_unitor :
    (Category.Product.unit_right_inv C
    ≫ (Category.identity C ×c Functor.constant (1 : Category) I)
    ≫ M) ≅ (Category.identity C)
  triangle : ∀ x y : C,
    associator.hom.map ((x, I), y) ≫ (𝟙 x ⊗ left_unitor.hom.map y)
    = right_unitor.hom.map x ⊗ 𝟙 y
  pentagon : ∀ w x y z : C,
    associator.hom.map (((w ⊗ x), y), z)
    ≫ associator.hom.map ((w, x), y ⊗ z)
    = (associator.hom.map ((w, x), y) ⊗ 𝟙 z)
    ≫ associator.hom.map ((w, x ⊗ y), z)
    ≫ (𝟙 w ⊗ associator.hom.map ((x, y), z))

end CategoryTheory

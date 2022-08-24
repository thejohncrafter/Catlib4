
import Catlib4.Basic

namespace CategoryTheory.Category

universe u

def cat_one : Category.{u,v} where
  α := PUnit.{u+1}
  hom := λ _ _ => PUnit.{v}
  id _ := PUnit.unit
  comp _ _ := PUnit.unit
  id_comp' _ := rfl
  comp_id' _ := rfl
  assoc' _ _ _ := rfl

instance : OfNat Category (nat_lit 1) where
  ofNat := cat_one

namespace CategoryTheory.Category


section

universe u v

class HasHom (α : Type u) : Sort (max u v + 1) where
  hom : α → α → Sort v

infixr:10 "⟶" => HasHom.hom -- \h

class HasIdentity (α : Type u) [HasHom α] where
  identity : ∀ a : α, a ⟶ a

notation "𝟙" => HasIdentity.identity -- \b1

class HasComp (α : Type u) [HasHom α] where
  comp : ∀ {a b c : α}, (a ⟶ b) → (b ⟶ c) → (a ⟶ c)

infixr:80 "≫" => HasComp.comp -- \gg

class HasIso (α : Type u) : Sort (max u v + 1) where
  iso : α → α → Sort v

infixr:10 "≅" => HasIso.iso

class HasTensorUnit (α : Type u) (β : Type v) where
  unit : β

notation "𝟙_" => HasTensorUnit.unit

end

section

universe u v w

class HasComp' (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  comp' : α → β → γ

infixr:80 "⋙" => HasComp'.comp'

class HasHComp (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hcomp : α → β → γ

infixr:80 "◫" => HasHComp.hcomp

class HasCatProduct (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  catProduct : α → β → γ

infixr:35 "×c" => HasCatProduct.catProduct

class HasTensor (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  tensor : α → β → γ

infixr:70 "⊗" => HasTensor.tensor

end

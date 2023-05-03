
class SMul (α χ : Type u) where
  smul : α → χ → χ

infixr:73 " • " => SMul.smul

abbrev ℕ := Nat

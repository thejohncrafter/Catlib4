
class SMul (α χ : Type u) where
  smul : α → χ → χ

infixr:73 " • " => SMul.smul

class LSMul (α χ : Type u) where
  lmul : α → χ → χ

infixr:73 " •ₗ " => LSMul.lmul

class RSMul (χ α : Type u) where
  rmul : χ → α → χ

infixl:73 " •ᵣ " => RSMul.rmul

abbrev ℕ := Nat

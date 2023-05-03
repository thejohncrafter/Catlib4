
import Catlib4.Algebra.VectorSpace

def Vector.product {K : Field} {α : Type} (Φ : α → VectorSpace K) : VectorSpace K where
  α := (a : α) → Φ a
  add := λ f g a => f a + g a
  neg := λ f a => - f a
  zero := λ _ => 0
  smul μ := λ f a => μ • f a
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

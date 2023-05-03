
import Catlib4.Groundwork.Finite
import Catlib4.Algebra.VectorSpace

open Classical

noncomputable section

def support {α : Type} {A : Ring} (f : α → A) := { x : α // f x ≠ 0 }

def finite_support (α : Type) (K : Field) := { f : α → K // finite (support f) }

theorem finite_support.eq {α : Type} {K : Field} {φ ψ : finite_support α K}
  : φ.1 = ψ.1 → φ = ψ := Subtype.eq 

def map_supports {K : Field} {α : Type} (μ : K) (f : α → K) :
  support (λ x => μ * f x) → support f :=
  λ ⟨ x, q ⟩ => by
    apply Subtype.mk x
    by_cases h : μ = 0
    exact False.elim <| q <| h ▸ K.zero_mul _
    exact λ h' => q <| show μ * f x = 0 from h'.symm ▸ K.mul_zero _

theorem map_supports_injective {K : Field} {α : Type} {μ : K} {f : α → K} :
  injective (map_supports μ f) :=
  λ _ _ h => Subtype.eq <| Subtype.noConfusion h id

--def map_supports' {K : Field} {α : Type} (μ : K) (f g : α → K) :
--  support (λ x => f x + g x) → support f ⊕ support g :=
--  λ ⟨ x, q ⟩ => by
--    sorry

def List.sum {α : Type} {K : Field} {V : VectorSpace K} : List α → (α → V) → V
  | [], _ => 0
  | u :: t, f => f u + t.sum f

theorem List.sum_perm {α : Type} {K : Field} {V : VectorSpace K} {f : α → V}
  {l₁ l₂ : List α} (h : List.perm l₁ l₂) :
  l₁.sum f = l₂.sum f := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [sum, ih]
  | swap x y l => simp [sum, V.add_comm (f x) (f y)]
  | trans h h' ih ih' => rw [ih, ih']

def Multiset.sum {α : Type} {K : Field} {V : VectorSpace K} (f : α → V) : Multiset α → V :=
  Quotient.lift (List.sum · f) <| by apply List.sum_perm

def Finset.sum {α : Type} {K : Field} {V : VectorSpace K} (s : Finset α) (f : α → V) :
  V := s.val.sum f

def finite_sum {K : Field} {V : VectorSpace K} {α : Type} (h : finite α) (f : α → V) : V :=
  (fintype_of_finite h).elems.sum f

theorem finite_sum_val {α : Type} {K : Field} {V : VectorSpace K} {f : α → V}
  {h : finite α} (fin : Fintype α) : finite_sum h f = fin.elems.sum f := by
  simp only [finite_sum]
  congr
  apply fintype_singleton

def finite_support.sum_support {α : Type} {K : Field} {V : VectorSpace K}
  (f : finite_support α K) (g : α → V) := finite_sum f.2 (λ ⟨ x, _ ⟩ => f.1 x • g x)

inductive List.perm : List α → List α → Prop where
  | nil : perm nil nil
  | cons (x : α) {l₁ l₂ : List α} (h : perm l₁ l₂) : perm (x :: l₁) (x :: l₂)
  | swap (x y : α) (l : List α) : perm (x :: y :: l) (y :: x :: l)
  | trans {l₁ l₂ l₃} (h : perm l₁ l₂) (h' : perm l₂ l₃) : perm l₁ l₃

theorem List.multiset_equivalence {α : Type} : Equivalence (@perm α) where
  refl x := by
    induction x with
    | nil => exact .nil
    | cons u _ ih => exact .cons u ih
  symm := λ {x y} h => by
    induction h with
    | nil => exact .nil
    | cons x _ ih => exact .cons x ih
    | swap x y l => exact .swap y x l
    | trans _ _ ih ih' => exact .trans ih' ih
  trans := λ {x y z} h h' => .trans h h'

instance List.multiset_setoid (α : Type) : Setoid (List α) where
  r := perm
  iseqv := multiset_equivalence

def Multiset (α : Type) := Quotient (List.multiset_setoid α)

inductive List.pairwise (R : α → α → Prop) : List α → Prop
  | nil : pairwise R []
  | cons {a : α} {l : List α}
    (h : ∀ a' : α, a' ∈ l → R a a') (h' : pairwise R l) : pairwise R (a :: l)

def List.nodup {α : Type} := List.pairwise (λ x y : α => x ≠ y)

def Multiset.nodup {α : Type} : Multiset α → Prop :=
  Quotient.lift List.nodup <| by
    intro l₁ l₂ h
    apply propext
    sorry

structure Finset (α : Type) where
  val : Multiset α
  nodup : val.nodup

instance (α : Type) : Membership α (Finset α) where
  mem a s := Quotient.lift (λ l => a ∈ l) sorry s.val

structure Fintype (α : Type) where
  elems : Finset α
  complete : ∀ a : α, a ∈ elems

theorem Finset.ext_iff {α : Type} {s₁ s₂ : Finset α} : s₁ = s₂ ↔ ∀ a : α, a ∈ s₁ ↔ a ∈ s₂ := by
  sorry

theorem fintype_singleton {α : Type} {x y : Fintype α} : x = y := by
  let ⟨ x, p ⟩ := x
  let ⟨ y, q ⟩ := y
  congr
  simp [Finset.ext_iff, p, q]

def injective {α β : Type} (f : α → β) :=
  ∀ x y : α, f x = f y → x = y

theorem comp_injective {α β γ : Type} {f : β → γ} {g : α → β}
  (h₁ : injective f) (h₂ : injective g) : injective (f ∘ g) :=
  λ _ _ h => h₂ _ _ <| h₁ _ _ h

def finite (α : Type) := ∃ n : Nat, ∃ φ : α → Fin n, injective φ

def fintype_of_finite {α : Type} (h : finite α) : Fintype α where
  elems := sorry
  complete := sorry

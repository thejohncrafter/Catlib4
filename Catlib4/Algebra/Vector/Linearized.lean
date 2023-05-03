
import Catlib4.Groundwork.Finite
import Catlib4.Algebra.VectorSpace

open Classical

noncomputable section

def support {α : Type} {A : Ring} (f : α → A) := { x : α // f x ≠ 0 }

def finite_support (α : Type) (K : Field) := { f : α → K // finite (support f) }

structure BilinearMap {K : Field} (U V W : VectorSpace K) where
  f : U → V → W
  map_smul_l : ∀ μ : K, ∀ u : U, ∀ v : V, f (μ • u) v = μ • f u v
  map_smul_r : ∀ μ : K, ∀ u : U, ∀ v : V, f u (μ • v) = μ • f u v
  map_add_l : ∀ v w : U, ∀ t : V, f (v + w) t = f v t + f w t
  map_add_r : ∀ v : U, ∀ w t : V, f v (w + t) = f v w + f v t

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

def linearized (K : Field) (α : Type) : VectorSpace K where
  α := finite_support α K
  add := λ ⟨ f, p ⟩ ⟨ g, q ⟩ =>
    ⟨ λ x => f x + g x
    , by
      sorry ⟩
  neg := λ ⟨ f, p ⟩ =>
    ⟨ λ x => - f x
    , by
      conv => enter [1, 1, x]; rw [K.neg_eq_neg_one_mul]
      let ⟨ n, φ, p ⟩ := p
      apply Exists.intro n
      apply Exists.intro (φ ∘ map_supports (-1) f)
      exact comp_injective p map_supports_injective ⟩
  zero :=
    ⟨ λ _ => 0
    , by
      apply Exists.intro 0
      apply Exists.intro λ x => False.elim (x.2 rfl)
      intro x _ _
      apply False.elim (x.2 rfl) ⟩
  smul := λ μ ⟨ f, p ⟩ =>
    ⟨ λ x => μ * f x
    , by
      let ⟨ n, φ, p ⟩ := p
      apply Exists.intro n
      apply Exists.intro (φ ∘ map_supports μ f)
      exact comp_injective p map_supports_injective ⟩
  add_zero' _ := Subtype.eq ∘ funext <| λ _ => K.add_zero _
  zero_add' _ := Subtype.eq ∘ funext <| λ _ => K.zero_add _
  add_assoc' _ _ _ := Subtype.eq ∘ funext <| λ _ => K.add_assoc _ _ _
  add_comm' _ _ := Subtype.eq ∘ funext <| λ _ => K.add_comm _ _
  add_neg' _ := Subtype.eq ∘ funext <| λ _ => K.add_neg _
  smul_smul' _ _ _ := Subtype.eq ∘ funext <| λ _ => K.mul_assoc _ _ _
  smul_add' _ _ _ := Subtype.eq ∘ funext <| λ _ => K.mul_add _ _ _
  smul_zero' _ := Subtype.eq ∘ funext <| λ _ => K.mul_zero _
  add_smul' _ _ _ := Subtype.eq ∘ funext <| λ _ => K.add_mul _ _ _
  zero_smul' _ := Subtype.eq ∘ funext <| λ _ => K.zero_mul _
  one_smul' _ := Subtype.eq ∘ funext <| λ _ => K.one_mul _

private def lem {α : Type} {x y : α} {A : Ring}
  (h : (if x = y then (1 : A) else (0 : A)) ≠ 0) : x = y :=
  if p : x = y then p else False.elim ∘ h <| by simp [p]

def linearizeα {K : Field} {α : Type} (x : α) : finite_support α K :=
  ⟨ λ y => if x = y then 1 else 0
  , by
    apply Exists.intro 1
    apply Exists.intro λ _ => ⟨ 0, Nat.zero_lt_one ⟩
    intro ⟨ y, p ⟩ ⟨ z, q ⟩ _
    apply Subtype.eq
    exact lem p ▸ lem q ▸ Eq.refl x ⟩

#print List.Mem

theorem List.mem_of_eq_head {α : Type} {x y : α} {l : List α} (h : x = y) : x ∈ (y :: l) :=
  h ▸ Mem.head _

theorem List.nodup_of_singleton {α : Type} (x : α) : nodup [a] := by
  sorry

def linearizeα_support {K : Field} (x : α) : Fintype (support (@linearizeα K α x).1) where
  elems :=
    { val := Quotient.mk _ [⟨ x, by simp [linearizeα] ⟩]
    , nodup := sorry }
  complete := by
    intro a
    simp [Membership.mem]
    suffices p : a ∈ [⟨ x, _ ⟩] by
      exact p
    let ⟨ a, h ⟩ := a
    apply List.mem_of_eq_head
    apply Subtype.eq
    suffices p : a = x from p
    by_cases h' : x = a
    apply Eq.symm
    exact h'
    apply False.elim ∘ h
    simp [linearizeα, h']

def linearizeF {K : Field} {α : Type} {V : VectorSpace K} (f : α → V) :
  LinearMap (linearized K α) V where
  f φ := φ.sum_support f
  map_smul' := sorry
  map_add' := sorry

theorem linearize_val {K : Field} {α : Type} {V : VectorSpace K} {f : α → V} {x : α} :
  (linearizeF f).f (linearizeα x) = f x := by
  simp [linearizeF, linearizeα, finite_support.sum_support]
  rw [finite_sum_val (linearizeα_support x)]
  show (if x = x then (1 : K) else (0 : K)) • f x + 0 = f x
  simp

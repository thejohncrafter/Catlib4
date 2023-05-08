
import Catlib4.Algebra.Vector.FiniteSupport
import Catlib4.Algebra.VectorSpace

open Classical

noncomputable section

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
  add_zero _ := Subtype.eq ∘ funext <| λ _ => K.add_zero _
  zero_add _ := Subtype.eq ∘ funext <| λ _ => K.zero_add _
  add_assoc _ _ _ := Subtype.eq ∘ funext <| λ _ => K.add_assoc _ _ _
  add_comm _ _ := Subtype.eq ∘ funext <| λ _ => K.add_comm _ _
  add_neg _ := Subtype.eq ∘ funext <| λ _ => K.add_neg _
  smul_smul _ _ _ := Subtype.eq ∘ funext <| λ _ => K.mul_assoc _ _ _
  smul_add _ _ _ := Subtype.eq ∘ funext <| λ _ => K.mul_add _ _ _
  smul_zero _ := Subtype.eq ∘ funext <| λ _ => K.mul_zero _
  add_smul _ _ _ := Subtype.eq ∘ funext <| λ _ => K.add_mul _ _ _
  zero_smul _ := Subtype.eq ∘ funext <| λ _ => K.zero_mul _
  one_smul _ := Subtype.eq ∘ funext <| λ _ => K.one_mul _

private def lem {α : Type} {x y : α} {A : Ring}
  (h : (if x = y then (1 : A) else (0 : A)) ≠ 0) : x = y :=
  if p : x = y then p else False.elim ∘ h <| by simp [p]

def linearizeα {K : Field} {α : Type} (x : α) : linearized K α :=
  ⟨ λ y => if x = y then 1 else 0
  , by
    apply Exists.intro 1
    apply Exists.intro λ _ => ⟨ 0, Nat.zero_lt_one ⟩
    intro ⟨ y, p ⟩ ⟨ z, q ⟩ _
    apply Subtype.eq
    exact lem p ▸ lem q ▸ Eq.refl x ⟩

notation "l[" x "]" => linearizeα x

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

@[simp] theorem linearize_val {K : Field} {α : Type} {V : VectorSpace K} {f : α → V} {x : α} :
  (linearizeF f).f l[x] = f x := by
  simp only [linearizeF, linearizeα, finite_support.sum_support]
  rw [finite_sum_val (linearizeα_support x)]
  show (if x = x then (1 : K) else (0 : K)) • f x + 0 = f x
  simp

theorem finite_support_eq_finite_sum_pure {K : Field} {α : Type} (φ : linearized K α)
  : φ = φ.sum_support λ x => l[x] := sorry

theorem linearize.inductionOn {K : Field} {α : Type}
  {motive : linearized K α → Prop}
  (φ : linearized K α)
  (pure : (x : α) → motive l[x])
  (smul : (μ : K) → (x : linearized K α) → motive x → motive (μ • x))
  (add : (x y : linearized K α) → motive x → motive y → motive (x + y))
  (zero : motive 0)
  : motive φ := by
  rw [finite_support_eq_finite_sum_pure φ]
  have ⟨ ⟨ val, nodup ⟩, complete ⟩ : Fintype (support φ.1) := fintype_of_finite φ.2
  rw [finite_support.sum_support, finite_sum_val ⟨ ⟨ val, nodup ⟩, complete ⟩]
  induction val using Quotient.inductionOn with
  | h l =>
    show motive (l.sum λ ⟨ x, _ ⟩ => φ.1 x • l[x])
    clear complete nodup
    induction l with
    | nil => exact zero
    | cons x t ih =>
      apply add _ _ (smul _ _ <| pure _)
      apply ih

def linearizeF_map {α β : Type} {K : Field} {V W : VectorSpace K} (f : β → W) (g : α → β) :
  linearizeF (f ∘ g) = LinearMap.compose (linearizeF f) (linearizeF (λ x => l[g x])) := by
  apply LinearMap.ext
  intro x
  induction x using linearize.inductionOn with
  | pure x => simp [LinearMap.compose]
  | smul μ x ih => simp_all
  | add x y ih ih' => simp_all
  | zero => simp

theorem factor_of_vanish {α : Type} {K : Field} {V W : VectorSpace K}
  {f : α → V} {g : LinearMap V W}
  (h : ∀ a : α, g (f a) = 0) : LinearMap.compose g (linearizeF f) = LinearMap.zero (linearized K α) W := by
  apply LinearMap.ext
  intro x
  induction x using linearize.inductionOn with
  | pure x => simp [h x]
  | smul μ x ih => simp_all
  | add x y ih ih' => simp_all
  | zero => simp

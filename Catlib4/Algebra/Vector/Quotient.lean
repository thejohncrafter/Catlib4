
import Catlib4.Algebra.VectorSpace

opaque opaque_id_wrapper {α : Type u} : { f : α → α // f = id } := ⟨ id, rfl ⟩
def opaque_id {α : Type u} : α → α := opaque_id_wrapper.1
theorem opaque_id_eq {α : Type u} : @opaque_id α = id := opaque_id_wrapper.2

section

variable {K : Field} {V W : VectorSpace K} (f : LinearMap W V)

def modulo : V → V → Prop := λ x y => ∃ z, x + -y = f z

theorem modulo_equivalence : Equivalence (modulo f) where
  refl x := ⟨ 0, by simp ⟩
  symm := λ {x y} ⟨ z, h ⟩ => by
    apply Exists.intro (-z)
    simp [← h, V.add_comm y]
  trans := λ {x y z} ⟨ z, h ⟩ ⟨ z', h' ⟩ => by
    apply Exists.intro (z + z')
    rw [f.map_add, ← h, ← h', V.add_assoc
      , ← V.add_assoc x (-y)
      , V.add_comm (-y) y
      , V.add_neg
      , V.add_zero]

instance modulo_setoid : Setoid V where
  r := modulo f
  iseqv := modulo_equivalence f

def LinearMap.cokernel : VectorSpace K where
  α := Quotient (modulo_setoid f)
  add := Quotient.lift₂
    (λ x y => Quotient.mk _ <| x + y)
    (by
      intro x y x' y' ⟨ z, h ⟩ ⟨ z', h' ⟩
      apply Quotient.sound
      apply Exists.intro (z + z')
      suffices p : x + y + -x' + -y' = x + -x' + y + -y' by
        simp_all [← h, ← h']
      rw [← V.add_assoc x (-x')
      , V.add_comm (-x') y
      , V.add_assoc])
  neg := Quotient.lift
    (λ x => Quotient.mk _ <| -x)
    (by
      intro x y ⟨ z, h ⟩
      apply Quotient.sound
      apply Exists.intro (-z)
      simp [← h])
  zero := Quotient.mk _ 0
  smul μ := Quotient.lift
    (λ x => Quotient.mk _ <| μ • x)
    (by
      intro x x' ⟨ z, h ⟩
      apply Quotient.sound
      apply Exists.intro (μ • z)
      simp [← h, K.mul_comm μ])
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

def LinearMap.cokernel_projector : LinearMap V f.cokernel where
  f := λ x => Quotient.mk _ x
  map_smul' _ _ := rfl
  map_add' _ _ := rfl

def LinearMap.cokernel_factor {E : VectorSpace K} (g : LinearMap V E)
  (h : LinearMap.compose g f = LinearMap.zero _ _) :
  LinearMap f.cokernel E where
  f := Quotient.lift g
    (by
      intro x x' ⟨ z, p ⟩
      conv =>
        enter [1, 2]
        rw [← V.zero_add x, ← V.add_neg x', ← V.add_assoc x']
        enter [2]
        rw [V.add_comm, p]
      let p : g (f z) = 0 := congrFun (congrArg LinearMap.f h) z
      simp [p, h])
  map_smul' μ := λ x => by
    induction x using Quotient.inductionOn with
    | h _ => exact g.map_smul _ _
  map_add' := λ x y => by
    induction x, y using Quotient.inductionOn₂ with
    | h _ _ => exact g.map_add _ _

end

section

variable {K : Field} {W V : VectorSpace K} {f : LinearMap W V}

theorem cokernel_vanish : LinearMap.compose f.cokernel_projector f = LinearMap.zero _ _ := by
  apply LinearMap.ext
  intro x
  apply Quotient.sound
  apply Exists.intro x
  simp

theorem factor_sound {E : VectorSpace K} {g : LinearMap V E}
  {h : LinearMap.compose g f = LinearMap.zero _ _} :
  g = LinearMap.compose (f.cokernel_factor g h) f.cokernel_projector := by rfl

theorem eq_from_eq_compose_proj {E : VectorSpace K}
  {g g' : LinearMap f.cokernel E}
  (h : LinearMap.compose g f.cokernel_projector
    = LinearMap.compose g' f.cokernel_projector)
  : g = g' := by
  apply LinearMap.ext
  intro x
  induction x using Quotient.inductionOn with
  | h x => exact congrFun (congrArg LinearMap.f h) x

attribute [irreducible] LinearMap.cokernel
attribute [irreducible] LinearMap.cokernel_projector
attribute [irreducible] LinearMap.cokernel_factor

end

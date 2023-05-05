
import Catlib4.Algebra.VectorSpace

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

def LinearMap.cokernel' : VectorSpace K where
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

def LinearMap.cokernel_projector' : LinearMap V f.cokernel' where
  f := λ x => Quotient.mk _ x
  map_smul' _ _ := rfl
  map_add' _ _ := rfl

def LinearMap.cokernel_factor' {E : VectorSpace K} (g : LinearMap V E)
  (h : LinearMap.compose g f = LinearMap.zero _ _) :
  LinearMap f.cokernel' E where
  f := Quotient.lift g
    (by
      intro x x' ⟨ z, p ⟩
      conv =>
        enter [1, 2]
        rw [← V.zero_add x, ← V.add_neg x', ← V.add_assoc x']
        enter [2]
        rw [V.add_comm, p]
      let p : g (f z) = 0 := congrFun h z
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

theorem cokernel_vanish' : LinearMap.compose f.cokernel_projector' f = LinearMap.zero _ _ := by
  apply LinearMap.ext
  intro x
  apply Quotient.sound
  apply Exists.intro x
  simp

theorem factor_sound' {E : VectorSpace K} {g : LinearMap V E}
  {h : LinearMap.compose g f = LinearMap.zero _ _} :
  g = LinearMap.compose (f.cokernel_factor' g h) f.cokernel_projector' := by rfl

theorem eq_from_eq_compose_proj' {E : VectorSpace K}
  {g g' : LinearMap f.cokernel' E}
  (h : LinearMap.compose g f.cokernel_projector'
    = LinearMap.compose g' f.cokernel_projector')
  : g = g' := by
  apply LinearMap.ext
  intro x
  induction x using Quotient.inductionOn with
  | h x => exact congrFun (congrArg LinearMap.f h) x

structure QuotientInterface {K : Field} {W V : VectorSpace K} (f : LinearMap W V) where
  cokernel : VectorSpace K
  cokernel_projector : LinearMap V cokernel
  cokernel_factor {E : VectorSpace K} (g : LinearMap V E) (h : LinearMap.compose g f = 0)
    : LinearMap cokernel E
  cokernel_vanish : (LinearMap.compose cokernel_projector f = 0)
  factor_sound {E : VectorSpace K} {g : LinearMap V E}
    {h : LinearMap.compose g f = 0}
    : g = LinearMap.compose (cokernel_factor g h) cokernel_projector
  eq_from_compose_proj {E : VectorSpace K} {g g' : LinearMap cokernel E}
    (h : LinearMap.compose g cokernel_projector = LinearMap.compose g' cokernel_projector)
    : g = g'

def LinearMap.quotient_interface' {K : Field} {W V : VectorSpace K} (f : LinearMap W V)
  : QuotientInterface f where
  cokernel := f.cokernel'
  cokernel_projector := f.cokernel_projector'
  cokernel_factor g h := f.cokernel_factor' g h
  cokernel_vanish := cokernel_vanish'
  factor_sound := factor_sound'
  eq_from_compose_proj h := eq_from_eq_compose_proj' h

opaque LinearMap.quotient_interface {K : Field} {W V : VectorSpace K} (f : LinearMap W V)
  : QuotientInterface f := f.quotient_interface'

def LinearMap.cokernel := f.quotient_interface.cokernel
def LinearMap.cokernel_projector : LinearMap V f.cokernel :=
  f.quotient_interface.cokernel_projector
def LinearMap.cokernel_factor {E : VectorSpace K}
  (g : LinearMap V E) (h : LinearMap.compose g f = LinearMap.zero _ _)
  : LinearMap f.cokernel E := f.quotient_interface.cokernel_factor g h

theorem cokernel_vanish : LinearMap.compose f.cokernel_projector f = LinearMap.zero _ _ :=
  f.quotient_interface.cokernel_vanish

theorem factor_sound {E : VectorSpace K} {g : LinearMap V E}
  {h : LinearMap.compose g f = LinearMap.zero _ _} :
  g = LinearMap.compose (f.cokernel_factor g h) f.cokernel_projector :=
  f.quotient_interface.factor_sound

theorem eq_from_eq_compose_proj {E : VectorSpace K}
  {g g' : LinearMap f.cokernel E}
  (h : LinearMap.compose g f.cokernel_projector
    = LinearMap.compose g' f.cokernel_projector)
  : g = g' := f.quotient_interface.eq_from_compose_proj h

end

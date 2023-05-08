
import Catlib4.Algebra.VectorSpace

section

variable {K : Field} {V W : KVect K} (f : W ⟶ V)

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

def cokernel' : KVect K where
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
  add_zero := sorry
  zero_add := sorry
  add_assoc := sorry
  add_comm := sorry
  add_neg := sorry
  smul_smul := sorry
  smul_add := sorry
  smul_zero := sorry
  add_smul := sorry
  zero_smul := sorry
  one_smul := sorry

def cokernel_projector' : V ⟶ (cokernel' f) where
  f := λ x => Quotient.mk _ x
  map_smul _ _ := rfl
  map_add _ _ := rfl

def cokernel_factor' {E : KVect K} (g : V ⟶ E)
  (h : f ≫ g = 0) :
  LinearMap (cokernel' f) E where
  f := Quotient.lift g
    (by
      intro x x' ⟨ z, p ⟩
      conv =>
        enter [1, 2]
        rw [← V.zero_add x, ← V.add_neg x', ← V.add_assoc x']
        enter [2]
        rw [V.add_comm, p]
      let p : g (f z) = 0 := congrFun (congrArg CoeFun.coe h) z
      simp [p, h])
  map_smul μ := λ x => by
    induction x using Quotient.inductionOn with
    | h _ => exact g.map_smul _ _
  map_add := λ x y => by
    induction x, y using Quotient.inductionOn₂ with
    | h _ _ => exact g.map_add _ _

end

section

variable {K : Field} {W V : KVect K} {f : W ⟶ V}

theorem cokernel_vanish' : f ≫ (cokernel_projector' f) = 0 := by
  apply LinearMap.ext
  intro x
  apply Quotient.sound
  apply Exists.intro x
  simp

theorem factor_sound' {E : KVect K} {g : V ⟶ E}
  {h : f ≫ g = LinearMap.zero _ _} :
  g = (cokernel_projector' f) ≫ (cokernel_factor' f g h) := by rfl

theorem eq_from_eq_compose_proj' {E : KVect K}
  {g g' : cokernel' f ⟶ E}
  (h : cokernel_projector' f ≫ g = cokernel_projector' f ≫ g')
  : g = g' := by
  apply LinearMap.ext
  intro x
  induction x using Quotient.inductionOn with
  | h x => exact congrFun (congrArg LinearMap.f h) x

end

structure QuotientInterface {K : Field} {W V : KVect K} (f : W ⟶ V) where
  cokernel : KVect K
  cokernel_projector : V ⟶ cokernel
  cokernel_factor {E : KVect K} (g : V ⟶ E) (h : f ≫ g = 0)
    : LinearMap cokernel E
  cokernel_vanish : (f ≫ cokernel_projector = 0)
  factor_sound {E : KVect K} {g : V ⟶ E} {h : f ≫ g = 0}
    : g = cokernel_projector ≫ (cokernel_factor g h)
  eq_from_compose_proj {E : KVect K} {g g' : cokernel ⟶ E}
    (h : cokernel_projector ≫ g = cokernel_projector ≫ g')
    : g = g'

def quotient_interface' {K : Field} {W V : KVect K} (f : W ⟶ V)
  : QuotientInterface f where
  cokernel := cokernel' f
  cokernel_projector := cokernel_projector' f
  cokernel_factor g h := cokernel_factor' f g h
  cokernel_vanish := cokernel_vanish'
  factor_sound := factor_sound'
  eq_from_compose_proj h := eq_from_eq_compose_proj' h

opaque quotient_interface {K : Field} {W V : KVect K} (f : W ⟶ V)
  : QuotientInterface f := quotient_interface' f

section

variable {K : Field} {W V : KVect K}

def cokernel (f : W ⟶ V) := (quotient_interface f).cokernel
def cokernel_projector (f : W ⟶ V) : V ⟶ cokernel f :=
  (quotient_interface f).cokernel_projector
def cokernel_factor (f : W ⟶ V) {E : KVect K}
  (g : LinearMap V E) (h : LinearMap.compose g f = LinearMap.zero _ _)
  : cokernel f ⟶ E := (quotient_interface f).cokernel_factor g h

theorem cokernel_vanish {f : W ⟶ V} : f ≫ cokernel_projector f = 0 :=
  (quotient_interface f).cokernel_vanish

theorem factor_sound {f : W ⟶ V} {E : KVect K} {g : LinearMap V E}
  {h : LinearMap.compose g f = LinearMap.zero _ _} :
  g = cokernel_projector f ≫ cokernel_factor f g h :=
  (quotient_interface f).factor_sound

theorem eq_from_eq_compose_proj {f : W ⟶ V} {E : KVect K}
  {g g' : cokernel f ⟶ E}
  (h : cokernel_projector f ≫ g = cokernel_projector f ≫ g')
  : g = g' := (quotient_interface f).eq_from_compose_proj h

end

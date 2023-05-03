
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

abbrev quotient_obj := Quotient (modulo_setoid f)

def LinearMap.cokernel : VectorSpace K where
  α := quotient_obj f
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

def cokernel_projector : LinearMap V f.cokernel where
  f := λ x => Quotient.mk _ x
  map_smul' _ _ := rfl
  map_add' _ _ := rfl

end

section

variable {K : Field} {W V : VectorSpace K} {f : LinearMap W V}

def cokernel_factor {E : VectorSpace K} (g : LinearMap V E) (h : ∀ x : W, g (f x) = 0) :
  LinearMap f.cokernel E where
  f := Quotient.lift g
    (by
      intro x x' ⟨ z, p ⟩
      conv =>
        enter [1, 2]
        rw [← V.zero_add x, ← V.add_neg x', ← V.add_assoc x']
        enter [2]
        rw [V.add_comm, p]
      simp [h])
  map_smul' μ := λ x => by
    induction x using Quotient.inductionOn with
    | h _ => exact g.map_smul _ _
  map_add' := λ x y => by
    induction x, y using Quotient.inductionOn₂ with
    | h _ _ => exact g.map_add _ _

theorem factor {E : VectorSpace K} {g : LinearMap V E} {h : ∀ x : W, g (f x) = 0} :
  g.f = λ x => cokernel_factor g h (cokernel_projector f x) := by rfl

end

--def VectorSpace.cokernel {K : Field} {W V : VectorSpace K} (f : W → V) : VectorSpace K where
--  α := 

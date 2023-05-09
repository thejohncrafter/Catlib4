
import Catlib4.Algebra.Ring
import Catlib4.Category.Category
import Catlib4.Algebra.VectorSpace

namespace CategoryTheory

def Rng : Category where
  α := Ring
  hom := λ A B => RingMorphism A B
  id := Ring.idF
  comp := Ring.compF
  id_comp' := by intros; rfl
  comp_id' := by intros; rfl
  assoc' := by intros; rfl

instance : CoeSort Rng (Type u) := inferInstanceAs (CoeSort Ring (Type u))

def Fld : Category where
  α := Field
  hom := λ A B => RingMorphism A.toRing B.toRing
  id F := Ring.idF F.toRing
  comp := Ring.compF
  id_comp' := by intros; rfl
  comp_id' := by intros; rfl
  assoc' := by intros; rfl

instance : CoeSort Fld (Type u) := inferInstanceAs (CoeSort Field (Type u))

def forget_Rng_Fld : Fld ⥤ Rng where
  obj F := F.toRing
  map f := f
  map_id' := by intros; rfl
  map_comp' := by intros; rfl

def KAlg (K : Fld) : Category where
  α := Σ A : Rng, { ι : (forget_Rng_Fld.obj K) ⟶ A // ∀ x : A, ∀ μ : K, x * ι.φ μ = ι.φ μ * x }
  hom := λ ⟨ A, φ, _ ⟩ ⟨ B, ψ, _ ⟩ => { f : A ⟶ B // ψ = φ ≫ f }
  id := λ ⟨ A, φ ⟩ => ⟨ Ring.idF A, rfl ⟩
  comp := λ ⟨ f, p ⟩ ⟨ g, q ⟩ => ⟨ f ≫ g, by simp [p, q] ⟩
  id_comp' := by intros; rfl
  comp_id' := by intros; rfl
  assoc' := by intros; rfl

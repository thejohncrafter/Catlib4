
import Catlib4.Groundwork.Basic
import Catlib4.Notation
import Catlib4.Combinatorics

namespace CategoryTheory

section Category

structure CategoryStruct extends Quiver where
  id : ∀ a : α, a ⟶ a
  comp : ∀ {a b c : α}, (a ⟶ b) → (b ⟶ c) → (a ⟶ c)

instance : Coe CategoryStruct Quiver where
  coe C := {
    α := C.α
    hom := C.hom
  }

instance : CoeSort CategoryStruct (Type u) where
  coe C := C.α

instance (C : CategoryStruct) : HasIdentity C where
  identity := C.id

instance (C : CategoryStruct) : HasComp C where
  comp := C.comp

structure Category extends CategoryStruct where
  id_comp' {x y : α} : ∀ (f : x ⟶ y), 𝟙 x ≫ f = f
  comp_id' {x y : α} : ∀ (f : x ⟶ y), f ≫ 𝟙 y = f
  assoc' : ∀ {w x y z : α} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z),
    f ≫ (g ≫ h) = (f ≫ g) ≫ h

instance : Coe Category CategoryStruct where
  coe C := {
    α := C.α
    hom := C.hom
    id := C.id
    comp := C.comp
  }

instance : CoeSort Category (Type u) where
  coe C := C.α

@[simp]
theorem Category.id_comp (α : Category)
  : ∀ {x y : α} (f : x ⟶ y), 𝟙 x ≫ f = f := α.id_comp'

@[simp]
theorem Category.comp_id (α : Category)
  : ∀ {x y : α} (f : x ⟶ y), f ≫ 𝟙 y = f := α.comp_id'

@[simp]
theorem Category.assoc (α : Category)
  : ∀ {w x y z : α} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z),
    f ≫ (g ≫ h) = (f ≫ g) ≫ h := α.assoc'

structure Iso {C : Category} (x y : C) where
  hom : x ⟶ y
  inv : y ⟶ x
  hom_inv_id : hom ≫ inv = 𝟙 x
  inv_hom_id : inv ≫ hom = 𝟙 y

instance (C : Category) : HasIso C where
  iso := Iso

end Category

section Functor

structure Functor (C D : Category) extends Prefunctor C D where
  map_id' : ∀ (x : C), map (𝟙 x) = 𝟙 (obj x)
  map_comp' : ∀ {x y z : C} (f : x ⟶ y) (g : y ⟶ z), map (f ≫ g) = map f ≫ map g

infixr:26 "⥤" => Functor

section NaturalTransformations

structure NatTrans {α β : Category.{u,v}} (F G : α ⥤ β) : Type (max u v)
where
  map : ∀ (x : α), F.obj x ⟶ G.obj x
  naturality : ∀ {x y : α} (f : x ⟶ y), F.map f ≫ map y = map x ≫ G.map f

theorem NatTrans.ext {C D : Category} {F G : C ⥤ D} :
  (σ τ : NatTrans F G) → σ.map = τ.map → σ = τ
| ⟨ _, _ ⟩, ⟨ _, _ ⟩ => by simp_all

def NatTrans.vcomp
  {α β : Category}
  {F G H : α ⥤ β}
  (σ : NatTrans F G) (τ : NatTrans G H) : NatTrans F H
where
  map x := σ.map x ≫ τ.map x
  naturality f := by
    conv => lhs; rw [Category.assoc, σ.naturality f]
    conv => rhs; rw [← Category.assoc, ← τ.naturality f]
    rw [Category.assoc]

def NatTrans.id
  {α β : Category}
  (F : α ⥤ β) : NatTrans F F
where
  map x := 𝟙 (F.obj x)
  naturality f := by simp

end NaturalTransformations

section functor_category

def functor_category (C D : Category.{u,v}) : Category.{max u v, max u v + 1} where
  α := C ⥤ D
  hom F G := NatTrans F G
  id := NatTrans.id
  comp := NatTrans.vcomp
  id_comp' {F G} σ := by
    suffices p : NatTrans.vcomp (NatTrans.id F) σ = σ
    from p
    apply NatTrans.ext
    simp [NatTrans.vcomp, NatTrans.id]
  comp_id' {F G} σ := by
    suffices p : NatTrans.vcomp σ (NatTrans.id G) = σ
    from p
    apply NatTrans.ext
    simp [NatTrans.vcomp, NatTrans.id]
  assoc' {F₁ F₂ F₃ F₄} σ τ ρ := by
    suffices p
      : NatTrans.vcomp σ (NatTrans.vcomp τ ρ)
      = NatTrans.vcomp (NatTrans.vcomp σ τ) ρ
    from p
    apply NatTrans.ext
    simp [NatTrans.vcomp, NatTrans.id]

instance : CoeSort (functor_category.{u,v} C D) (Type (max u v)) where
  coe _ := C ⥤ D

instance : HasHom (C ⥤ D) := inferInstanceAs (HasHom (functor_category C D).α)
instance (C D : Category ): HasIso (C ⥤ D) := inferInstanceAs (HasIso (functor_category C D).α)

end functor_category

@[simp]
theorem Functor.map_id {C D : Category} (F : Functor C D) (x : C) : F.map (𝟙 x) = 𝟙 (F.obj x) := map_id' F x

@[simp]
theorem Functor.map_comp {C D : Category} (F : Functor C D)
  : ∀ {x y z : C} (f : x ⟶ y) (g : y ⟶ z), F.map (f ≫ g) = F.map f ≫ F.map g
  := map_comp' F

def Functor.constant' (C : Category) {D : Category} (a : D) : C ⥤ D where
  obj _ := a
  map _ := 𝟙 a
  map_id' _ := rfl
  map_comp' _ _ := (D.id_comp _).symm

def Functor.comp' {B C D : Category} (F : Functor B C) (G : Functor C D) : Functor B D where
  obj := G.obj ∘ F.obj
  map := G.map ∘ F.map
  map_id' x := by simp
  map_comp' f g := by
    simp -- Work around bug
    rw [F.map_comp, G.map_comp]

instance {B C D : Category} : HasComp' (Functor B C) (Functor C D) (Functor B D) where
  comp' := Functor.comp'

@[simp]
theorem comp'_map {B C D : Category} (F : Functor B C) (G : Functor C D)
  {x y : B} (f : x ⟶ y) : (F ⋙ G).map f = G.map (F.map f) := rfl

section NaturalTransformations

def NatTrans.hcomp {B C D : Category} {F₁ G₁ : B ⥤ C} {F₂ G₂ : C ⥤ D}
  (σ : NatTrans F₁ G₁) (τ : NatTrans F₂ G₂) : NatTrans (F₁ ⋙ F₂) (G₁ ⋙ G₂)
where
  map x := τ.map (F₁.obj x) ≫ G₂.map (σ.map x)
  naturality f := by
    dsimp
    rw [Category.assoc D]
    rw [τ.naturality]
    rw [← Category.assoc D]
    rw [← G₂.map_comp]
    rw [σ.naturality]
    rw [G₂.map_comp]
    rw [Category.assoc D]

instance {B C D : Category} {F₁ G₁ : B ⥤ C} {F₂ G₂ : C ⥤ D}
  : HasHComp (NatTrans F₁ G₁) (NatTrans F₂ G₂) (NatTrans (F₁ ⋙ F₂) (G₁ ⋙ G₂)) where
  hcomp := NatTrans.hcomp

end NaturalTransformations

end Functor

end CategoryTheory

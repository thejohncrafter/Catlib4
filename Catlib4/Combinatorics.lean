
import Catlib4.Notation

universe u v

structure Quiver : Type (max u v + 1) where
  α : Type u
  hom : α → α → Sort v

instance : CoeSort Quiver (Type u) where
  coe Q := Q.α

instance (Q : Quiver.{u,v}) : HasHom.{u,v} Q where
  hom := Q.hom

structure Prefunctor (Q R : Quiver.{u,v}) : Type (max u v) where
  obj : Q → R
  map {x y : Q} : (x ⟶ y) → (obj x ⟶ obj y)

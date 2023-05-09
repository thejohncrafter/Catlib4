
import Catlib4.Notation

structure ConcreteStructure where
  α : Type u

instance : CoeSort ConcreteStructure (Type u) where
  coe S := S.α

structure AddStructure extends ConcreteStructure where
  add : α → α → α
  neg : α → α
  zero : α

instance : CoeSort AddStructure (Type u) where
  coe S := S.α

instance (S : AddStructure) : Add S where
  add := S.add

instance (S : AddStructure) : Neg S where
  neg := S.neg

instance (S : AddStructure) : OfNat S (nat_lit 0) where
  ofNat := S.zero

structure MulStructure extends ConcreteStructure where
  mul : α → α → α
  one : α

instance : CoeSort MulStructure (Type u) where
  coe S := S.α

instance (S : MulStructure) : Mul S where
  mul := S.mul

instance (S : MulStructure) : OfNat S (nat_lit 1) where
  ofNat := S.one

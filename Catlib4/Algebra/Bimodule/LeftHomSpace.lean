
import Catlib4.Algebra.Bimodule.Basic

namespace Algebra.Bimodule

section

variable {K : Field} {A B C : Algebra K} (M : Bimod A B) (N : Bimod A C)

structure LeftLinearMap where
  f : M → N
  map_smul : ∀ x : M, ∀ μ : K, f (μ • x) = μ • f x
  map_add : ∀ x y : M, f (x + y) = f x + f y
  map_zero : f 0 = 0
  map_lmul : ∀ x : M, ∀ μ : A, f (μ •ₗ x) = μ •ₗ f x

attribute [simp] LeftLinearMap.map_smul
attribute [simp] LeftLinearMap.map_add
attribute [simp] LeftLinearMap.map_zero
attribute [simp] LeftLinearMap.map_lmul

instance : CoeFun (LeftLinearMap M N) (fun _ => M → N) where
  coe φ := φ.f

end

section

variable {K : Field} {A B C : Algebra K} {M : Bimod A B} {N : Bimod A C}

theorem LeftLinearMap.eq :
  ∀ {f g : LeftLinearMap M N}, f.f = g.f → f = g
  | ⟨ _, _, _, _, _ ⟩, ⟨ _, _, _, _, _ ⟩, rfl => rfl

theorem LeftLinearMap.ext : ∀ {f g : LeftLinearMap M N}, (∀ x, f x = g x) → f = g :=
  eq ∘ funext

end

section

variable {K : Field} {A B C : Algebra K} (M : Bimod A B) (N : Bimod A C)

def left_hom_space_struct : BimoduleStructure B C where
  α := LeftLinearMap M N
  add f g :=
    ⟨ λ x => f x + g x
    , by simp
    , by
      intro x y
      suffices r : f x + f y + g x + g y = f x + g x + f y + g y by
        simp [r]
      rw [← N.add_assoc (f x) (g x), N.add_comm (g x) (f y), N.add_assoc]
    , by simp
    , by simp ⟩
  neg f :=
    ⟨ λ x => - f x
    , by simp [K.mul_comm (-1)]
    , by simp
    , by simp
    , by simp ⟩
  zero :=
    ⟨ λ _ => 0
    , by simp
    , by simp
    , by simp
    , by simp ⟩
  smul μ f :=
    ⟨ λ x => μ • f x
    , by intro x ν; simp [K.mul_comm μ ν]
    , by simp
    , by simp
    , by simp ⟩
  lmul b f :=
    ⟨ λ x => f (x •ᵣ b)
    , by simp
    , by simp
    , by simp
    , by simp ⟩
  rmul f c :=
    ⟨ λ x => f x •ᵣ c
    , by simp
    , by simp
    , by simp
    , by simp ⟩

def left_hom_space : Bimod B C where
  toBimoduleStructure := left_hom_space_struct M N
  add_zero _ := by
    apply LeftLinearMap.ext
    exact λ _ => N.add_zero _
  zero_add _ := by
    apply LeftLinearMap.ext
    exact λ _ => N.zero_add _
  add_assoc _ _ _ := by
    apply LeftLinearMap.ext
    exact λ _ => N.add_assoc _ _ _
  add_comm _ _ := by
    apply LeftLinearMap.ext
    exact λ _ => N.add_comm _ _
  add_neg _ := by
    apply LeftLinearMap.ext
    exact λ _ => N.add_neg _
  smul_smul _ _ _ := by
    apply LeftLinearMap.ext
    exact λ _ => N.smul_smul _ _ _
  smul_add _ _ _ := by
    apply LeftLinearMap.ext
    exact λ _ => N.smul_add _ _ _
  smul_zero _ := by
    apply LeftLinearMap.ext
    exact λ _ => N.smul_zero _
  add_smul _ _ _ := by
    apply LeftLinearMap.ext
    exact λ _ => N.add_smul _ _ _
  zero_smul _ := by
    apply LeftLinearMap.ext
    exact λ _ => N.zero_smul _
  one_smul _ := by
    apply LeftLinearMap.ext
    exact λ _ => N.one_smul _
  lmul_lmul _ _ _ := by
    apply LeftLinearMap.ext
    exact λ _ => congrArg _ <| M.rmul_rmul _ _ _
  lmul_add _ _ _ := rfl
  lmul_zero _ := rfl
  add_lmul x y f := by
    apply LeftLinearMap.ext
    exact λ z => by
      show f.f (z •ᵣ (x + y)) = f.f (z •ᵣ x) + f.f (z •ᵣ y)
      exact M.rmul_add _ _ _ ▸ f.map_add _ _
  zero_lmul f := by
    apply LeftLinearMap.ext
    exact λ x => by
      show f.f (x •ᵣ 0) = 0
      exact M.rmul_zero _ ▸ f.map_zero
  one_lmul f := by
    apply LeftLinearMap.ext
    exact λ x => by
      show f.f (x •ᵣ 1) = f.f x
      rw [M.rmul_one]
  rmul_rmul f x y := by
    apply LeftLinearMap.ext
    exact λ z => N.rmul_rmul _ _ _
  rmul_add _ _ _ := by
    apply LeftLinearMap.ext
    exact λ _ => N.rmul_add _ _ _
  zero_rmul _ := by
    apply LeftLinearMap.ext
    exact λ _ => N.zero_rmul _
  rmul_zero _ := by
    apply LeftLinearMap.ext
    exact λ _ => N.rmul_zero _
  add_rmul _ _ _ := by
    apply LeftLinearMap.ext
    exact λ _ => N.add_rmul _ _ _
  rmul_one _ := by
    apply LeftLinearMap.ext
    exact λ _ => N.rmul_one _
  lmul_rmul _ _ _ := rfl
  lmul_linear f b μ := by
    apply LeftLinearMap.ext
    exact λ x => by
      show f.f (x •ᵣ (μ • b)) = μ • f.f (x •ᵣ b)
      rw [← f.map_smul]
      exact congrArg _ <| M.rmul_linear _ _ _
  rmul_linear _ _ _ := by
    apply LeftLinearMap.ext
    exact λ _ => N.rmul_linear _ _ _
  lmul_linear' f b μ := rfl
  rmul_linear' _ _ _ := by
    apply LeftLinearMap.ext
    exact λ _ => N.rmul_linear' _ _ _

instance : CoeFun (left_hom_space M N) (fun _ => M → N)
  := inferInstanceAs (CoeFun (LeftLinearMap M N) (fun _ => M → N))

instance : Add (LeftLinearMap M N) := inferInstanceAs (Add (left_hom_space M N))
instance : Neg (LeftLinearMap M N) := inferInstanceAs (Neg (left_hom_space M N))
instance : SMul K (LeftLinearMap M N) := inferInstanceAs (SMul K (left_hom_space M N))
instance : LSMul B (LeftLinearMap M N) := inferInstanceAs (LSMul B (left_hom_space M N))
instance : RSMul (LeftLinearMap M N) C := inferInstanceAs (RSMul (left_hom_space M N) C)
instance : OfNat (LeftLinearMap M N) (nat_lit 0) := inferInstanceAs (OfNat (left_hom_space M N) (nat_lit 0))

end

section

variable {K : Field} {A B C : Algebra K} {M : Bimod A B} {N : Bimod A C}

@[simp] theorem LeftLinearMap.add_val (f g : left_hom_space M N) (x : M) :
  (f + g) x = f x + g x := rfl

@[simp] theorem LeftLinearMap.neg_val (f : left_hom_space M N) (x : M) :
  (-f) x = -(f x) := rfl

@[simp] theorem LeftLinearMap.smul_val (μ : K) (f : left_hom_space M N) (x : M) :
  (μ • f) x = μ • f x := rfl

@[simp] theorem LeftLinearMap.lmul_val (b : B) (f : left_hom_space M N) (x : M) :
  (b •ₗ f) x = f (x •ᵣ b) := rfl

@[simp] theorem LeftLinearMap.rmul_val (f : left_hom_space M N) (c : C) (x : M) :
  (f •ᵣ c) x = f x •ᵣ c := rfl

@[simp] theorem LeftLinearMap.zero_val (x : M)
  : (0 : left_hom_space M N) x = 0 := rfl

end

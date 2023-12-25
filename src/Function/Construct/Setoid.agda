{-# OPTIONS --without-K --safe #-}

-- was not ported from old function hierarchy

module Function.Construct.Setoid where

  open import Function.Bundles using (Func; _⟨$⟩_)
  import Function.Construct.Composition as Comp
  open import Level using (Level)
  open import Relation.Binary.Bundles using (Setoid)


  private
    variable
      a₁ a₂ b₁ b₂ c₁ c₂ : Level
      
  function : Setoid a₁ a₂ → Setoid b₁ b₂ → Setoid _ _
  function From To = record
    { Carrier = Func From To
    ; _≈_ = λ f g → ∀ {x y} → x From.≈ y → f ⟨$⟩ x To.≈ g ⟨$⟩ y
    ; isEquivalence = record
      { refl = λ {f} x≈y → Func.cong f x≈y
      ; sym = λ {f} {g} fx≈gy x≈y → To.sym (fx≈gy (From.sym x≈y))
      ; trans = λ {f} {g} {h} fx≈gy gx≈hy x≈y → To.trans (fx≈gy x≈y) (gx≈hy From.refl)
      }
    }
    where
      module To = Setoid To
      module From = Setoid From

  -- This doesn't really belong here, it should be in Function.Construct.Composition but that's in stdlib
  -- so will need to be contributed to there first.
  infixr 9 _∙_
  _∙_ : {A : Setoid a₁ a₂} {B : Setoid b₁ b₂} {C : Setoid c₁ c₂} → Func B C → Func A B → Func A C
  f ∙ g = Comp.function g f
    
  

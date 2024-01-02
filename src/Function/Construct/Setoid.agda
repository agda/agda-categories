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
      
  setoid : Setoid a₁ a₂ → Setoid b₁ b₂ → Setoid _ _
  setoid From To = record
    { Carrier = Func From To
    ; _≈_ = λ f g → ∀ {x} → f ⟨$⟩ x To.≈ g ⟨$⟩ x
    ; isEquivalence = record
      { refl = To.refl
      ; sym = λ f≈g → To.sym f≈g
      ; trans = λ f≈g g≈h → To.trans f≈g g≈h
      }
    }
    where
      module To = Setoid To

  -- This doesn't really belong here, it should be in Function.Construct.Composition but that's in stdlib
  -- so will need to be contributed to there first.
  infixr 9 _∙_
  _∙_ : {A : Setoid a₁ a₂} {B : Setoid b₁ b₂} {C : Setoid c₁ c₂} → Func B C → Func A B → Func A C
  f ∙ g = Comp.function g f
    
  

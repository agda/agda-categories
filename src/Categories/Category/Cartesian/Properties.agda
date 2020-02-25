{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Category.Cartesian.Properties {o ℓ e} (C : Category o ℓ e) where

open import Function using (_$_)

open import Categories.Category.Cartesian C

open import Categories.Diagram.Pullback C
open import Categories.Diagram.Equalizer C
open import Categories.Morphism.Reasoning C

private
  open Category C
  variable
    A B X Y : Obj
    f g : A ⇒ B

-- all binary products and pullbacks implies equalizers
module _ (prods : BinaryProducts) (pullbacks : ∀ {A B X} (f : A ⇒ X) (g : B ⇒ X) → Pullback f g) where
  open BinaryProducts prods
  open HomReasoning
  
  prods×pullbacks⇒equalizers : Equalizer f g
  prods×pullbacks⇒equalizers {f = f} {g = g} = record
    { arr       = pb′.p₁
    ; equality  = begin
      f ∘ pb′.p₁           ≈⟨ refl⟩∘⟨ helper₁ ⟩
      f ∘ pb.p₁ ∘ pb′.p₂   ≈⟨ pullˡ pb.commute ⟩
      (g ∘ pb.p₂) ∘ pb′.p₂ ≈˘⟨ pushʳ helper₂ ⟩
      g ∘ pb′.p₁           ∎
    ; equalize  = λ {_ i} eq → pb′.universal $ begin
      ⟨ id , id ⟩ ∘ i                                       ≈⟨ ⟨⟩∘ ⟩
      ⟨ id ∘ i , id ∘ i ⟩                                   ≈⟨ ⟨⟩-cong₂ identityˡ identityˡ ⟩
      ⟨ i ,  i ⟩                                            ≈˘⟨ ⟨⟩-cong₂ pb.p₁∘universal≈h₁ pb.p₂∘universal≈h₂ ⟩
      ⟨ pb.p₁ ∘ pb.universal eq , pb.p₂ ∘ pb.universal eq ⟩ ≈˘⟨ ⟨⟩∘ ⟩
      h ∘ pb.universal eq                                   ∎
    ; universal = ⟺ pb′.p₁∘universal≈h₁
    ; unique    = λ eq → pb′.unique (⟺ eq) (pb.unique (pullˡ (⟺ helper₁) ○ ⟺ eq) (pullˡ (⟺ helper₂) ○ ⟺ eq))
    }
    where pb : Pullback f g
          pb         = pullbacks _ _
          module pb  = Pullback pb
          h          = ⟨ pb.p₁ , pb.p₂ ⟩
          pb′ : Pullback ⟨ id , id ⟩ h
          pb′        = pullbacks _ _
          module pb′ = Pullback pb′
          helper₁ : pb′.p₁ ≈ pb.p₁ ∘ pb′.p₂
          helper₁    = begin
            pb′.p₁                    ≈˘⟨ cancelˡ project₁ ⟩
            π₁ ∘ ⟨ id , id ⟩ ∘ pb′.p₁ ≈⟨ refl⟩∘⟨ pb′.commute ⟩
            π₁ ∘ h ∘ pb′.p₂           ≈⟨ pullˡ project₁ ⟩
            pb.p₁ ∘ pb′.p₂            ∎
          helper₂ : pb′.p₁ ≈ pb.p₂ ∘ pb′.p₂
          helper₂    = begin
            pb′.p₁                    ≈˘⟨ cancelˡ project₂ ⟩
            π₂ ∘ ⟨ id , id ⟩ ∘ pb′.p₁ ≈⟨ refl⟩∘⟨ pb′.commute ⟩
            π₂ ∘ h ∘ pb′.p₂           ≈⟨ pullˡ project₂ ⟩
            pb.p₂ ∘ pb′.p₂            ∎
          

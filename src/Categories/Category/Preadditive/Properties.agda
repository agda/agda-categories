{-# OPTIONS --without-K --safe #-}

module Categories.Category.Preadditive.Properties where

open import Categories.Category
open import Categories.Category.Preadditive

open import Categories.Object.Initial
open import Categories.Object.Terminal
open import Categories.Object.Zero

module _ {o ℓ e} {𝒞 : Category o ℓ e} (preadditive : Preadditive 𝒞) where
  open Category 𝒞
  open HomReasoning
  open Preadditive preadditive

  Initial⇒Zero : Initial 𝒞 → Zero 𝒞
  Initial⇒Zero initial = record
    { zero = ⊥
    ; ! = ! 
    ; ¡ = 0H
    ; !-unique = !-unique
    ; ¡-unique = λ f → begin
      0H     ≈˘⟨ 0-resp-∘ˡ ⟩
      0H ∘ f ≈⟨ !-unique₂ 0H id ⟩∘⟨refl ⟩
      id ∘ f ≈⟨ identityˡ ⟩
      f ∎
    }
    where
      open Initial initial

  Terminal⇒Zero : Terminal 𝒞 → Zero 𝒞
  Terminal⇒Zero terminal = record
    { zero = ⊤
    ; ! = 0H
    ; ¡ = !
    ; !-unique = λ f → begin
      0H     ≈˘⟨ 0-resp-∘ʳ ⟩
      f ∘ 0H ≈⟨ refl⟩∘⟨ !-unique₂ ⟩
      f ∘ id ≈⟨ identityʳ ⟩
      f ∎
    ; ¡-unique = !-unique
    }
    where
      open Terminal terminal

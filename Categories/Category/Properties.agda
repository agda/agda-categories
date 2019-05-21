{-# OPTIONS --without-K --safe #-}
module Categories.Category.Properties where

open import Level
open import Categories.Category.Core

{-
  A₁ -- f₁ -> B₁
  |           |
  g₁  comm    g₂
  |           |
  V           V
  A₂ -- f₂ -> B₂
  |           |
  h₁  comm    h₂
  |           |
  V           V
  A₃ -- f₃ -> B₃

  then the whole diagram commutes
-}
private 
  square-compose-prop : ∀ {o ℓ e} → Category o ℓ e → Set _
  square-compose-prop C = ∀ {A₁ A₂ A₃ B₁ B₂ B₃}
                            {f₁ : A₁ ⇒ B₁} {f₂ : A₂ ⇒ B₂} {f₃ : A₃ ⇒ B₃}
                            {g₁ : A₁ ⇒ A₂} {g₂ : B₁ ⇒ B₂} {h₁ : A₂ ⇒ A₃} {h₂ : B₂ ⇒ B₃} →
                            CommutativeSquare f₁ g₁ g₂ f₂ →
                            CommutativeSquare f₂ h₁ h₂ f₃ →
                            CommutativeSquare f₁ (h₁ ∘ g₁) (h₂ ∘ g₂) f₃  
    where open Category C

square-compose : ∀ {o ℓ e} (C : Category o ℓ e) →
                   square-compose-prop C
square-compose C {f₁ = f₁} {f₂} {f₃} {g₁} {g₂} {h₁} {h₂} sq₁ sq₂ =
  begin
    (h₂ ∘ g₂) ∘ f₁ ≈⟨ assoc ⟩
    h₂ ∘ g₂ ∘ f₁   ≈⟨ Equiv.refl ⟩∘⟨ sq₁ ⟩
    h₂ ∘ f₂ ∘ g₁   ≈⟨ Equiv.sym assoc ⟩
    (h₂ ∘ f₂) ∘ g₁ ≈⟨ sq₂ ⟩∘⟨ Equiv.refl ⟩
    (f₃ ∘ h₁) ∘ g₁ ≈⟨ assoc ⟩
    f₃ ∘ h₁ ∘ g₁   ∎
  where open Category C
        open HomReasoning

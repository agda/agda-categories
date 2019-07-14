{-# OPTIONS --without-K --safe #-}
open import Categories.Category

module Categories.Object.Coproduct {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level

open Category 𝒞

open import Categories.Morphism.Reasoning 𝒞
open import Categories.Morphism 𝒞

open HomReasoning

private
  variable
    A B C : Obj
    f g h : A ⇒ B

record Coproduct (A B : Obj) : Set (o ⊔ ℓ ⊔ e) where
  infix 10 [_,_]
  
  field
    A+B   : Obj
    i₁    : A ⇒ A+B
    i₂    : B ⇒ A+B
    [_,_] : A ⇒ C → B ⇒ C → A+B ⇒ C

    inject₁ : [ f , g ] ∘ i₁ ≈ f
    inject₂ : [ f , g ] ∘ i₂ ≈ g
    unique   : h ∘ i₁ ≈ f → h ∘ i₂ ≈ g → [ f , g ] ≈ h

  g-η : [ f ∘ i₁ , f ∘ i₂ ] ≈ f
  g-η = unique Equiv.refl Equiv.refl

  η : [ i₁ , i₂ ] ≈ id
  η = unique identityˡ identityˡ

  []-cong₂ : ∀ {C} → {f f′ : A ⇒ C} {g g′ : B ⇒ C} → f ≈ f′ → g ≈ g′ → [ f , g ] ≈ [ f′ , g′ ]
  []-cong₂ f≈f′ g≈g′ = unique (inject₁ ○ ⟺ f≈f′) (inject₂ ○ ⟺ g≈g′)

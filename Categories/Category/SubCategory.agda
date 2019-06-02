{-# OPTIONS --without-K --safe #-}
open import Categories.Category

module Categories.Category.SubCategory {o ℓ e} (𝒞 : Category o ℓ e) where

open Category 𝒞
open HomReasoning

open import Level
open import Data.Product

private
  variable
    a ℓ′ : Level
    A    : Set a

SubCategory : (U : A → Obj) (R : ∀ {a b} → U a ⇒ U b → Set ℓ′) → 
              (∀ {a} → R (id {U a})) →
              (∀ {a b c} {f : U b ⇒ U c} {g : U a ⇒ U b} → R f → R g → R (f ∘ g)) →
              Category _ _ _
SubCategory {A = A} U R Rid R∘ = record
  { Obj       = A
  ; _⇒_       = λ a b → Σ (U a ⇒ U b) R
  ; _≈_       = λ f g → proj₁ f ≈ proj₁ g
  ; id        = id , Rid
  ; _∘_       = λ where
    (f , Rf) (g , Rg) → f ∘ g , R∘ Rf Rg
  ; assoc     = assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; equiv     = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }
  ; ∘-resp-≈  = ∘-resp-≈
  }

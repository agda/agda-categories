{-# OPTIONS --safe --without-K #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Displayed using (Displayed)

module Categories.Category.Construction.Total {o ℓ e o′ ℓ′ e′} {B : Category o ℓ e} (C : Displayed B o′ ℓ′ e′) where

open import Data.Product using (proj₁; proj₂; Σ-syntax; ∃-syntax; -,_)
open import Level using (_⊔_)

open import Categories.Functor.Core using (Functor)

open Category B
open Displayed C
open Equiv′

Total : Set (o ⊔ o′)
Total = Σ[ Carrier ∈ Obj ] Obj[ Carrier ]

record Total⇒ (X Y : Total) : Set (ℓ ⊔ ℓ′) where
  constructor total⇒
  field
    {arr} : proj₁ X ⇒ proj₁ Y
    preserves : proj₂ X ⇒[ arr ] proj₂ Y

open Total⇒ public using (preserves)

∫ : Category (o ⊔ o′) (ℓ ⊔ ℓ′) (e ⊔ e′)
∫ = record
  { Obj = Total
  ; _⇒_ = Total⇒
  ; _≈_ = λ f g → ∃[ p ] preserves f ≈[ p ] preserves g
  ; id = total⇒ id′
  ; _∘_ = λ f g → total⇒ (preserves f ∘′ preserves g)
  ; assoc = -, assoc′
  ; sym-assoc = -, sym-assoc′
  ; identityˡ = -, identityˡ′
  ; identityʳ = -, identityʳ′
  ; identity² = -, identity²′
  ; equiv = record
    { refl = -, refl′
    ; sym = λ p → -, sym′ (proj₂ p)
    ; trans = λ p q → -, trans′ (proj₂ p) (proj₂ q)
    }
  ; ∘-resp-≈ = λ p q → -, ∘′-resp-[]≈ (proj₂ p) (proj₂ q)
  }

display : Functor ∫ B
display = record
  { F₀ = proj₁
  ; F₁ = Total⇒.arr
  ; identity = Equiv.refl
  ; homomorphism = Equiv.refl
  ; F-resp-≈ = proj₁
  }

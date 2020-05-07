{-# OPTIONS --without-K --safe #-}
open import Categories.Category

-- Properties relating Initial and Terminal Objects,
-- and Product / Coproduct via op

module Categories.Object.Duality {o ℓ e} (C : Category o ℓ e) where

open Category C

open import Level

open import Categories.Morphism C
open import Categories.Object.Terminal op
open import Categories.Object.Initial C
open import Categories.Object.Product op
open import Categories.Object.Coproduct C


⊥⇒op⊤ : Initial → Terminal
⊥⇒op⊤ i = record
  { ⊤             = ⊥
  ; ⊤-is-terminal = record
    { !        = !
    ; !-unique = !-unique
    }
  }
  where open Initial i

op⊤⇒⊥ : Terminal → Initial
op⊤⇒⊥ t = record
  { ⊥        = ⊤
  ; ⊥-is-initial = record
    { !        = !
    ; !-unique = !-unique
    }
  }
  where open Terminal t

Coproduct⇒coProduct : ∀ {A B} → Coproduct A B → Product A B
Coproduct⇒coProduct A+B = record
  { A×B      = A+B.A+B
  ; π₁       = A+B.i₁
  ; π₂       = A+B.i₂
  ; ⟨_,_⟩    = A+B.[_,_]
  ; project₁ = A+B.inject₁
  ; project₂ = A+B.inject₂
  ; unique   = A+B.unique
  }
  where
  module A+B = Coproduct A+B

coProduct⇒Coproduct : ∀ {A B} → Product A B → Coproduct A B
coProduct⇒Coproduct A×B = record
  { A+B     = A×B.A×B
  ; i₁      = A×B.π₁
  ; i₂      = A×B.π₂
  ; [_,_]   = A×B.⟨_,_⟩
  ; inject₁ = A×B.project₁
  ; inject₂ = A×B.project₂
  ; unique  = A×B.unique
  }
  where
  module A×B = Product A×B

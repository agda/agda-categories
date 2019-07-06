{-# OPTIONS --without-K --safe #-}
open import Categories.Category

-- Properties relating Initial and Terminal Objects via op

module Categories.Object.OpProperties {o ℓ e} (C : Category o ℓ e) where

open Category C

open import Level

open import Categories.Morphism C
open import Categories.Object.Terminal op
open import Categories.Object.Initial C

⊥⇒op⊤ : Initial → Terminal
⊥⇒op⊤ i = record
  { ⊤        = ⊥
  ; !        = !
  ; !-unique = !-unique
  }
  where open Initial i

op⊤⇒⊥ : Terminal → Initial
op⊤⇒⊥ t = record
  { ⊥        = ⊤
  ; !        = !
  ; !-unique = !-unique
  }
  where open Terminal t

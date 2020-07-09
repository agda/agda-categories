{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Functor.Bifunctor using (Bifunctor)

module Categories.Category.Construction.Cowedges {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′}
  (F : Bifunctor (Category.op C) C D) where

open import Level

open import Categories.Category.Core using (Category)
open import Categories.Diagram.Coend F

Cowedges : Category (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) e′
Cowedges = record
  { Obj = Cowedge
  ; _⇒_ = Cowedge-Morphism
  ; _≈_ = λ M N → u M ≈ u N
  ; id = Cowedge-id
  ; _∘_ = Cowedge-Morphism-∘
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv = record { refl = Equiv.refl ; sym = Equiv.sym ; trans = Equiv.trans }
  ; ∘-resp-≈ = ∘-resp-≈
  }
  where
  open Cowedge-Morphism
  open Category D

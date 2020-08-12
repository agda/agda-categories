{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Functor.Bifunctor using (Bifunctor)

module Categories.Category.Construction.Wedges {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′}
  (F : Bifunctor (Category.op C) C D) where

open import Level

open import Categories.Category.Core using (Category)
open import Categories.Diagram.End F

Wedges : Category (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) e′
Wedges =  record
  { Obj = Wedge
  ; _⇒_ = Wedge-Morphism
  ; _≈_ = λ M N → u M ≈ u N
  ; id = Wedge-id
  ; _∘_ = Wedge-Morphism-∘
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv = record { refl = Equiv.refl ; sym = Equiv.sym ; trans = Equiv.trans }
  ; ∘-resp-≈ = ∘-resp-≈
  }
  where
  open Wedge-Morphism
  open Category D

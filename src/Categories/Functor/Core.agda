{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Functor.Core where

open import Level
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

private
  variable
    o ℓ e o′ ℓ′ e′ : Level

record Functor (C : Category o ℓ e) (D : Category o′ ℓ′ e′) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  eta-equality
  private module C = Category C
  private module D = Category D

  field
    F₀ : C.Obj → D.Obj
    F₁ : ∀ {A B} (f : C [ A , B ]) → D [ F₀ A , F₀ B ]

    identity     : ∀ {A} → D [ F₁ (C.id {A}) ≈ D.id ]
    homomorphism : ∀ {X Y Z} {f : C [ X , Y ]} {g : C [ Y , Z ]} →
                     D [ F₁ (C [ g ∘ f ]) ≈ D [ F₁ g ∘ F₁ f ] ]
    F-resp-≈     : ∀ {A B} {f g : C [ A , B ]} → C [ f ≈ g ] → D [ F₁ f ≈ F₁ g ]

  -- nice shorthands
  ₀ = F₀
  ₁ = F₁

  op : Functor C.op D.op
  op = record
    { F₀           = F₀
    ; F₁           = F₁
    ; identity     = identity
    ; homomorphism = homomorphism
    ; F-resp-≈     = F-resp-≈
    }

private
  op-involutive : {C : Category o ℓ e} {D : Category o′ ℓ′ e′} → (F : Functor C D) → Functor.op (Functor.op F) ≡ F
  op-involutive _ = ≡.refl

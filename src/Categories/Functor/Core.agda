{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Functor.Core where

open import Level
open import Function renaming (id to id→; _∘_ to _●_) using ()
open import Relation.Binary hiding (_⇒_)

import Relation.Binary.Reasoning.Setoid as SetoidR

import Categories.Morphism as M

private
  variable
    o ℓ e o′ ℓ′ e′ o′′ ℓ′′ e′′ : Level
    C D : Category o ℓ e

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

Endofunctor : Category o ℓ e → Set _
Endofunctor C = Functor C C

id : ∀ {C : Category o ℓ e} → Endofunctor C
id {C = C} = record
  { F₀           = id→
  ; F₁           = id→
  ; identity     = refl
  ; homomorphism = refl
  ; F-resp-≈     = id→
  }
  where open Category.Equiv C

infixr 9 _∘F_

-- note that this definition could be shortened a lot by inlining the definitions for
-- identity′ and homomorphism′, but the definitions below are simpler to understand.
_∘F_ : ∀ {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {E : Category o′′ ℓ′′ e′′}
    → Functor D E → Functor C D → Functor C E
_∘F_ {C = C} {D = D} {E = E} F G = record
  { F₀ = F₀ ● G₀
  ; F₁ = F₁ ● G₁
  ; identity = identity′
  ; homomorphism = homomorphism′
  ; F-resp-≈ =  F-resp-≈ ● G-resp-≈
  }
  where
  module C = Category C
  module D = Category D
  module E = Category E
  module F = Functor F
  module G = Functor G
  open F
  open G renaming (F₀ to G₀; F₁ to G₁; F-resp-≈ to G-resp-≈)

  identity′ : ∀ {A} → E [ F₁ (G₁ (C.id {A})) ≈ E.id ]
  identity′ = begin
    F₁ (G₁ C.id) ≈⟨ F-resp-≈ G.identity ⟩
    F₁ D.id      ≈⟨ F.identity ⟩
    E.id         ∎
    where open SetoidR E.hom-setoid

  homomorphism′ : ∀ {X Y Z} {f : C [ X , Y ]} {g : C [ Y , Z ]}
                 → E [ F₁ (G₁ (C [ g ∘ f ])) ≈ E [ F₁ (G₁ g) ∘ F₁ (G₁ f) ] ]
  homomorphism′ {f = f} {g = g} = begin
    F₁ (G₁ (C [ g ∘ f ]))       ≈⟨ F-resp-≈ G.homomorphism ⟩
    F₁ (D [ G₁ g ∘ G₁ f ])      ≈⟨ F.homomorphism ⟩
    E [ F₁ (G₁ g) ∘ F₁ (G₁ f) ] ∎
    where open SetoidR E.hom-setoid

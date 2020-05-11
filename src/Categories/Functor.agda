{-# OPTIONS --without-K --safe #-}
module Categories.Functor where

open import Level
open import Function renaming (id to id→; _∘_ to _●_) using ()

open import Categories.Category
open import Categories.Functor.Core public

private
  variable
    o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ : Level

Endofunctor : Category o ℓ e → Set _
Endofunctor C = Functor C C

id : ∀ {C : Category o ℓ e} → Functor C C
id {C = C} = record
  { F₀           = id→
  ; F₁           = id→
  ; identity     = Category.Equiv.refl C
  ; homomorphism = Category.Equiv.refl C
  ; F-resp-≈     = id→
  }

infixr 9 _∘F_

-- note that this definition could be shortened by inlining the definitions for
-- identity′ and homomorphism′, but the definitions below are simpler to understand.
_∘F_ : ∀ {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {E : Category o″ ℓ″ e″}
    → Functor D E → Functor C D → Functor C E
_∘F_ {C = C} {D = D} {E = E} F G = record
  { F₀ = F.₀ ● G.₀
  ; F₁ = F.₁ ● G.₁
  ; identity = identity′
  ; homomorphism = homomorphism′
  ; F-resp-≈ =  F.F-resp-≈ ● G.F-resp-≈
  }
  where
  module C = Category C using (id)
  module D = Category D using (id)
  module E = Category E using (id; module HomReasoning)
  module F = Functor F
  module G = Functor G

  identity′ : ∀ {A} → E [ F.₁ (G.₁ (C.id {A})) ≈ E.id ]
  identity′ = begin
    F.₁ (G.₁ C.id) ≈⟨ F.F-resp-≈ G.identity ⟩
    F.₁ D.id       ≈⟨ F.identity ⟩
    E.id           ∎
    where open E.HomReasoning

  homomorphism′ : ∀ {X Y Z} {f : C [ X , Y ]} {g : C [ Y , Z ]}
                 → E [ F.₁ (G.₁ (C [ g ∘ f ])) ≈ E [ F.₁ (G.₁ g) ∘ F.₁ (G.₁ f) ] ]
  homomorphism′ {f = f} {g = g} = begin
    F.₁ (G.₁ (C [ g ∘ f ]))         ≈⟨ F.F-resp-≈ G.homomorphism ⟩
    F.₁ (D [ G.₁ g ∘ G.₁ f ])       ≈⟨ F.homomorphism ⟩
    E [ F.₁ (G.₁ g) ∘ F.₁ (G.₁ f) ] ∎
    where open E.HomReasoning

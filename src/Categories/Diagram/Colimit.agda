{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Functor hiding (id)

-- Coimit of a Cocone over a Functor F : J → C
module Categories.Diagram.Colimit
  {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {J : Category o′ ℓ′ e′} (F : Functor J C) where

private
  module C = Category C
  module J = Category J
open C
open HomReasoning
open Equiv
open Functor F

open import Level
open import Data.Product using (proj₂)

open import Categories.Category.Construction.Cocones F renaming (Cocone⇒ to _⇨_)
open import Categories.Object.Initial as I hiding (up-to-iso; transport-by-iso)
open import Categories.Morphism.Reasoning C
open import Categories.Morphism C
open import Categories.Morphism Cocones as MC using () renaming (_≅_ to _⇔_)

private
  variable
    K K′  : Cocone
    A B   : J.Obj
    X Y Z : Obj
    q     : K ⇨ K′

-- A Colimit is an Initial object in the category of Cocones
--   (This could be unpacked...)
record Colimit : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  field
    initial : Initial Cocones

  module initial = Initial initial

  open initial using () renaming (⊥ to colimit) public
  open Cocone colimit hiding (coapex) renaming (N to coapex; ψ to proj; commute to colimit-commute) public

  rep-cocone : ∀ K → colimit ⇨ K
  rep-cocone K = initial.! {K}

  rep : ∀ K → coapex ⇒ Cocone.N K
  rep K = arr
    where open _⇨_ (rep-cocone K)

  unrep : coapex ⇒ X → Cocone
  unrep f = record {
    coapex        = record
      { ψ       = λ A → f ∘ proj A
      ; commute = λ g → pullʳ (colimit-commute g)
      }
    }

  coconify : (f : coapex ⇒ X) → colimit ⇨ unrep f
  coconify f = record
    { arr     = f
    ; commute = refl
    }

  commute : rep K ∘ proj A ≈ Cocone.ψ K A
  commute {K = K} = _⇨_.commute (rep-cocone K)

  unrep-cone : (colimit ⇨ K) → Cocone
  unrep-cone f = unrep (_⇨_.arr f)

  g-η : ∀ {f : coapex ⇒ X} → rep (unrep f) ≈ f
  g-η {f = f} = initial.!-unique (coconify f)

  η-cocone : Cocones [ rep-cocone colimit ≈ Category.id Cocones ]
  η-cocone = initial.⊥-id (rep-cocone colimit)

  η : rep colimit ≈ id
  η = η-cocone

  rep-cocone∘ : Cocones [ Cocones [ q ∘ rep-cocone K ] ≈ rep-cocone K′ ]
  rep-cocone∘ {K = K} {q = q} = Equiv.sym (initial.!-unique (Cocones [ q ∘ rep-cocone K ]))

  rep∘ : ∀ {q : K ⇨ K′} → _⇨_.arr q ∘ rep K ≈ rep K′
  rep∘ {q = q} = rep-cocone∘ {q = q}

  rep-cone-self-id : Cocones [ rep-cocone colimit ≈  Cocones.id  ]
  rep-cone-self-id = initial.!-unique ( Cocones.id )

  rep-self-id : rep colimit ≈ id
  rep-self-id = rep-cone-self-id

open Colimit

up-to-iso-cone : (L₁ L₂ : Colimit) → colimit L₁ ⇔ colimit L₂
up-to-iso-cone L₁ L₂ =  I.up-to-iso Cocones (initial L₁) (initial L₂)

up-to-iso : (L₁ L₂ : Colimit) → coapex L₁ ≅ coapex L₂
up-to-iso L₁ L₂ =  iso-cocone⇒iso-coapex (up-to-iso-cone L₁ L₂)

transport-by-iso-cocone : (C : Colimit) → colimit C ⇔ K → Colimit
transport-by-iso-cocone C C⇿K = record
  { initial =  I.transport-by-iso Cocones (initial C) C⇿K
  }

transport-by-iso : (C : Colimit) → coapex C ≅ X → Colimit
transport-by-iso C C≅X = transport-by-iso-cocone C (proj₂ p)
  where p = cocone-resp-iso (colimit C) C≅X

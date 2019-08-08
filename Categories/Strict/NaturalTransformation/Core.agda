{-# OPTIONS --without-K --safe #-}

module Categories.Strict.NaturalTransformation.Core where

open import Level
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst₂; subst)
open import Data.Product using (Σ; _,_)
open import Axiom.Extensionality.Propositional

open import Categories.Strict.Category
open import Categories.Strict.Functor renaming (id to idF)
open import Categories.Strict.Functor.Properties
import Categories.Strict.Morphism as Morphism
import Categories.Strict.Morphism.Reasoning as MR

private
  variable
    o ℓ o′ ℓ′ : Level
    C D E : Category o ℓ

postulate
  ext-fun : Extensionality o′ o′

record NaturalTransformation {C : Category o ℓ}
                             {D : Category o′ ℓ′}
                             (F G : Functor C D) : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
  eta-equality
  constructor nt -- for using eta
  private
    module C = Category C
    module D = Category D
    module F = Functor F
    module G = Functor G
  open F using (F₀; F₁)
  open G using () renaming (F₀ to G₀; F₁ to G₁)

  field
    η : ∀ X → D [ F₀ X , G₀ X ]
    commute : ∀ {X Y} (f : C [ X , Y ]) → D.CommutativeSquare (F₁ f) (η X) (η Y) (G₁ f)

  op : NaturalTransformation G.op F.op
  op = record
    { η       = η
    ; commute = λ f → sym (commute f)
    }

id : ∀ {F : Functor C D} → NaturalTransformation F F
id {D = D} = record
  { η = λ _ → D.id
  ; commute = λ _ → D.identityˡ ○ ⟺ D.identityʳ
  }
  where
  module D = Category D
  open D.HomReasoning

infixr 9 _∘ᵥ_ _∘ₕ_ _∘ˡ_ _∘ʳ_

-- "Vertical composition"
_∘ᵥ_ : ∀ {F G H : Functor C D} →
         NaturalTransformation G H → NaturalTransformation F G → NaturalTransformation F H
_∘ᵥ_ {C = C} {D = D} {F} {G} {H} X Y = record
  { η       = λ q → D [ X.η q ∘ Y.η q ]
  ; commute = λ f → glue (X.commute f) (Y.commute f)
  }
  where module X = NaturalTransformation X
        module Y = NaturalTransformation Y
        open MR D

-- "Horizontal composition"
_∘ₕ_ : ∀ {F G : Functor C D} {H I : Functor D E} →
         NaturalTransformation H I → NaturalTransformation F G → NaturalTransformation (H ∘F F) (I ∘F G)
_∘ₕ_ {E = E} {F} {I = I} Y X = record
  { η = λ q → E [ I₁ (X.η q) ∘ Y.η (F.F₀ q) ]
  ; commute = λ f → glue ([ I ]-resp-square (X.commute f)) (Y.commute (F.F₁ f))
  }
  where module F = Functor F
        module X = NaturalTransformation X
        module Y = NaturalTransformation Y
        open Functor I renaming (F₀ to I₀; F₁ to I₁)
        open MR E

_∘ˡ_ : ∀ {G H : Functor C D} (F : Functor D E) → NaturalTransformation G H → NaturalTransformation (F ∘F G) (F ∘F H)
_∘ˡ_ {E = E} F α = record
  { η       = λ X → F₁ (η X)
  ; commute = λ f → [ F ]-resp-square (commute f)
  }
  where open Functor F
        open NaturalTransformation α
        open Category.HomReasoning E

_∘ʳ_ : ∀ {G H : Functor D E} → NaturalTransformation G H → (F : Functor C D) → NaturalTransformation (G ∘F F) (H ∘F F)
_∘ʳ_ {D = D} {E = E} {G = G} {H = H} α F = record
  { η       = λ X → η (F₀ X)
  ; commute = λ f → commute (F₁ f)
  }
  where open Functor F
        open NaturalTransformation α

module LeftRightId (F : Functor C D) where
  open Category D
  open HomReasoning
  open Functor F
  module D = Category D

  -- the component proofs are all the same, factor out
  comm : {X Y : Category.Obj C} (f : C [ X , Y ]) → D.id ∘ F₁ f ≡ F₁ f ∘ D.id
  comm _ = sym id-comm

  iso-id-id : (X : Category.Obj C) → Morphism.Iso D {A = F₀ X} D.id D.id
  iso-id-id X = record { isoˡ = identityˡ ; isoʳ = identityʳ }


module _ {F : Functor C D} where
  open Category.HomReasoning D
  open Functor F
  open Category D
  open LeftRightId F

  F⇒F∘id : NaturalTransformation F (F ∘F idF)
  F⇒F∘id = record { η = λ _ → D.id ; commute = comm }

  F⇒id∘F : NaturalTransformation F (idF ∘F F)
  F⇒id∘F = record { η = λ _ → D.id ; commute = comm }

  F∘id⇒F : NaturalTransformation (F ∘F idF) F
  F∘id⇒F = record { η = λ _ → D.id ; commute = comm }

  id∘F⇒F : NaturalTransformation (idF ∘F F) F
  id∘F⇒F = record { η = λ _ → D.id ; commute = comm }

-- Useful for equality of Natural Transformations
module _ {F G : Functor C D} where
  open NaturalTransformation
  open Functor F
  open Functor G renaming (F₀ to G₀; F₁ to G₁)
  module D = Category D

  Σ-≡-intro :
    ∀ {α β}{A : Set α}{B : A → Set β}{a a' : A}{b : B a}{b' : B a'}
    → (Σ (a ≡ a') λ p → subst B p b ≡ b') → (a , b) ≡ (a' , b')
  Σ-≡-intro (refl , refl) = refl

{-
  NT-≡-intro :
    {η₁ η₂ : ∀ X → D [ F₀ X , G₀ X ]}
    {c₁ : ∀ {X Y} (f : C [ X , Y ]) → D.CommutativeSquare (F₁ f) (η₁ X) (η₁ Y) (G₁ f)}
    {c₂ : ∀ {X Y} (f : C [ X , Y ]) → D.CommutativeSquare (F₁ f) (η₂ X) (η₂ Y) (G₁ f)}
    → (X : Category.Obj C) → (Σ (η₁ X ≡ η₂ X) λ p → c₁ ≡ subst ? p c₂) →
      record {η = η₁ ; commute = c₁} ≡ record {η = η₂ ; commute = c₂}
  NT-≡-intro X (refl , refl) = refl
-}
  NT-≡-elim :
    ∀ {α β}{A : Set α}{B : A → Set β}{a a' : A}{b : B a}{b' : B a'}
    → (a , b) ≡ (a' , b') → Σ (a ≡ a') λ p → subst B p b ≡ b'
  NT-≡-elim refl = refl , refl

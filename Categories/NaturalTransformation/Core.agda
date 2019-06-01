{-# OPTIONS --without-K --safe #-}

module Categories.NaturalTransformation.Core where

open import Level
open import Relation.Binary using (Rel; IsEquivalence; Setoid)

open import Categories.Category
open import Categories.Functor.Core renaming (id to idF)
open import Categories.Functor.Properties
import Categories.Square as Square

private
  variable
    o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ : Level
    C D E : Category o ℓ e

record NaturalTransformation {C : Category o ℓ e}
                             {D : Category o′ ℓ′ e′}
                             (F G : Functor C D) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
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
    ; commute = λ f → D.Equiv.sym (commute f)
    }

id : ∀ {F : Functor C D} → NaturalTransformation F F
id {C = C} {D = D} {F} = record
  { η = λ _ → D.id
  ; commute = commute′
  }
  where
  module C = Category C
  module D = Category D
  module F = Functor F
  open F

  commute′ : ∀ {X Y} (f : C [ X , Y ]) → D [ D [ D.id ∘ F₁ f ] ≈ D [ F₁ f ∘ D.id ] ]
  commute′ f = begin
    D [ D.id ∘ F₁ f ] ≈⟨ D.identityˡ ⟩
    F₁ f              ≈⟨ D.Equiv.sym D.identityʳ ⟩
    D [ F₁ f ∘ D.id ] ∎
    where open D.HomReasoning

infixr 9 _∘ᵥ_ _∘ₕ_

-- "Vertical composition"
_∘ᵥ_ : ∀ {F G H : Functor C D} →
         NaturalTransformation G H → NaturalTransformation F G → NaturalTransformation F H
_∘ᵥ_ {C = C} {D = D} {F} {G} {H} X Y = record
  { η       = λ q → D [ X.η q ∘ Y.η q ]
  ; commute = λ f → glue (X.commute f) (Y.commute f)
  }
  where module X = NaturalTransformation X
        module Y = NaturalTransformation Y
        open Square D

-- "Horizontal composition"
_∘ₕ_ : ∀ {F G : Functor C D} {H I : Functor D E} →
         NaturalTransformation H I → NaturalTransformation F G → NaturalTransformation (H ∘F F) (I ∘F G)
_∘ₕ_ {C = C} {D = D} {E = E} {F} {G} {H} {I} Y X = record
  { η = λ q → E [ I₁ (X.η q) ∘ Y.η (F₀ q) ]
  ; commute = λ f → glue ([ I ]-resp-square (X.commute f)) (Y.commute (F₁ f))
  }
  where module F = Functor F
        module I = Functor I
        module X = NaturalTransformation X
        module Y = NaturalTransformation Y
        open F
        open I renaming (F₀ to I₀; F₁ to I₁)
        open Square E

infix 4 _≃_

_≃_ : ∀ {F G : Functor C D} → Rel (NaturalTransformation F G) _
_≃_ {D = D} X Y = ∀ {x} → D [ NaturalTransformation.η X x ≈ NaturalTransformation.η Y x ]

≃-isEquivalence : ∀ {F G : Functor C D} → IsEquivalence (_≃_ {F = F} {G})
≃-isEquivalence {D = D} {F} {G} = record
  { refl  = refl
  ; sym   = λ f → sym f
  ; trans = λ f g → trans f g
  }
  where open Category.Equiv D

≃-setoid : ∀ (F G : Functor C D) → Setoid _ _
≃-setoid F G = record
  { Carrier       = NaturalTransformation F G
  ; _≈_           = _≃_
  ; isEquivalence = ≃-isEquivalence
  }

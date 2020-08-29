{-# OPTIONS --without-K --safe #-}

module Categories.NaturalTransformation.Core where

open import Level

open import Categories.Category
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Properties
import Categories.Morphism as Morphism
import Categories.Morphism.Reasoning as MR

open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

private
  variable
    o ℓ e o′ ℓ′ e′ : Level
    C D E : Category o ℓ e

record NaturalTransformation {C : Category o ℓ e}
                             {D : Category o′ ℓ′ e′}
                             (F G : Functor C D) : Set (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) where
  eta-equality
  private
    module F = Functor F
    module G = Functor G
  open F using (F₀; F₁)
  open Category D hiding (op)

  field
    η           : ∀ X → D [ F₀ X , G.F₀ X ]
    commute     : ∀ {X Y} (f : C [ X , Y ]) → η Y ∘ F₁ f ≈ G.F₁ f ∘ η X
    -- We introduce an extra proof to ensure the opposite of the opposite of a natural
    -- transformation is definitionally equal to itself.
    sym-commute : ∀ {X Y} (f : C [ X , Y ]) → G.F₁ f ∘ η X ≈ η Y ∘ F₁ f

  op : NaturalTransformation G.op F.op
  op = record
    { η           = η
    ; commute     = sym-commute
    ; sym-commute = commute
    }

-- Just like `Category`, we introduce a helper definition to ease the actual
-- construction of a natural transformation.
record NTHelper {C : Category o ℓ e}
                {D : Category o′ ℓ′ e′}
                (F G : Functor C D) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  private
    module G = Functor G
  open Functor F using (F₀; F₁)
  open Category D hiding (op)
  field
    η           : ∀ X → D [ F₀ X , G.F₀ X ]
    commute     : ∀ {X Y} (f : C [ X , Y ]) → η Y ∘ F₁ f ≈ G.F₁ f ∘ η X

ntHelper : ∀ {F G : Functor C D} → NTHelper F G → NaturalTransformation F G
ntHelper {D = D} α = record
  { η           = η
  ; commute     = commute
  ; sym-commute = λ f → Equiv.sym (commute f)
  }
  where open NTHelper α
        open Category D

-- Don't use ntHelper as it produces non-reduction in other places
-- and be pedantic about arguments too, this helps inference too.
id : ∀ {F : Functor C D} → NaturalTransformation F F
id {D = D} {F} = record
  { η = λ _ → D.id
  ; commute = λ f → id-comm-sym {f = Functor.F₁ F f}
  ; sym-commute = λ f → id-comm {f = Functor.F₁ F f}
  }
  where
  module D = Category D
  open MR D

infixr 9 _∘ᵥ_ _∘ₕ_ _∘ˡ_ _∘ʳ_

-- "Vertical composition"
_∘ᵥ_ : ∀ {F G H : Functor C D} →
         NaturalTransformation G H → NaturalTransformation F G → NaturalTransformation F H
_∘ᵥ_ {C = C} {D = D} {F} {G} {H} X Y = record
  { η       = λ q → D [ X.η q ∘ Y.η q ]
  ; commute = λ f → glue (X.commute f) (Y.commute f)
  ; sym-commute = λ f → Category.Equiv.sym D (glue (X.commute f) (Y.commute f))
  }
  where module X = NaturalTransformation X
        module Y = NaturalTransformation Y
        open MR D

-- "Horizontal composition"
_∘ₕ_ : ∀ {F G : Functor C D} {H I : Functor D E} →
         NaturalTransformation H I → NaturalTransformation F G → NaturalTransformation (H ∘F F) (I ∘F G)
_∘ₕ_ {E = E} {F} {I = I} Y X = ntHelper record
  { η = λ q → E [ I₁ (X.η q) ∘ Y.η (F.F₀ q) ]
  ; commute = λ f → glue ([ I ]-resp-square (X.commute f)) (Y.commute (F.F₁ f))
  }
  where module F = Functor F
        module X = NaturalTransformation X
        module Y = NaturalTransformation Y
        open Functor I renaming (F₀ to I₀; F₁ to I₁)
        open MR E

_∘ˡ_ : ∀ {G H : Functor C D} (F : Functor D E) → NaturalTransformation G H → NaturalTransformation (F ∘F G) (F ∘F H)
_∘ˡ_ F α = record
  { η           = λ X → F₁ (η X)
  ; commute     = λ f → [ F ]-resp-square (commute f)
  ; sym-commute = λ f → [ F ]-resp-square (sym-commute f)
  }
  where open Functor F
        open NaturalTransformation α

_∘ʳ_ : ∀ {G H : Functor D E} → NaturalTransformation G H → (F : Functor C D) → NaturalTransformation (G ∘F F) (H ∘F F)
_∘ʳ_ {D = D} {E = E} {G = G} {H = H} α F = record
  { η           = λ X → η (F₀ X)
  ; commute     = λ f → commute (F₁ f)
  ; sym-commute = λ f → sym-commute (F₁ f)
  }
  where open Functor F
        open NaturalTransformation α

id∘id⇒id : {C : Category o ℓ e} → NaturalTransformation {C = C} {D = C} (idF ∘F idF) idF
id∘id⇒id {C = C} = record
  { η           = λ _ → Category.id C
  ; commute     = λ f → MR.id-comm-sym C {f = f}
  ; sym-commute = λ f → MR.id-comm C {f = f}
  }

id⇒id∘id : {C : Category o ℓ e} → NaturalTransformation {C = C} {D = C} idF (idF ∘F idF)
id⇒id∘id {C = C} = record
  { η           = λ _ → Category.id C
  ; commute     = λ f → MR.id-comm-sym C {f = f}
  ; sym-commute = λ f → MR.id-comm C {f = f}
  }

module _ {F : Functor C D} where
  open Category.HomReasoning D
  open Functor F
  open Category D
  open MR D
  private module D = Category D

  F⇒F∘id : NaturalTransformation F (F ∘F idF)
  F⇒F∘id = record { η = λ _ → D.id ; commute = λ _ → id-comm-sym ; sym-commute = λ _ → id-comm }

  F⇒id∘F : NaturalTransformation F (idF ∘F F)
  F⇒id∘F = record { η = λ _ → D.id ; commute = λ _ → id-comm-sym ; sym-commute = λ _ → id-comm }

  F∘id⇒F : NaturalTransformation (F ∘F idF) F
  F∘id⇒F = record { η = λ _ → D.id ; commute = λ _ → id-comm-sym ; sym-commute = λ _ → id-comm }

  id∘F⇒F : NaturalTransformation (idF ∘F F) F
  id∘F⇒F = record { η = λ _ → D.id ; commute = λ _ → id-comm-sym ; sym-commute = λ _ → id-comm }

private
  op-involutive : {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {F G : Functor C D} →
                  (α : NaturalTransformation F G) → NaturalTransformation.op (NaturalTransformation.op α) ≡ α
  op-involutive _ = ≡.refl

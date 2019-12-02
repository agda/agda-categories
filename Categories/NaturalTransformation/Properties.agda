{-# OPTIONS --without-K --safe #-}

module Categories.NaturalTransformation.Properties where

open import Level
open import Data.Product using (Σ; _,_)
open import Function.Equality using (Π)

open import Categories.Category
open import Categories.Category.Product
open import Categories.Category.Instance.Setoids
open import Categories.Functor
open import Categories.Functor.Construction.Constant
open import Categories.Functor.Construction.LiftSetoids
open import Categories.Functor.Bifunctor
open import Categories.NaturalTransformation renaming (id to idN)
open import Categories.NaturalTransformation.NaturalIsomorphism
open import Categories.NaturalTransformation.Dinatural hiding (_≃_)

import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ ℓ′ e : Level
    C D E : Category o ℓ e

module _ {F G : Functor C D} where
  private
    module C = Category C
    module D = Category D
    open D
    open MR D
    open HomReasoning
    open Functor

    F′ : Bifunctor C.op C D
    F′ = F ∘F πʳ

    G′ : Bifunctor C.op C D
    G′ = G ∘F πʳ

  NT⇒Dinatural : NaturalTransformation F G → DinaturalTransformation F′ G′
  NT⇒Dinatural β = dtHelper record
    { α       = η
    ; commute = λ f → ∘-resp-≈ʳ (elimʳ (identity F)) ○ ⟺ (commute f) ○ introˡ (identity G)
    }
    where open NaturalTransformation β

  Dinatural⇒NT : DinaturalTransformation F′ G′ → NaturalTransformation F G
  Dinatural⇒NT θ = ntHelper record
    { η       = α
    ; commute = λ f → introˡ (identity G) ○ ⟺ (commute f) ○ ∘-resp-≈ʳ (elimʳ (identity F))
    }
    where open DinaturalTransformation θ

  replaceˡ : ∀ {F′} → NaturalTransformation F G → F ≃ F′ → NaturalTransformation F′ G
  replaceˡ {F′} α F≃F′ = ntHelper record
    { η       = λ X → η X ∘ ⇐.η X
    ; commute = λ {X Y} f → begin
      (η Y ∘ ⇐.η Y) ∘ F₁ F′ f ≈⟨ pullʳ (⇐.commute f) ⟩
      η Y ∘ F₁ F f ∘ ⇐.η X    ≈⟨ pullˡ (commute f) ○ assoc ⟩
      F₁ G f ∘ η X ∘ ⇐.η X    ∎
    }
    where open NaturalIsomorphism F≃F′
          open NaturalTransformation α

  replaceʳ : ∀ {G′} → NaturalTransformation F G → G ≃ G′ → NaturalTransformation F G′
  replaceʳ {G′} α G≃G′ = ntHelper record
    { η       = λ X → ⇒.η X ∘ η X
    ; commute = λ {X Y} f → begin
      (⇒.η Y ∘ η Y) ∘ F₁ F f ≈⟨ pullʳ (commute f) ⟩
      ⇒.η Y ∘ F₁ G f ∘ η X   ≈⟨ pullˡ (⇒.commute f) ○ assoc ⟩
      F₁ G′ f ∘ ⇒.η X ∘ η X  ∎
    }
    where open NaturalIsomorphism G≃G′
          open NaturalTransformation α  

module _ (F : Bifunctor C D E) where

  -- there is natural transformation between two partially applied bifunctors.

  appˡ-nat : ∀ {X Y} → (f : Category._⇒_ C X Y) → NaturalTransformation (appˡ F X) (appˡ F Y)
  appˡ-nat f = F ∘ˡ (constNat f ※ⁿ idN)

  appʳ-nat : ∀ {X Y} → (f : Category._⇒_ D X Y) → NaturalTransformation (appʳ F X) (appʳ F Y)
  appʳ-nat f = F ∘ˡ (idN ※ⁿ constNat f)

module _ {F G : Bifunctor C D E} (α : NaturalTransformation F G) where
  private
    module C = Category C
    module D = Category D
    module E = Category E

  appˡ′ : ∀ X → NaturalTransformation (appˡ F X) (appˡ G X)
  appˡ′ X = α ∘ₕ idN

  appʳ′ : ∀ X → NaturalTransformation (appʳ F X) (appʳ G X)
  appʳ′ X = α ∘ₕ idN

-- unlift universe level
module _ {c ℓ ℓ′ e} {F G : Functor C (Setoids c ℓ)} (α : NaturalTransformation (LiftSetoids ℓ′ e ∘F F) (LiftSetoids ℓ′ e ∘F G)) where
  open NaturalTransformation α
  open Π

  unlift-nat : NaturalTransformation F G
  unlift-nat = ntHelper record
    { η       = λ X → record
      { _⟨$⟩_ = λ x → lower (η X ⟨$⟩ lift x)
      ; cong = λ eq → lower (cong (η X) (lift eq))
      }
    ; commute = λ f eq → lower (commute f (lift eq))
    }

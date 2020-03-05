{-# OPTIONS --without-K --safe #-}

module Categories.Category.Construction.Elements where

-- Category of Elements -- given a functor into Sets, construct the category of elements 'above' each object
-- see https://ncatlab.org/nlab/show/category+of+elements
open import Level
open import Data.Product using (Σ; _,_; Σ-syntax; proj₁; proj₂; map)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)
open import Function hiding (_∘_) renaming (id to idf)

open import Categories.Category using (Category)
open import Categories.Functor hiding (id)
open import Categories.Category.Instance.Sets
open import Categories.Category.Instance.Cats
open import Categories.Category.Construction.Functors
open import Categories.NaturalTransformation.NaturalIsomorphism hiding (refl; sym; trans)
open import Categories.NaturalTransformation hiding (id)
import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e o′ : Level

-- the first, most explicit definition is taken as 'canonical'.
Elements : {C : Category o ℓ e} → Functor C (Sets o′) → Category (o ⊔ o′) (ℓ ⊔ o′) e
Elements {C = C} F = record
  { Obj       = Σ Obj F₀
  ; _⇒_       = λ { (c , x) (c′ , x′) → Σ (c ⇒ c′) (λ f → F₁ f x ≡ x′)  }
  ; _≈_       = λ p q → proj₁ p ≈ proj₁ q
  ; id        = id , identity
  ; _∘_       = λ { (f , Ff≡) (g , Fg≡) → f ∘ g ,  trans homomorphism (trans (cong (F₁ f) Fg≡) Ff≡)}
  ; assoc     = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv     = record { refl = Equiv.refl ; sym = Equiv.sym ; trans = Equiv.trans }
  ; ∘-resp-≈  = ∘-resp-≈
  }
  where
  open Category C
  open Functor F

-- This induces a functor. It is largely uninteresting as it is as close to 'strict'
-- as things get in this setting.
El : {C : Category o ℓ e} → Functor (Functors C (Sets o′)) (Cats (o ⊔ o′) (ℓ ⊔ o′) e)
El {C = C} = record
  { F₀ = Elements
  ; F₁ = λ A⇒B → record
    { F₀ = map idf (η A⇒B _)
    ; F₁ = map idf λ {f} eq → trans (sym $ commute A⇒B f) (cong (η A⇒B _) eq)
    ; identity = Equiv.refl
    ; homomorphism = Equiv.refl
    ; F-resp-≈ = idf
    }
  ; identity = λ {P} → record
    { F⇒G = record
      { η           = λ X → id , identity P
      ; commute     = λ _ → MR.id-comm-sym C
      ; sym-commute = λ _ → MR.id-comm C
      }
    ; F⇐G = record
      { η           = λ X → id , identity P
      ; commute     = λ _ → MR.id-comm-sym C
      ; sym-commute = λ _ → MR.id-comm C
      }
    ; iso = λ X → record { isoˡ = identityˡ ; isoʳ = identityʳ } }
  ; homomorphism = λ {X₁} {Y₁} {Z₁} → record
    { F⇒G = record
      { η           = λ X → id , identity Z₁
      ; commute     = λ _ → MR.id-comm-sym C
      ; sym-commute = λ _ → MR.id-comm C
      }
    ; F⇐G = record
      { η           = λ X → id , identity Z₁
      ; commute     = λ _ → MR.id-comm-sym C
      ; sym-commute = λ _ → MR.id-comm C
      }
    ; iso = λ X → record { isoˡ = identityˡ ; isoʳ = identityʳ }
    }
  ; F-resp-≈ = λ {_} {B₁} f≈g → record
    { F⇒G = record
      { η           = λ _ → id , trans (identity B₁) f≈g
      ; commute     = λ _ → MR.id-comm-sym C
      ; sym-commute = λ _ → MR.id-comm C
      }
    ; F⇐G = record
      { η           = λ _ → id , trans (identity B₁) (sym f≈g)
      ; commute     = λ _ → MR.id-comm-sym C
      ; sym-commute = λ _ → MR.id-comm C
      }
    ; iso = λ X → record { isoˡ = identityˡ ; isoʳ = identityʳ } }
  }
  where
  open Category C
  open Functor
  open NaturalTransformation

-- But there are all sorts of interesting alternate definitions
-- note how this one is WAY less level polymorphic than the above!
-- it looks like it contains more information... but not really either.
{-  Unfinished because it is super tedious and not informative!
module Alternate-Pullback {C : Category (suc o) o o} (F : Functor C (Sets o)) where
  open import Categories.Category.Instance.PointedSets
  open import Categories.Category.Instance.Cats
  open import Categories.Diagram.Pullback (Cats (suc o) o o)
  open import Categories.Category.Product using (_※_; πˡ)
  open Category C
  open Functor F

  Pb : Pullback F Underlying
  Pb = record
    { P = Elements F
    ; p₁ = record
     { F₀ = proj₁
     ; F₁ = proj₁
     ; identity = Equiv.refl
     ; homomorphism = Equiv.refl
     ; F-resp-≈ = idf
     }
    ; p₂ = record
     { F₀ = map F₀ idf
     ; F₁ = map F₁ idf
     ; identity = λ x → identity {_} {x}
     ; homomorphism = λ _ → homomorphism
     ; F-resp-≈ = λ f≈g _ → F-resp-≈ f≈g
     }
    ; commute = record
      { F⇒G = record { η = λ _ → idf ; commute = λ _ → refl }
      ; F⇐G = record { η = λ _ → idf ; commute = λ _ → refl }
      ; iso = λ X → record { isoˡ = refl ; isoʳ = refl }
      }
    ; universal = λ {A} {h₁} {h₂} NI → record
      { F₀ = λ X → Functor.F₀ h₁ X , η (F⇐G NI) X (proj₂ $ Functor.F₀ h₂ X)
      ; F₁ = λ f → Functor.F₁ h₁ f ,
        trans (sym $ commute (F⇐G NI) f) (cong (η (F⇐G NI) _) (proj₂ $ Functor.F₁ h₂ f))
      ; identity = Functor.identity h₁
      ; homomorphism = Functor.homomorphism h₁
      ; F-resp-≈ = Functor.F-resp-≈ h₁
      }
    ; unique = λ πˡ∘i≃h₁ map∘i≃h₂ → record
      { F⇒G = record { η = λ X → {!!} ; commute = {!!} }
      ; F⇐G = record { η = {!!} ; commute = {!!} }
      ; iso = λ X → record { isoˡ = {!!} ; isoʳ = {!!} }
      }
    ; p₁∘universal≈h₁ = {!!}
    ; p₂∘universal≈h₂ = {!!}
    }
    where
    open NaturalTransformation
    open NaturalIsomorphism
-}

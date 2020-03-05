{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Properties.Cats where

open import Data.Product using (_,_)

open import Categories.Category
open import Categories.Category.Construction.Functors
  using (Functors; eval; module curry)
open import Categories.Category.Cartesian using (Cartesian)
import Categories.Category.CartesianClosed as CCC
import Categories.Category.CartesianClosed.Canonical as Canonical
open import Categories.Category.Instance.Cats using (Cats)
open import Categories.Category.Monoidal.Instance.Cats
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.Functor.Construction.Constant using (constNat)
import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation
  using (NaturalTransformation; _∘ˡ_) renaming (id to idNT)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (NaturalIsomorphism; _≃_; module LeftRightId)

-- It's easier to define exponentials with respect to the *canonical*
-- product.  The more generic version can then be given by appealing
-- to uniqueness (up to iso) of products.

module CanonicallyCartesianClosed {l} where
  private
    module Cats = Category (Cats l l l)
    module Cart = Cartesian (Product.Cats-is {l} {l} {l})
  open Cats using (_⇒_) renaming (Obj to Cat)
  open Cart hiding (η)

  infixr 9 _^_

  _^_ : Cat → Cat → Cat
  B ^ A = Functors A B

  -- The β law (aka computation principle) for exponential objects

  eval-comp : ∀ {A B C} {G : C × A ⇒ B} → eval ∘F (curry.F₀ G ⁂ idF) ≃ G
  eval-comp {A} {B} {C} {G} = record
    { F⇒G = record
      { η           = λ _ → id B
      ; commute     = λ _ → ∘-resp-≈ʳ B commute ○ MR.id-comm-sym B
      ; sym-commute = λ _ → ⟺ (∘-resp-≈ʳ B commute ○ MR.id-comm-sym B)
      }
    ; F⇐G = record
      { η           = λ _ → id B
      ; commute     = λ _ → ⟺ (MR.id-comm B ○ ∘-resp-≈ʳ B commute)
      ; sym-commute = λ _ → MR.id-comm B ○ ∘-resp-≈ʳ B commute
      }
    ; iso = iso-id-id
    }
    where
      open Functor G renaming (F₀ to G₀; F₁ to G₁)
      open Category hiding (_∘_)
      open Category B using (_∘_)
      open HomReasoning B
      open LeftRightId G

      commute : ∀ {a₁ a₂ b₁ b₂} {f₁ : C [ a₁ , b₁ ]} {f₂ : A [ a₂ , b₂ ]} →
                B [ (G₁ (f₁ , id A) ∘ G₁ (id C , f₂)) ≈ G₁ (f₁ , f₂) ]
      commute {_} {_} {_} {_} {f₁} {f₂} = begin
          G₁ (f₁ , id A) ∘ G₁ (id C , f₂)
        ≈˘⟨ homomorphism ⟩
          G₁ (C [ f₁ ∘ id C ] , A [ id A ∘ f₂ ])
        ≈⟨ F-resp-≈ (identityʳ C , identityˡ A) ⟩
          G₁ (f₁ , f₂)
        ∎

  -- The η law (aka uniqueness principle) for exponential objects

  η-exp : ∀ {A B C} {H : C ⇒ B ^ A} → H ≃ curry.F₀ (eval ∘F (H ⁂ idF))
  η-exp {A} {B} {C} {H} = record
    { F⇒G = record
      { η = λ _ → record
        { η           = λ _ → id B
        ; commute     = λ f → ⟺ (MR.id-comm B ○ ∘-resp-≈ʳ B (commute₁ f))
        ; sym-commute = λ f → MR.id-comm B ○ ∘-resp-≈ʳ B (commute₁ f)
        }
      ; commute       = λ f → ⟺ (MR.id-comm B ○ ∘-resp-≈ʳ B (commute₂ f))
      ; sym-commute   = λ f → MR.id-comm B ○ ∘-resp-≈ʳ B (commute₂ f)
      }
    ; F⇐G = record
      { η = λ _ → record
        { η           = λ _ → id B
        ; commute     = λ f → ∘-resp-≈ʳ B (commute₁ f) ○ MR.id-comm-sym B
        ; sym-commute = λ f → ⟺ (∘-resp-≈ʳ B (commute₁ f) ○ MR.id-comm-sym B)
        }
      ; commute       = λ f → ∘-resp-≈ʳ B (commute₂ f) ○ MR.id-comm-sym B
      ; sym-commute   = λ f → ⟺ (∘-resp-≈ʳ B (commute₂ f) ○ MR.id-comm-sym B)
      }
    ; iso = λ _ → record { isoˡ = identity² B; isoʳ = identity² B }
    }
    where
      open Functor using (identity) renaming (F₁ to _$₁_)
      open Functor H hiding (identity) renaming (F₀ to H₀; F₁ to H₁)
      open Category hiding (_∘_)
      open Category B using (_∘_)
      open HomReasoning B
      open NaturalTransformation
      open LeftRightId H

      commute₁ : ∀ {a b c} (f : A [ a , b ]) →
                 B [ (η (H₁ (id C)) b ∘ (H₀ c $₁ f)) ≈ H₀ c $₁ f ]
      commute₁ {_} {b} {c} f = begin
        η (H₁ (id C)) b ∘ (H₀ c $₁ f)  ≈⟨ ∘-resp-≈ˡ B (identity H) ⟩
        id B ∘ (H₀ c $₁ f)             ≈⟨ identityˡ B ⟩
        H₀ c $₁ f                      ∎

      commute₂ : ∀ {c₁ c₂} (f : C [ c₁ , c₂ ]) {a} →
                 B [ (η (H₁ f) a ∘ (H₀ c₁ $₁ id A)) ≈ η (H₁ f) a ]
      commute₂ {c} {_} f {a} = begin
        η (H₁ f) a ∘ (H₀ c $₁ id A)    ≈⟨ ∘-resp-≈ʳ B (identity (H₀ c)) ⟩
        η (H₁ f) a ∘ id B              ≈⟨ identityʳ B ⟩
        η (H₁ f) a                     ∎

  curry-unique : ∀ {A B C} {G : C ⇒ B ^ A} {H : C × A ⇒ B} →
                 eval ∘F (G ⁂ idF) ≃ H → G ≃ curry.F₀ H
  curry-unique {A} {B} {C} {G} {H} hyp =
    begin
      G
    ≈⟨ η-exp {A} {B} {C} {G} ⟩
      curry.F₀ (eval ∘F (G ⁂ idF))
    ≈⟨ curry.resp-NI {F = eval ∘F (G ⁂ idF)} {H} hyp ⟩
      curry.F₀ H
    ∎
    where
      open Functor
      open Cats.HomReasoning

  Cats-CCC : Canonical.CartesianClosed (Cats l l l)
  Cats-CCC = record
    { !            = !
    ; π₁           = π₁
    ; π₂           = π₂
    ; ⟨_,_⟩        = ⟨_,_⟩
    ; !-unique     = !-unique
    ; π₁-comp      = λ {_} {_} {F} {_} {G} → project₁ {h = F} {i = G}
    ; π₂-comp      = λ {_} {_} {F} {_} {G} → project₂ {h = F} {i = G}
    ; ⟨,⟩-unique   = unique
    ; eval         = eval
    ; curry        = curry.F₀
    ; eval-comp    = λ {_} {_} {_} {G} → eval-comp {G = G}
    ; curry-resp-≈ = λ {_} {_} {_} {G} {H} → curry.resp-NI {F = G} {H}
    ; curry-unique = λ {_} {_} {_} {G} {H} → curry-unique {G = G} {H}
    }

  open Canonical.CartesianClosed Cats-CCC

Cats-CCC : ∀ {l} → CCC.CartesianClosed (Cats l l l)
Cats-CCC =
  Canonical.Equivalence.fromCanonical _ CanonicallyCartesianClosed.Cats-CCC

module CartesianClosed {l} = CCC.CartesianClosed (Cats-CCC {l})

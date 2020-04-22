{-# OPTIONS --without-K --safe #-}

open import Level
open import Categories.Category using () renaming (Category to Setoid-Category)
open import Categories.Category.Monoidal using (Monoidal)

module Categories.Pseudofunctor.Instance.EnrichedUnderlying
  {o ℓ e} {V : Setoid-Category o ℓ e} (M : Monoidal V) (v : Level) where

-- The "forgetful" functor from V-enriched categories to their
-- underlying Setoid-categories.

open import Data.Product as Prod using (_,_)

open import Categories.Bicategory.Instance.Cats
open import Categories.Bicategory.Instance.EnrichedCats M
open import Categories.Enriched.Category M
open import Categories.Enriched.Category.Underlying M
open import Categories.Enriched.Functor M
open import Categories.Enriched.NaturalTransformation M
open import Categories.Functor using () renaming (Functor to Setoid-Functor) -- makes some things print more nicely
import Categories.Morphism.Reasoning as MorphismReasoning
open import Categories.NaturalTransformation using (ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)
open import Categories.Pseudofunctor using (Pseudofunctor)

private
  module V = Setoid-Category V
  module UnderlyingReasoning {c} (C : Category c) where
    open Underlying C public hiding (id)
    open HomReasoning public
    open MorphismReasoning (Underlying C) public
  open NaturalTransformation using (_[_])

  -- Aliases used to shorten some proof expressions

  module UF = UnderlyingFunctor
  infixr 14 _$₀_ _$₁_
  _$₀_ = UF.F₀
  _$₁_ = UF.F₁

-- The "forgetful" pseudofunctor mapping a V-enriched category to its
-- underlying Setoid-category.
--
-- Note that all the equational reasoning happens in the underlying
-- (ordinary) categories!

EnrichedUnderlying : Pseudofunctor (EnrichedCats v) (Cats v ℓ e)
EnrichedUnderlying = record
  { P₀ = Underlying
  ; P₁ = λ {x y} → record
    { F₀ = UnderlyingFunctor
    ; F₁ = UnderlyingNT
    ; identity     = V.Equiv.refl {x = Category.id y}
    ; homomorphism = V.Equiv.refl
    ; F-resp-≈     = λ eq → eq
    }
  ; P-identity = λ {C} →
    let module C = Underlying C
        open UnderlyingReasoning C
    in niHelper record
      { η = λ _ → ntHelper record
        { η       = λ c → C.id {c}
        ; commute = λ f → begin
            C.id ∘ f              ≈⟨ identityˡ ⟩
            f                     ≈˘⟨ identityʳ ○ V.identityˡ ⟩
            (V.id V.∘ f) ∘ C.id   ∎
        }
      ; η⁻¹ = λ _ → ntHelper record
        { η       = λ c → C.id {c}
        ; commute = λ f → begin
            C.id ∘ (V.id V.∘ f)   ≈⟨ identityˡ ○ V.identityˡ ⟩
            f                     ≈˘⟨ identityʳ ⟩
            f ∘ C.id              ∎
        }
      ; commute = λ _ → V.Equiv.refl
      ; iso     = λ _ → record { isoˡ = C.identityˡ {f = Category.id C}
                               ; isoʳ = C.identityʳ {f = Category.id C} }
      }
  ; P-homomorphism = λ {C D E} →
    let module C = Underlying C
        module D = Underlying D
        module E = Underlying E
        open UnderlyingReasoning E
    in niHelper record
      { η = λ{ (F , G) → ntHelper record
        { η       = λ _ → E.id
        ; commute = λ f → begin
            E.id ∘ F $₁ G $₁ f     ≈⟨ id-comm-sym ⟩
            F $₁ G $₁ f ∘ E.id     ≈˘⟨ V.assoc ⟩∘⟨refl ⟩
            (F ∘F G) $₁ f ∘ E.id   ∎
        } }
      ; η⁻¹ = λ{ (F , G) → ntHelper record
        { η       = λ _ → E.id
        ; commute = λ f → begin
            E.id ∘ (F ∘F G) $₁ f   ≈⟨ id-comm-sym ⟩
            (F ∘F G) $₁ f ∘ E.id   ≈⟨ V.assoc ⟩∘⟨refl ⟩
            F $₁ G $₁ f ∘ E.id     ∎
        } }
      ; commute = λ _ → id-comm-sym
      ; iso     = λ _ → record { isoˡ = E.identityˡ ; isoʳ = E.identityʳ }
      }
  ; unitaryˡ = λ {_ D} →
    let module D = Underlying D
        open UnderlyingReasoning D
    in begin
      D.id ∘ D.id ∘ (V.id V.∘ D.id) ∘ D.id   ≈⟨ identityˡ ○ identityˡ ⟩
      (V.id V.∘ D.id) ∘ D.id                 ≈⟨ identityʳ ○ V.identityˡ ⟩
      D.id                                   ∎
  ; unitaryʳ = λ {C D F X} →
    let module C = Underlying C
        module D = Underlying D
        open UnderlyingReasoning D
    in begin
      D.id ∘ D.id ∘ F $₁ C.id ∘ D.id   ≈⟨ identityˡ ○ identityˡ ○ identityʳ ⟩
      F $₁ C.id                        ≈⟨ UF.identity F ⟩
      D.id                             ∎
  ; assoc = λ {_ B C D F G H X} →
    let module B = Underlying B
        module C = Underlying C
        module D = Underlying D
        open UnderlyingReasoning D
    in ∘-resp-≈ʳ (begin
      D.id ∘ (H ∘F G) $₁ B.id ∘ D.id   ≈⟨ refl⟩∘⟨ V.assoc ⟩∘⟨refl ⟩
      D.id ∘ H $₁ G $₁ B.id ∘ D.id     ≈⟨ refl⟩∘⟨ UF.F-resp-≈ H
                                                    (UF.identity G) ⟩∘⟨refl ⟩
      D.id ∘ H $₁ C.id ∘ D.id          ≈⟨ id-comm-sym ⟩
      (H $₁ C.id ∘ D.id) ∘ D.id        ∎)
  }

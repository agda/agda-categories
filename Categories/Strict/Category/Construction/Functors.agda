{-# OPTIONS --without-K --safe #-}
module Categories.Strict.Category.Construction.Functors where

-- the "Functor Category", often denoted [ C , D ]

open import Level
open import Data.Product using (Σ; _,_; _×_; uncurry′; proj₁)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

open import Categories.Strict.Category
open import Categories.Strict.Functor
open import Categories.Strict.Functor.Bifunctor
open import Categories.Strict.NaturalTransformation renaming (id to idN)
-- open import Categories.NaturalTransformation.Equivalence using (_≃_; ≃-isEquivalence)
import Categories.Strict.Morphism.Reasoning as MR

private
  variable
    o ℓ o′ ℓ′ : Level
    C D : Category o ℓ

-- The reason the proofs below are so easy is that _∘ᵥ_ 'computes' all the way down into
-- expressions in D, from which the properties follow.
Functors : Category o ℓ → Category o′ ℓ′ → Category (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) {!!}
Functors C D = record
  { Obj       = Functor C D
  ; _⇒_       = NaturalTransformation
  ; id        = idN
  ; _∘_       = _∘ᵥ_
  ; assoc     = {!λ {A} {B} {C₁} {D₁} {f} {g} {g} → cong η ?!} -- assoc
  ; identityˡ = {!!} -- identityˡ
  ; identityʳ = {!!} -- identityʳ
  }
  where module C = Category C
        module D = Category D
        open D
        open NaturalTransformation

-- Godement product ?
{-
product : {A B C : Category o ℓ} → Bifunctor (Functors B C) (Functors A B) (Functors A C)
product {A = A} {B = B} {C = C} = record
  { F₀ = uncurry′ _∘F_
  ; F₁ = uncurry′ _∘ₕ_
  ; identity = λ {f} → identityʳ ○ identity {D = C} (proj₁ f)
  ; homomorphism = λ { {_ , F₂} {G₁ , G₂} {H₁ , _} {f₁ , f₂} {g₁ , g₂} {x} → begin
      F₁ H₁ (η g₂ x B.∘ η f₂ x) ∘ η g₁ (F₀ F₂ x) ∘ η f₁ (F₀ F₂ x)
          ≈⟨ cong (_∘ _) (homomorphism H₁) ○ assoc ○ (cong ∘_) (⟺ assoc) ⟩
      F₁ H₁ (η g₂ x) ∘ (F₁ H₁ (η f₂ x) ∘ η g₁ (F₀ F₂ x)) ∘ η f₁ (F₀ F₂ x)
          ≈⟨  ⟺ ( refl⟩∘⟨ ( commute g₁ (η f₂ x) ⟩∘⟨refl) ) ⟩
      F₁ H₁ (η g₂ x) ∘ (η g₁ (F₀ G₂ x) ∘ F₁  G₁ (η f₂ x)) ∘ η f₁ (F₀ F₂ x)
          ≈⟨ cong ? assoc ○ ⟺ assoc ⟩
      (F₁ H₁ (η g₂ x) ∘ η g₁ (F₀ G₂ x)) ∘ F₁ G₁ (η f₂ x) ∘ η f₁ (F₀ F₂ x) ∎ }
  }
  where
    open Category C
    open HomReasoning
    open Functor
    module B = Category B
    open NaturalTransformation
-}

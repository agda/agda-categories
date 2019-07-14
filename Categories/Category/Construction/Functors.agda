{-# OPTIONS --without-K --safe #-}
module Categories.Category.Construction.Functors where

-- the "Functor Category", often denoted [ C , D ]

open import Level
open import Data.Product using (Σ; _,_; _×_; uncurry′)

open import Categories.Category
open import Categories.Functor
open import Categories.Functor.Bifunctor
open import Categories.NaturalTransformation renaming (id to idN)
import Categories.Morphism.Reasoning as Mr

-- The reason the proofs below are so easy is that _∘ᵥ_ 'computes' all the way down into
-- expressions in D, from which the properties follow.
Functors : ∀ {o ℓ e o′ ℓ′ e′} → Category o ℓ e → Category o′ ℓ′ e′ → Category _ _ _
Functors C D = record
  { Obj       = Functor C D
  ; _⇒_       = NaturalTransformation
  ; _≈_       = _≃_
  ; id        = idN
  ; _∘_       = _∘ᵥ_
  ; assoc     = assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; equiv     = ≃-isEquivalence
  ; ∘-resp-≈  = λ eq eq′ → ∘-resp-≈ eq eq′
  }
  where module C = Category C
        module D = Category D
        open D

private
  variable
    o ℓ e : Level
    C D : Category o ℓ e

-- Part of the proof that Cats is a CCC:
eval : Bifunctor (Functors C D) C D
eval {C = C} {D = D} = record
  { F₀           = uncurry′ Functor.F₀
  ; F₁           = λ where
    {F , _} {_ , B} (α , f) →
      let open NaturalTransformation α
          open Functor F
      in η B ∘ F₁ f
  ; identity     = λ where
    {F , _} → elimʳ (Functor.identity F)
  ; homomorphism = λ where
    {F , _} {G , B} {_ , C} {α , f} {β , g} →
      let open NaturalTransformation
          open Functor
      in begin
        (η β C ∘ η α C) ∘ F₁ F (g C.∘ f)  ≈⟨ refl ⟩∘⟨ homomorphism F ⟩
        (η β C ∘ η α C) ∘ F₁ F g ∘ F₁ F f ≈⟨ assoc ⟩
        η β C ∘ η α C ∘ F₁ F g ∘ F₁ F f   ≈⟨ refl ⟩∘⟨ pullˡ (commute α g) ⟩
        η β C ∘ (F₁ G g ∘ η α B) ∘ F₁ F f ≈⟨ refl ⟩∘⟨ assoc ⟩
        η β C ∘ F₁ G g ∘ η α B ∘ F₁ F f   ≈˘⟨ assoc ⟩
        (η β C ∘ F₁ G g) ∘ η α B ∘ F₁ F f ∎
  ; F-resp-≈     = λ where
    {F , _} (comm , eq) → ∘-resp-≈ comm (Functor.F-resp-≈ F eq)
  }
  where module C = Category C
        module D = Category D
        open D
        open Mr D
        open HomReasoning

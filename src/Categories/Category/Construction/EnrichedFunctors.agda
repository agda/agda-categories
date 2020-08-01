{-# OPTIONS --without-K --safe #-}

open import Categories.Category using () renaming (Category to Setoid-Category)
open import Categories.Category.Monoidal

module Categories.Category.Construction.EnrichedFunctors
  {o ℓ e} {V : Setoid-Category o ℓ e} (M : Monoidal V) where

-- The (enriched) functor category for a given pair of V-enriched categories

open import Level
open import Data.Product using (_,_; uncurry′)

open import Categories.Enriched.Category M
open import Categories.Enriched.Category.Underlying M
open import Categories.Enriched.Functor M renaming (id to idF)
open import Categories.Enriched.NaturalTransformation M renaming (id to idNT)
open import Categories.Functor.Bifunctor using (Bifunctor)

import Categories.Morphism.Reasoning as MR
open NaturalTransformation using (_[_])

EnrichedFunctors : ∀ {c d} (C : Category c) (D : Category d) →
                   Setoid-Category (ℓ ⊔ e ⊔ c ⊔ d) (ℓ ⊔ e ⊔ c) (e ⊔ c)
EnrichedFunctors C D = record
  { Obj = Functor C D
  ; _⇒_ = NaturalTransformation
  ; _≈_ = λ α β → ∀ {X} → α [ X ] ≈ β [ X ]
  ; id  = idNT
  ; _∘_ = _∘ᵥ_
  ; assoc     = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv     = record
    { refl  = Equiv.refl
    ; sym   = λ α≈β → Equiv.sym α≈β
    ; trans = λ α≈β β≈γ → Equiv.trans α≈β β≈γ
    }
  ; ∘-resp-≈ = λ α₁≈β₁ α₂≈β₂ → ∘-resp-≈ α₁≈β₁ α₂≈β₂
  }
  where open Underlying D

-- Horizontal composition of natural transformations (aka the Godement
-- product) induces a composition functor over functor categories.
--
-- Note that all the equational reasoning happens in the underlying
-- (ordinary) categories!

⊚ : ∀ {c d e} {C : Category c} {D : Category d} {E : Category e} →
    Bifunctor (EnrichedFunctors D E) (EnrichedFunctors C D) (EnrichedFunctors C E)
⊚ {_} {_} {_} {_} {D} {E} = record
  { F₀ = uncurry′ _∘F_
  ; F₁ = uncurry′ _∘ₕ_
  ; identity = λ{ {F , G} {X} →
    begin
      (F $₁ D.id) ∘ E.id   ≈⟨ identityʳ ⟩
      F $₁ D.id            ≈⟨ identity F ⟩
      E.id                 ∎ }
  ; homomorphism = λ{ {_ , F₂} {G₁ , G₂} {H₁ , _} {α₁ , α₂} {β₁ , β₂} {X} →
    begin
      H₁ $₁ (β₂ [ X ] D.∘ α₂ [ X ]) ∘ β₁ [ F₂ $₀ X ] ∘ α₁ [ F₂ $₀ X ]
    ≈⟨ homomorphism H₁ ⟩∘⟨refl ⟩
      (H₁ $₁ β₂ [ X ] ∘ H₁ $₁ α₂ [ X ]) ∘ β₁ [ F₂ $₀ X ] ∘ α₁ [ F₂ $₀ X ]
    ≈⟨ center (⟺ (commute β₁ (α₂ [ X ]))) ⟩
      (H₁ $₁ β₂ [ X ] ∘ (β₁ [ G₂ $₀ X ] ∘ G₁ $₁ α₂ [ X ]) ∘ α₁ [ F₂ $₀ X ])
    ≈⟨ pull-first refl ⟩
      (H₁ $₁ β₂ [ X ] ∘ β₁ [ G₂ $₀ X ]) ∘ G₁ $₁ α₂ [ X ] ∘ α₁ [ F₂ $₀ X ]
    ∎ }
  ; F-resp-≈ = λ{ {_} {F , _} (eq₁ , eq₂) → ∘-resp-≈ (F-resp-≈ F eq₂) eq₁ }
  }
  where
    module D = Underlying D
    module E = Underlying E
    open E hiding (id)
    open MR (Underlying E)
    open HomReasoning
    open Equiv using (refl)
    open UnderlyingFunctor hiding (F₀; F₁)
    open UnderlyingNT

    -- Aliases used to shorten some proof expressions

    infixr 14 _$₀_ _$₁_
    _$₀_ = UnderlyingFunctor.F₀
    _$₁_ = UnderlyingFunctor.F₁

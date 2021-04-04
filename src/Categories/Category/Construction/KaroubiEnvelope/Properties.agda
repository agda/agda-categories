{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core

module Categories.Category.Construction.KaroubiEnvelope.Properties {o ℓ e} (𝒞 : Category o ℓ e) where

open import Data.Product using (_,_)

open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Properties

open import Categories.Category.Construction.KaroubiEnvelope

open import Categories.Morphism.Idempotent

open Category 𝒞
open Equiv

--------------------------------------------------------------------------------
-- Some facts about embedding 𝒞 into it's Karoubi Envelope

KaroubiEmbedding : Functor 𝒞 (KaroubiEnvelope 𝒞)
KaroubiEmbedding = record
  { F₀ = λ X → record
    { obj = X
    ; isIdempotent = record
      { idem = id
      ; idempotent = identity²
      }
    }
  ; F₁ = λ f → record
    { hom = f
    ; absorbˡ = identityˡ
    ; absorbʳ = identityʳ
    }
  ; identity = refl
  ; homomorphism = refl
  ; F-resp-≈ = λ eq → eq
  }

private
  module KaroubiEmbedding = Functor KaroubiEmbedding

karoubi-embedding-full : Full KaroubiEmbedding
karoubi-embedding-full = record
  { from = record
    { _⟨$⟩_ = λ f → Idempotent⇒.hom f
    ; cong = λ eq → eq
    }
  ; right-inverse-of = λ _ → refl
  }

karoubi-embedding-faithful : Faithful KaroubiEmbedding
karoubi-embedding-faithful f g eq = eq

karoubi-embedding-fully-faithful : FullyFaithful KaroubiEmbedding
karoubi-embedding-fully-faithful = karoubi-embedding-full , karoubi-embedding-faithful

--------------------------------------------------------------------------------
-- Some facts about splitting idempotents

-- All idempotents in the Karoubi Envelope are split
idempotent-split : ∀ {A} → Idempotent (KaroubiEnvelope 𝒞) A → SplitIdempotent (KaroubiEnvelope 𝒞) A
idempotent-split {A} I = record
  { idem = idem
  ; isSplitIdempotent = record
    { obj = record
      { isIdempotent = record
        { idem = idem.hom
        ; idempotent = idempotent
        }
      }
    ; retract = record
      { hom = idem.hom
      ; absorbˡ = idempotent
      ; absorbʳ = idem.absorbʳ
      }
    ; section = record
      { hom = idem.hom
      ; absorbˡ = idem.absorbˡ
      ; absorbʳ = idempotent
      }
    ; retracts = idempotent
    ; splits = idempotent
    }
  }
  where
    module A = BundledIdempotent A
    open Idempotent I
    module idem = Idempotent⇒ idem

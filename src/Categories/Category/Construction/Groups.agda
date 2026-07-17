{-# OPTIONS --safe --without-K #-}

-- The category of group objects with a cartesian category

open import Categories.Category
open import Categories.Category.Cartesian

module Categories.Category.Construction.Groups {o ℓ e} {𝒞 : Category o ℓ e} (C : Cartesian 𝒞) where

open import Level

open import Categories.Category.BinaryProducts 𝒞
open import Categories.Morphism.Reasoning 𝒞
open import Categories.Object.Group C
open import Categories.Object.Product.Morphisms 𝒞

open Category 𝒞
open Cartesian C

open Equiv
open HomReasoning
open Group using (μ)
open Group⇒

Groups : Category (o ⊔ ℓ ⊔ e) (ℓ ⊔ e) e
Groups = record
  { Obj = Group
  ; _⇒_ = Group⇒
  ; _≈_ = λ f g → arr f ≈ arr g
  ; id = record
    { arr = id
    ; preserves-μ = identityˡ ○ introʳ (id×id product)
    ; preserves-η = identityˡ
    ; preserves-ι = id-comm-sym
    }
  ; _∘_ = λ f g → record
    { arr = arr f ∘ arr g
    ; preserves-μ = glue (preserves-μ f) (preserves-μ g) ○ ∘-resp-≈ʳ ×₁∘×₁
    ; preserves-η = glueTrianglesˡ (preserves-η f) (preserves-η g)
    ; preserves-ι = glue (preserves-ι f) (preserves-ι g)
    }
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv = record
    { refl = refl
    ; sym = sym
    ; trans = trans
    }
  ; ∘-resp-≈ = ∘-resp-≈
  }

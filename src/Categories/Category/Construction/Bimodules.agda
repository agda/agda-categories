{-# OPTIONS --without-K --safe #-}

open import Categories.Bicategory

module Categories.Category.Construction.Bimodules {o ℓ e t} {𝒞 : Bicategory o ℓ e t} where

open import Level
open import Categories.Category
open import Categories.Bicategory.Monad
open import Categories.Bicategory.Monad.Bimodule
open import Categories.Bicategory.Monad.Bimodule.Homomorphism
import Categories.Bicategory.Extras as Bicat
open Bicat 𝒞

Bimodules : Monad 𝒞 → Monad 𝒞 → Category (o ⊔ ℓ ⊔ e) (ℓ ⊔ e) e
Bimodules M₁ M₂  = record
  { Obj = Bimodule M₁ M₂
  ; _⇒_ = λ B₁ B₂ → Bimodulehomomorphism B₁ B₂
  ; _≈_ = λ h₁ h₂ → α h₁ ≈ α h₂
  ; id = id-bimodule-hom
  ; _∘_ = bimodule-hom-∘
  ; assoc = assoc₂
  ; sym-assoc = sym-assoc₂
  ; identityˡ = identity₂ˡ
  ; identityʳ = identity₂ʳ
  ; identity² = identity₂²
  ; equiv = record
    { refl = hom.Equiv.refl
    ; sym = hom.Equiv.sym
    ; trans = hom.Equiv.trans
    }
  ; ∘-resp-≈ = hom.∘-resp-≈
  }
  where
    open Bimodulehomomorphism using (α)

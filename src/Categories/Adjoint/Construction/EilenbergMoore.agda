{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core
open import Categories.Monad

module Categories.Adjoint.Construction.EilenbergMoore {o ℓ e} {C : Category o ℓ e} (M : Monad C) where

open import Categories.Category.Construction.EilenbergMoore M
open import Categories.Adjoint
open import Categories.Functor
open import Categories.Functor.Properties
open import Categories.NaturalTransformation.Core
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_)
open import Categories.Morphism.Reasoning C

private
  module C = Category C
  module M = Monad M
  open M.F
  open C
  open HomReasoning
  open Equiv

Forgetful : Functor EilenbergMoore C
Forgetful = record
  { F₀           = Module.A
  ; F₁           = Module⇒.arr
  ; identity     = refl
  ; homomorphism = refl
  ; F-resp-≈     = λ eq → eq
  }

Free : Functor C EilenbergMoore
Free = record
  { F₀           = λ A → record
    { A        = F₀ A
    ; action   = M.μ.η A
    ; commute  = M.assoc
    ; identity = M.identityʳ
    }
  ; F₁           = λ f → record
    { arr     = F₁ f
    ; commute = ⟺ (M.μ.commute f)
    }
  ; identity     = identity
  ; homomorphism = homomorphism
  ; F-resp-≈     = F-resp-≈
  }

FF≃F : Forgetful ∘F Free ≃ M.F
FF≃F = record
  { F⇒G = record
    { η           = λ _ → F₁ C.id
    ; commute     = λ _ → [ M.F ]-resp-square id-comm-sym
    ; sym-commute = λ _ → [ M.F ]-resp-square id-comm
    }
  ; F⇐G = record
    { η       = λ _ → F₁ C.id
    ; commute = λ _ → [ M.F ]-resp-square id-comm-sym
    ; sym-commute = λ _ → [ M.F ]-resp-square id-comm
    }
  ; iso = λ _ → record
    { isoˡ = elimˡ identity ○ identity
    ; isoʳ = elimˡ identity ○ identity
    }
  }

Free⊣Forgetful : Free ⊣ Forgetful
Free⊣Forgetful = record
  { unit   = record
    { η           = M.η.η
    ; commute     = M.η.commute
    ; sym-commute = M.η.sym-commute
    }
  ; counit = record
    { η           = λ X →
      let module X = Module X
      in record
        { arr     = X.action
        ; commute = ⟺ X.commute
        }
    ; commute     = λ f → ⟺ (Module⇒.commute f)
    ; sym-commute = Module⇒.commute
    }
  ; zig    = M.identityˡ
  ; zag    = λ {B} → Module.identity B
  }

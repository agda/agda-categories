{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core
open import Categories.Comonad

-- verbatim dual of Categories.Adjoint.Construction.EilenbergMoore
module Categories.Adjoint.Construction.CoEilenbergMoore {o ℓ e} {C : Category o ℓ e} (M : Comonad C) where

open import Categories.Category.Construction.CoEilenbergMoore M
open import Categories.Adjoint
open import Categories.Functor
open import Categories.Functor.Properties
open import Categories.NaturalTransformation.Core
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_)
open import Categories.Morphism.Reasoning C

private
  module C = Category C
  module M = Comonad M
  open M.F
  open C
  open HomReasoning
  open Equiv

Forgetful : Functor CoEilenbergMoore C
Forgetful = record
  { F₀           = Comodule.A
  ; F₁           = Comodule⇒.arr
  ; identity     = refl
  ; homomorphism = refl
  ; F-resp-≈     = λ eq → eq
  }

Cofree : Functor C CoEilenbergMoore
Cofree = {!   !}
{-
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
-}
UC≃M : Forgetful ∘F Cofree ≃ M.F
UC≃M = {!   !}
{-
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
-}

Free⊣Forgetful : Cofree ⊣ Forgetful
Free⊣Forgetful = {!   !}
{-
  { unit   = record
    { η           = M.η.η
    ; commute     = M.η.commute
    ; sym-commute = M.η.sym-commute
    }
  ; counit = record
    { η           = λ X →
      let module X = Comodule X
      in record
        { arr     = X.action
        ; commute = ⟺ X.commute
        }
    ; commute     = λ f → ⟺ (Comodule⇒.commute f)
    ; sym-commute = Comodule⇒.commute
    }
  ; zig    = M.identityˡ
  ; zag    = λ {B} → Comodule.identity B
  }
-}
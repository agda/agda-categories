{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core
open import Categories.Comonad

-- verbatim dual of Categories.Adjoint.Construction.EilenbergMoore
module Categories.Adjoint.Construction.CoEilenbergMoore {o ℓ e} {C : Category o ℓ e} (M : Comonad C) where

open import Categories.Category.Construction.CoEilenbergMoore M
open import Categories.Adjoint
open import Categories.Functor
open import Categories.Functor.Properties
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)
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
Cofree = record
 { F₀ = λ A → record
  { A = F₀ A
  ; coaction = M.δ.η A
  ; commute = sym M.assoc
  ; identity = Comonad.identityʳ M
  }
 ; F₁ = λ f → record
  { arr = F₁ f
  ; commute = ⟺ (sym (M.δ.commute f))
  }
 ; identity = identity
 ; homomorphism = homomorphism
 ; F-resp-≈ = F-resp-≈
 }

UC≃M : Forgetful ∘F Cofree ≃ M.F
UC≃M = niHelper (record
 { η = λ _ → F₁ C.id
 ; η⁻¹ = λ _ → F₁ C.id
 ; commute = λ f → [ M.F ]-resp-square id-comm-sym
 ; iso = λ _ → record
    { isoˡ = elimˡ identity ○ identity
    ; isoʳ = elimˡ identity ○ identity
    }
 })

Forgetful⊣Cofree : Forgetful ⊣ Cofree
Forgetful⊣Cofree = record
 { unit = record
  { η = λ X → let module X = Comodule X
      in record
        { arr     = X.coaction
        ; commute = ⟺ X.commute
        }
  ; commute = Comodule⇒.commute
  ; sym-commute = λ f → ⟺ (Comodule⇒.commute f)
  }
 ; counit = record
  { η = M.ε.η
  ; commute = M.ε.commute
  ; sym-commute = M.ε.sym-commute
  }
 ; zig = λ {A} → Comodule.identity A
 ; zag = λ {B} → Comonad.identityˡ M
 }
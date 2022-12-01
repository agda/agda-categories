{-# OPTIONS --without-K --safe #-}
module Categories.Category.Construction.μ-Bialgebras where

open import Level
open import Function using (_$_)

open import Categories.Category
open import Categories.Functor hiding (id)
open import Categories.Functor.Algebra
open import Categories.Functor.Coalgebra
import Categories.Morphism.Reasoning as MR
open import Categories.Functor.Bialgebra
open import Categories.Category.Construction.F-Algebras
open import Categories.Category.Construction.F-Coalgebras

private
  variable
    o ℓ e : Level
    C : Category o ℓ e

μ-Bialgebras : {C : Category o ℓ e} → (T : Endofunctor C) → (F : Endofunctor C) → (Distr-law T F) → Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) e
μ-Bialgebras {C = C} T F μ = record
 { Obj       = μ-Bialgebra T F μ
 ; _⇒_       = μ-Bialgebra-Morphism
 ; _≈_       = λ β₁ β₂ → f β₁ ≈ f β₂
 ; _∘_       = λ β₁ β₂ → record
   { f                = f β₁ ∘ f β₂
   ; f-is-alg-morph   =
     F-Algebra-Morphism.commutes $
       (alg-morph β₁) T-Algebras.∘ (alg-morph β₂)
   ; f-is-coalg-morph = F-Coalgebra-Morphism.commutes $
     (coalg-morph β₁) F-Coalgebras.∘ (coalg-morph β₂)
   }
 ; id        = record
   { f = id
   ; f-is-alg-morph   =  F-Algebra-Morphism.commutes (T-Algebras.id)
   ; f-is-coalg-morph =  F-Coalgebra-Morphism.commutes (F-Coalgebras.id)
   }
 ; assoc     = assoc
 ; sym-assoc = sym-assoc
 ; identityˡ = identityˡ
 ; identityʳ = identityʳ
 ; identity² = identity²
 ; equiv     = record
   { refl  = refl
   ; sym   = sym
   ; trans = trans
   }
 ; ∘-resp-≈  = ∘-resp-≈
 }
   where
    open Category C
    open MR C
    open HomReasoning
    open Equiv
    open μ-Bialgebra-Morphism
    open μ-Bialgebra
    module T-Algebras = Category (F-Algebras T)
    module F-Coalgebras = Category (F-Coalgebras F)
    open Functor F
    open F-Coalgebra-Morphism
    open F-Coalgebra


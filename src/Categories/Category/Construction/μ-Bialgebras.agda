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
       T-Algebras._∘_ (alg-morph β₁) (alg-morph β₂)
   ; f-is-coalg-morph = commut (coalg-morph β₁) (coalg-morph β₂)
   }
 ; id        = record
   { f = id
   ; f-is-alg-morph   =  F-Algebra-Morphism.commutes (T-Algebras.id)
   ; f-is-coalg-morph = ⟺ id-comm-sym ○ (∘-resp-≈ˡ (⟺ identity))
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
    open Functor F
    open F-Coalgebra-Morphism
    open F-Coalgebra
    commut : {A B C : F-Coalgebra F} (α₁ : F-Coalgebra-Morphism B C) (α₂ : F-Coalgebra-Morphism A B) →
      α C ∘ (f α₁ ∘ f α₂) ≈  F₁ (f α₁ ∘ f α₂) ∘ α A
    commut {A} {B} {C} α₁ α₂ = begin
      α C ∘ (f α₁ ∘ f α₂) ≈⟨ pullˡ (commutes α₁) ⟩
      (F₁ (f α₁) ∘ α B) ∘ f α₂ ≈⟨ pullʳ (commutes α₂)⟩
      F₁ (f α₁) ∘ F₁ (f α₂) ∘ α A
      ≈⟨ pullˡ (⟺ homomorphism) ⟩
      F₁ (f α₁ ∘ f α₂) ∘ α A  ∎


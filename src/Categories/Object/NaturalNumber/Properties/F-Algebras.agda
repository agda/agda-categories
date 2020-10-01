{-# OPTIONS --without-K --safe #-}
module Categories.Object.NaturalNumber.Properties.F-Algebras where

open import Level
open import Function using (_$_)

open import Categories.Category
open import Categories.Category.Construction.F-Algebras
open import Categories.Category.Cocartesian
open import Categories.Functor
open import Categories.Functor.Algebra
open import Categories.Object.Terminal renaming (up-to-iso to ⊤-up-to-iso)
open import Categories.Object.Initial

import Categories.Morphism.Reasoning as MR
import Categories.Object.NaturalNumber as NNO

-- A NNO is an inital algebra for the 'X ↦ ⊤ + X' endofunctor.
module _ {o ℓ e} (𝒞 : Category o ℓ e) (𝒞-Terminal : Terminal 𝒞) (𝒞-Coproducts : BinaryCoproducts 𝒞) where

  open Terminal 𝒞-Terminal
  open BinaryCoproducts 𝒞-Coproducts
  open Category 𝒞
  open HomReasoning
  open Equiv
  open MR 𝒞
  open NNO 𝒞 𝒞-Terminal
  
  Maybe : Functor 𝒞 𝒞
  Maybe = record
    { F₀ = λ X → ⊤ + X
    ; F₁ = λ f → [ i₁ , i₂ ∘ f ]
    ; identity = []-cong₂ refl identityʳ ○ +-η 
    ; homomorphism = +-unique (pullʳ inject₁ ○ inject₁) (pullʳ inject₂ ○ pullˡ inject₂ ○ assoc)
    ; F-resp-≈ = λ eq → []-cong₂ refl (∘-resp-≈ʳ eq)
    }

  private
    module Maybe = Functor Maybe

  Initial⇒NNO : Initial (F-Algebras Maybe) → NaturalNumber
  Initial⇒NNO initial = record
    { N = ⊥.A
    ; z = ⊥.α ∘ i₁
    ; s = ⊥.α ∘ i₂
    ; universal = λ {A} q f →
      F-Algebra-Morphism.f (initial.! {A = alg q f})
    ; z-commute = λ {A} {q} {f} → begin
      q                                                                 ≈⟨ ⟺ inject₁ ⟩
      [ q , f ] ∘ i₁                                                    ≈⟨ pushʳ (⟺ inject₁) ⟩
      (([ q , f ] ∘ [ i₁ , i₂ ∘ F-Algebra-Morphism.f initial.! ]) ∘ i₁) ≈⟨ pushˡ (⟺ (F-Algebra-Morphism.commutes (initial.! {A = alg q f}))) ⟩
      F-Algebra-Morphism.f initial.! ∘ ⊥.α ∘ i₁                         ∎
    ; s-commute = λ {A} {q} {f} → begin
      (f ∘ F-Algebra-Morphism.f initial.!) ≈⟨ pushˡ (⟺ inject₂) ⟩
      [ q , f ] ∘ i₂ ∘ F-Algebra-Morphism.f initial.!                 ≈⟨ pushʳ (⟺ inject₂) ⟩
      ([ q , f ] ∘ [ i₁ , i₂ ∘ F-Algebra-Morphism.f initial.! ]) ∘ i₂ ≈⟨ pushˡ (⟺ (F-Algebra-Morphism.commutes (initial.! {A = alg q f}))) ⟩
      F-Algebra-Morphism.f initial.! ∘ ⊥.α ∘ i₂                       ∎
    ; unique = λ {A} {f} {q} {u} eqᶻ eqˢ → ⟺ $ initial.!-unique record
        { f = u
        ; commutes = begin
          u ∘ ⊥.α ≈⟨ ⟺ +-g-η ⟩
          [ (u ∘ ⊥.α) ∘ i₁ , (u ∘ ⊥.α) ∘ i₂ ] ≈⟨ []-cong₂ (assoc ○ ⟺ eqᶻ) (assoc ○ ⟺ eqˢ) ⟩
          [ f , q ∘ u ]                       ≈⟨ +-unique (pullʳ inject₁ ○ inject₁) (pullʳ inject₂ ○ pullˡ inject₂) ⟩
          [ f , q ] ∘ [ i₁ , i₂ ∘ u ]         ∎
        }
    }
    where
      module initial = Initial initial
      module ⊥ = F-Algebra initial.⊥
  
      alg : ∀ {A} → (q : ⊤ ⇒ A) → (f : A ⇒ A) → F-Algebra Maybe
      alg {A} q f = record
        { A = A
        ; α = [ q , f ]
        }

  NNO⇒Initial : NaturalNumber → Initial (F-Algebras Maybe)
  NNO⇒Initial NNO = record
    { ⊥ = record
      { A = N 
      ; α = [ z , s ]
      }
    ; ⊥-is-initial = record
      { ! = λ {alg} → record
        { f = universal (F-Algebra.α alg ∘ i₁) (F-Algebra.α alg ∘ i₂)
        ; commutes = begin
          universal _ _ ∘ [ z , s ]                                         ≈⟨ ∘-distribˡ-[] ⟩
          [ universal _ _ ∘ z , universal _ _ ∘ s ]                         ≈⟨ []-cong₂ (⟺ z-commute) (⟺ s-commute ○ assoc) ⟩
          [ F-Algebra.α alg ∘ i₁ , F-Algebra.α alg ∘ (i₂ ∘ universal _ _) ] ≈˘⟨ ∘-distribˡ-[] ⟩
          F-Algebra.α alg ∘ [ i₁ , i₂ ∘ universal _ _ ]                   ∎
        }
      ; !-unique = λ {A} f →
        let z-commutes = begin
              F-Algebra.α A ∘ i₁                                          ≈⟨ pushʳ (⟺ inject₁) ⟩
              (F-Algebra.α A ∘ [ i₁ , i₂ ∘ F-Algebra-Morphism.f f ]) ∘ i₁ ≈˘⟨ F-Algebra-Morphism.commutes f ⟩∘⟨refl ⟩
              (F-Algebra-Morphism.f f ∘ [ z , s ]) ∘ i₁                   ≈⟨ pullʳ inject₁ ⟩
              F-Algebra-Morphism.f f ∘ z                                  ∎
            s-commutes = begin
              (F-Algebra.α A ∘ i₂) ∘ F-Algebra-Morphism.f f               ≈⟨ pullʳ (⟺ inject₂) ○ ⟺ assoc ⟩
              (F-Algebra.α A ∘ [ i₁ , i₂ ∘ F-Algebra-Morphism.f f ]) ∘ i₂ ≈˘⟨ F-Algebra-Morphism.commutes f ⟩∘⟨refl ⟩
              (F-Algebra-Morphism.f f ∘ [ z , s ]) ∘ i₂                   ≈⟨ pullʳ inject₂ ⟩
              F-Algebra-Morphism.f f ∘ s                                  ∎
        in ⟺ $ unique z-commutes s-commutes
      }
    }
    where
      open NaturalNumber NNO

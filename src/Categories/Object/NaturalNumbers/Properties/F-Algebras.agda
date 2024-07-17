{-# OPTIONS --without-K --safe #-}

open import Level
open import Categories.Category.Core
open import Categories.Object.Terminal using (Terminal)
open import Categories.Category.Cocartesian using (BinaryCoproducts)

-- A NNO is an inital algebra for the 'X ↦ ⊤ + X' endofunctor.
module Categories.Object.NaturalNumbers.Properties.F-Algebras {o ℓ e} (𝒞 : Category o ℓ e) (𝒞-Terminal : Terminal 𝒞) (𝒞-Coproducts : BinaryCoproducts 𝒞) where

open import Function using (_$_)

open import Categories.Category.Construction.F-Algebras using (F-Algebras)
open import Categories.Functor.Algebra using (F-Algebra; F-Algebra-Morphism)
open import Categories.Object.Initial using (Initial; IsInitial)

import Categories.Morphism.Reasoning as MR

open Terminal 𝒞-Terminal
open BinaryCoproducts 𝒞-Coproducts
open Category 𝒞
open HomReasoning
open Equiv
open MR 𝒞

open import Categories.Object.NaturalNumbers 𝒞 𝒞-Terminal

Initial⇒NNO : Initial (F-Algebras (⊤ +-)) → NNO
Initial⇒NNO initial = record
  { N = ⊥.A
  ; isNNO = record
    { z = ⊥.α ∘ i₁
    ; s = ⊥.α ∘ i₂
    ; universal = λ {A} q f →
      F-Algebra-Morphism.f (initial.! {A = alg q f})
    ; z-commute = λ {A} {q} {f} → begin 
      q                                                       ≈˘⟨ inject₁ ⟩ 
      [ q , f ] ∘ i₁                                          ≈˘⟨ refl⟩∘⟨ (+₁∘i₁ ○ identityʳ) ⟩ 
      [ q , f ] ∘ (id +₁ F-Algebra-Morphism.f initial.!) ∘ i₁ ≈˘⟨ extendʳ (F-Algebra-Morphism.commutes (initial.! {A = alg q f})) ⟩ 
      F-Algebra-Morphism.f initial.! ∘ ⊥.α ∘ i₁               ∎
    ; s-commute = λ {A} {q} {f} → begin 
      f ∘ F-Algebra-Morphism.f initial.!                      ≈˘⟨ pullˡ inject₂ ⟩ 
      [ q , f ] ∘ i₂ ∘ F-Algebra-Morphism.f initial.!         ≈˘⟨ refl⟩∘⟨ +₁∘i₂ ⟩ 
      [ q , f ] ∘ (id +₁ F-Algebra-Morphism.f initial.!) ∘ i₂ ≈˘⟨ extendʳ $ F-Algebra-Morphism.commutes (initial.! {A = alg q f}) ⟩ 
      F-Algebra-Morphism.f initial.! ∘ ⊥.α ∘ i₂               ∎
    ; unique = λ {A} {f} {q} {u} eqᶻ eqˢ → ⟺ $ initial.!-unique $ record 
      { f = u 
      ; commutes = begin 
        u ∘ ⊥.α                             ≈˘⟨ +-g-η ⟩ 
        [ (u ∘ ⊥.α) ∘ i₁ , (u ∘ ⊥.α) ∘ i₂ ] ≈˘⟨ []-cong₂ (eqᶻ ○ sym-assoc) (eqˢ ○ sym-assoc) ⟩ 
        [ f , q ∘ u ]                       ≈˘⟨ []∘+₁ ○ []-cong₂ identityʳ refl ⟩ 
        [ f , q ] ∘ (id +₁ u)               ∎ 
      }
    }
  }
  where
    module initial = Initial initial
    module ⊥ = F-Algebra initial.⊥

    alg : ∀ {A} → (q : ⊤ ⇒ A) → (f : A ⇒ A) → F-Algebra (⊤ +-)
    alg {A} q f = record
      { A = A
      ; α = [ q , f ]
      }

NNO⇒Initial : NNO → Initial (F-Algebras (⊤ +-))
NNO⇒Initial nno = record
  { ⊥ = record
    { A = N 
    ; α = [ z , s ]
    }
  ; ⊥-is-initial = record
    { ! = λ {alg} → record
      { f = universal (F-Algebra.α alg ∘ i₁) (F-Algebra.α alg ∘ i₂)
      ; commutes = begin 
        universal (F-Algebra.α alg ∘ i₁) (F-Algebra.α alg ∘ i₂) ∘ [ z , s ]                                         ≈⟨ ∘[] ⟩ 
        [ universal (F-Algebra.α alg ∘ i₁) (F-Algebra.α alg ∘ i₂) ∘ z 
        , universal (F-Algebra.α alg ∘ i₁) (F-Algebra.α alg ∘ i₂) ∘ s ]                                             ≈˘⟨ []-cong₂ z-commute (sym-assoc ○ s-commute) ⟩ 
        [ F-Algebra.α alg ∘ i₁ , F-Algebra.α alg ∘ (i₂ ∘ universal (F-Algebra.α alg ∘ i₁) (F-Algebra.α alg ∘ i₂)) ] ≈˘⟨ ∘[] ○ []-cong₂ (∘-resp-≈ʳ identityʳ) refl ⟩ 
        F-Algebra.α alg ∘ (id +₁ universal (F-Algebra.α alg ∘ i₁) (F-Algebra.α alg ∘ i₂))                           ∎
      }
    ; !-unique = λ {A} f →
      let z-commutes = begin
            F-Algebra.α A ∘ i₁                                  ≈˘⟨ refl⟩∘⟨ (+₁∘i₁ ○ identityʳ) ⟩ 
            F-Algebra.α A ∘ (id +₁ F-Algebra-Morphism.f f) ∘ i₁ ≈˘⟨ extendʳ (F-Algebra-Morphism.commutes f) ⟩ 
            F-Algebra-Morphism.f f ∘ [ z , s ] ∘ i₁             ≈⟨ refl⟩∘⟨ inject₁ ⟩ 
            F-Algebra-Morphism.f f ∘ z                          ∎
          s-commutes = begin 
            (F-Algebra.α A ∘ i₂) ∘ F-Algebra-Morphism.f f       ≈⟨ pullʳ $ ⟺ inject₂ ⟩ 
            F-Algebra.α A ∘ (id +₁ F-Algebra-Morphism.f f) ∘ i₂ ≈˘⟨ pushˡ (F-Algebra-Morphism.commutes f) ⟩ 
            (F-Algebra-Morphism.f f ∘ [ z , s ]) ∘ i₂           ≈⟨ pullʳ inject₂ ⟩ 
            F-Algebra-Morphism.f f ∘ s                          ∎ 
      in ⟺ $ unique z-commutes s-commutes
    }
  }
  where
    open NNO nno

{-# OPTIONS --without-K --safe #-}
module Categories.Category.Construction.Properties.EilenbergMoore where

open import Level
import Relation.Binary.PropositionalEquality as ≡

open import Categories.Adjoint
open import Categories.Adjoint.Properties
open import Categories.Category
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Equivalence
open import Categories.Monad

open import Categories.NaturalTransformation renaming (id to idN)

open import Categories.Adjoint.Construction.EilenbergMoore
open import Categories.Category.Construction.EilenbergMoore

private
  variable
    o ℓ e : Level
    𝒞 𝒟 : Category o ℓ e

open NaturalTransformation

module _ {F : Functor 𝒞 𝒟} {G : Functor 𝒟 𝒞} (adjoint : Adjoint F G) where
  T : Monad 𝒞
  T = adjoint⇒monad adjoint

  𝒞ᵀ : Category _ _ _
  𝒞ᵀ = EilenbergMoore T

  module 𝒞 = Category 𝒞
  module 𝒟 = Category 𝒟
  module 𝒞ᵀ = Category 𝒞ᵀ

  module T = Monad T
  module F = Functor F
  module G = Functor G

  open Adjoint adjoint

  open Functor F
  open Functor G renaming (F₀ to G₀; F₁ to G₁)
  open Functor T.F renaming (F₀ to T₀; F₁ to T₁)

  -- Maclane's Comparison Functor
  K : Functor 𝒟 𝒞ᵀ
  K = record
    { F₀ = λ X → record
      { A = G₀ X
      ; action = G₁ (counit.η X)
      ; commute = commute (G ∘ˡ counit) (counit.η X)
      ; identity = zag
      }
    ; F₁ = λ {A} {B} f → record
      { arr = G₁ f
      ; commute =  begin
        𝒞 [ G₁ f ∘ G₁ (counit.η A) ]           ≈˘⟨ G.homomorphism ⟩
        G₁ (𝒟 [ f ∘ (counit.η A) ])            ≈˘⟨ G.F-resp-≈ (counit.commute f) ⟩
        G₁ (𝒟 [ counit.η B ∘ F₁ (G₁ f) ])      ≈⟨ G.homomorphism  ⟩
        𝒞 [ G₁ (counit.η B) ∘ G₁ (F₁ (G₁ f)) ] ∎
      }
    ; identity = G.identity
    ; homomorphism = G.homomorphism
    ; F-resp-≈ = G.F-resp-≈
    }
    where
      open 𝒞.HomReasoning

  open Functor K renaming (F₀ to K₀; F₁ to K₁)
  open Functor (Free T) renaming (F₀ to Free₀; F₁ to Free₁)
  open Functor (Forgetful T) renaming (F₀ to Forgetful₀; F₁ to Forgetful₁)

  K∘F≡Free : (K ∘F F) ≡F Free T
  K∘F≡Free = record
    { eq₀ = λ X → ≡.refl
    ; eq₁ = λ {A} {B} f → begin
      Module⇒.arr (𝒞ᵀ [ (hid ≡.refl) ∘ K₁ (F₁ f) ]) ≈⟨ hid-refl {A = K₀ (F₀ B)} ⟩∘⟨refl ⟩
      Module⇒.arr (𝒞ᵀ [ 𝒞ᵀ.id ∘ K₁ (F₁ f) ])       ≈⟨ 𝒞.identityˡ {f = Module⇒.arr (K₁ (F₁ f))} ⟩
      Module⇒.arr (K₁ (F₁ f))                       ≈⟨ refl ⟩
      Module⇒.arr (Free₁ f)                         ≈˘⟨ 𝒞ᵀ.identityʳ {f = Free₁ f} ⟩
      Module⇒.arr (𝒞ᵀ [ Free₁ f ∘ 𝒞ᵀ.id ])         ≈˘⟨ refl⟩∘⟨ hid-refl {A = Free₀ A} ⟩
      Module⇒.arr (𝒞ᵀ [ Free₁ f ∘ (hid ≡.refl) ])   ∎
    }
    where
      open 𝒞.HomReasoning
      open import Categories.Morphism.HeterogeneousIdentity 𝒞ᵀ

  Forgetful∘K≡U : (Forgetful T ∘F K) ≡F G
  Forgetful∘K≡U = record
    { eq₀ = λ X → ≡.refl
    ; eq₁ = λ f → begin
      𝒞 [ (hid ≡.refl) ∘ (Forgetful₁ (K₁ f)) ] ≈⟨ hid-refl ⟩∘⟨refl ⟩
      𝒞 [ 𝒞.id ∘ (Forgetful₁ (K₁ f)) ]        ≈⟨ 𝒞.identityˡ ⟩
      (Forgetful₁ (K₁ f))                      ≈⟨ refl ⟩
      G₁ f                                     ≈˘⟨ 𝒞.identityʳ ⟩
      𝒞 [ G₁ f ∘ 𝒞.id ]                       ≈˘⟨ refl⟩∘⟨ hid-refl ⟩
      𝒞 [ G₁ f ∘ (hid ≡.refl) ]                ∎
    }
    where
      open 𝒞.HomReasoning
      open import Categories.Morphism.HeterogeneousIdentity 𝒞

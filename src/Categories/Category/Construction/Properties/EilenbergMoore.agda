{-# OPTIONS --without-K --safe #-}
module Categories.Category.Construction.Properties.EilenbergMoore where

open import Level
import Relation.Binary.PropositionalEquality.Core as ≡

open import Categories.Adjoint
open import Categories.Adjoint.Properties
open import Categories.Category
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Equivalence
open import Categories.Monad

open import Categories.NaturalTransformation.Core renaming (id to idN)
open import Categories.Morphism.HeterogeneousIdentity

open import Categories.Adjoint.Construction.EilenbergMoore
open import Categories.Category.Construction.EilenbergMoore

private
  variable
    o ℓ e : Level
    𝒞 𝒟 : Category o ℓ e

module _ {F : Functor 𝒞 𝒟} {G : Functor 𝒟 𝒞} (F⊣G : Adjoint F G) where
  private
    T : Monad 𝒞
    T = adjoint⇒monad F⊣G

    𝒞ᵀ : Category _ _ _
    𝒞ᵀ = EilenbergMoore T

    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟
    module 𝒞ᵀ = Category 𝒞ᵀ

    open 𝒞.HomReasoning

    module T = Monad T
    module F = Functor F
    module G = Functor G

    open Adjoint F⊣G
    open NaturalTransformation

  -- Maclane's Comparison Functor
  ComparisonF : Functor 𝒟 𝒞ᵀ
  ComparisonF = record
    { F₀ = λ X → record
      { A = G.F₀ X
      ; action = G.F₁ (counit.η X)
      ; commute = commute (G ∘ˡ counit) (counit.η X)
      ; identity = zag
      }
    ; F₁ = λ {A} {B} f → record
      { arr = G.F₁ f
      ; commute =  begin
        𝒞 [ G.F₁ f ∘ G.F₁ (counit.η A) ]               ≈˘⟨ G.homomorphism ⟩
        G.F₁ (𝒟 [ f ∘ (counit.η A) ])                  ≈˘⟨ G.F-resp-≈ (counit.commute f) ⟩
        G.F₁ (𝒟 [ counit.η B ∘ F.F₁ (G.F₁ f) ])        ≈⟨ G.homomorphism  ⟩
        𝒞 [ G.F₁ (counit.η B) ∘ G.F₁ (F.F₁ (G.F₁ f)) ] ∎
      }
    ; identity = G.identity
    ; homomorphism = G.homomorphism
    ; F-resp-≈ = G.F-resp-≈
    }

  private
    K = ComparisonF
    module K = Functor K
    module Gᵀ = Functor (Forgetful T)
    module Fᵀ = Functor (Free T)

  Comparison∘F≡Free : (ComparisonF ∘F F) ≡F Free T
  Comparison∘F≡Free = record
    { eq₀ = λ X → ≡.refl
    ; eq₁ = λ {A} {B} f → begin
      Module⇒.arr (𝒞ᵀ [ (hid 𝒞ᵀ ≡.refl) ∘ K.F₁ (F.F₁ f) ]) ≈⟨ hid-refl 𝒞ᵀ {A = K.F₀ (F.F₀ B)} ⟩∘⟨refl ⟩
      Module⇒.arr (𝒞ᵀ [ 𝒞ᵀ.id ∘ K.F₁ (F.F₁ f) ])           ≈⟨ 𝒞.identityˡ {f = Module⇒.arr (K.F₁ (F.F₁ f))} ⟩
      Module⇒.arr (K.F₁ (F.F₁ f))                          ≈⟨ 𝒞.Equiv.refl ⟩
      Module⇒.arr (Fᵀ.F₁ f)                                 ≈˘⟨ 𝒞ᵀ.identityʳ {f = Fᵀ.F₁ f} ⟩
      Module⇒.arr (𝒞ᵀ [ Fᵀ.F₁ f ∘ 𝒞ᵀ.id ])                 ≈˘⟨ refl⟩∘⟨ hid-refl 𝒞ᵀ {A = Fᵀ.F₀ A} ⟩
      Module⇒.arr (𝒞ᵀ [ Fᵀ.F₁ f ∘ (hid 𝒞ᵀ ≡.refl) ])       ∎
    }

  Forgetful∘ComparisonF≡G : (Forgetful T ∘F ComparisonF) ≡F G
  Forgetful∘ComparisonF≡G = record
    { eq₀ = λ X → ≡.refl
    ; eq₁ = λ f → begin
      𝒞 [ (hid 𝒞 ≡.refl) ∘ (Gᵀ.F₁ (K.F₁ f)) ] ≈⟨ hid-refl 𝒞 ⟩∘⟨refl ⟩
      𝒞 [ 𝒞.id ∘ (Gᵀ.F₁ (K.F₁ f)) ]           ≈⟨ 𝒞.identityˡ ⟩
      (Gᵀ.F₁ (K.F₁ f))                         ≈⟨ 𝒞.Equiv.refl ⟩
      G.F₁ f                                   ≈˘⟨ 𝒞.identityʳ ⟩
      𝒞 [ G.F₁ f ∘ 𝒞.id ]                     ≈˘⟨ refl⟩∘⟨ hid-refl 𝒞 ⟩
      𝒞 [ G.F₁ f ∘ (hid 𝒞 ≡.refl) ]           ∎
    }

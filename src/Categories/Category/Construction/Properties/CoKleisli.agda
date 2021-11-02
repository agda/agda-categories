{-# OPTIONS --without-K --safe #-}
-- verbatim dual of Categories.Category.Construction.Properties.Kleisli
module Categories.Category.Construction.Properties.CoKleisli where

open import Level
import Relation.Binary.PropositionalEquality as ≡

open import Categories.Adjoint
open import Categories.Adjoint.Properties
open import Categories.Category
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Equivalence
open import Categories.Comonad
import Categories.Morphism.Reasoning as MR

open import Categories.Adjoint.Construction.CoKleisli
open import Categories.Category.Construction.CoKleisli

private
  variable
    o ℓ e : Level
    𝒞 𝒟 : Category o ℓ e

module _ {F : Functor 𝒞 𝒟} {G : Functor 𝒟 𝒞} (F⊣G : Adjoint F G) where
  private
    T : Comonad 𝒟
    T = adjoint⇒comonad F⊣G

    𝒟ₜ : Category _ _ _
    𝒟ₜ = CoKleisli T

    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟
    module 𝒟ₜ = Category 𝒟ₜ


    module T = Comonad T
    module F = Functor F
    module G = Functor G

    open Adjoint F⊣G

  -- Maclane's Comparison Functor
  ComparisonF : Functor 𝒟ₜ 𝒞
  ComparisonF = record
   { F₀ = λ X → G.F₀ X
   ; F₁ = λ {A} {B} f → 𝒞 [ (G.F₁ f) ∘ unit.η (G.F₀ A) ]
   ; identity = λ {A} → zag
   ; homomorphism = λ {X} {Y} {Z} {f} {g} → begin
      G.F₁ (g 𝒟.∘ F.F₁ (G.F₁ f) 𝒟.∘ F.F₁ (unit.η (G.F₀ X))) 𝒞.∘ unit.η (G.F₀ X) ≈⟨ pushˡ G.homomorphism ⟩
      G.F₁ g 𝒞.∘ G.F₁ ((F.F₁ (G.F₁ f)) 𝒟.∘ F.F₁ (unit.η (G.F₀ X))) 𝒞.∘ unit.η (G.F₀ X) ≈⟨ (refl⟩∘⟨ pushˡ G.homomorphism) ⟩
      G.F₁ g 𝒞.∘ G.F₁ (F.F₁ (G.F₁ f)) 𝒞.∘ G.F₁ (F.F₁ (unit.η (G.F₀ X))) 𝒞.∘ unit.η (G.F₀ X) ≈⟨ (refl⟩∘⟨ (refl⟩∘⟨ sym (unit.commute (unit.η (G.F₀ X))))) ⟩
      G.F₁ g 𝒞.∘ G.F₁ (F.F₁ (G.F₁ f)) 𝒞.∘ unit.η (G.F₀ (F.F₀ (G.F₀ X))) 𝒞.∘ unit.η (G.F₀ X) ≈⟨ (refl⟩∘⟨ pullˡ (sym (unit.commute (G.F₁ f)))) ⟩
      G.F₁ g 𝒞.∘ (unit.η (G.F₀ Y) 𝒞.∘ G.F₁ f) 𝒞.∘ unit.η (G.F₀ X) ≈⟨ (refl⟩∘⟨ Category.assoc 𝒞) ⟩
      G.F₁ g 𝒞.∘ unit.η (G.F₀ Y) 𝒞.∘ G.F₁ f 𝒞.∘ unit.η (G.F₀ X) ≈⟨ sym (Category.assoc 𝒞) ⟩
      (G.F₁ g 𝒞.∘ unit.η (G.F₀ Y)) 𝒞.∘ G.F₁ f 𝒞.∘ unit.η (G.F₀ X) ∎
   ; F-resp-≈ = λ eq → 𝒞.∘-resp-≈ (G.F-resp-≈ eq) (Category.Equiv.refl 𝒞)
   }
   where
    open 𝒞.HomReasoning
    open 𝒞.Equiv
    open MR 𝒞


{-
    { F₀ = λ X → F.F₀ X
    ; F₁ = λ {A} {B} f → 𝒟 [ counit.η (F.F₀ B) ∘ F.F₁ f ]
    ; identity = zig
    ; homomorphism = λ {X} {Y} {Z} {f} {g} → begin
      𝒟 [ counit.η (F.F₀ Z) ∘ F.F₁ (𝒞 [ 𝒞 [ G.F₁ (counit.η (F.F₀ Z)) ∘ G.F₁ (F.F₁ g)] ∘ f ])]                 ≈⟨ refl⟩∘⟨ F.homomorphism ⟩
      𝒟 [ counit.η (F.F₀ Z) ∘ 𝒟 [ F.F₁ (𝒞 [ G.F₁ (counit.η (F.F₀ Z)) ∘ G.F₁ (F.F₁ g) ]) ∘ F.F₁ f ] ]          ≈⟨ refl⟩∘⟨ F.homomorphism  ⟩∘⟨refl ⟩
      𝒟 [ counit.η (F.F₀ Z) ∘ 𝒟 [ 𝒟 [ F.F₁ (G.F₁ (counit.η (F.F₀ Z))) ∘ F.F₁ (G.F₁ (F.F₁ g)) ] ∘ F.F₁ f ] ]   ≈⟨ center⁻¹ refl refl ⟩
      𝒟 [ 𝒟 [ counit.η (F.F₀ Z) ∘ F.F₁ (G.F₁ (counit.η (F.F₀ Z))) ] ∘ 𝒟 [ F.F₁ (G.F₁ (F.F₁ g)) ∘ F.F₁ f ] ]   ≈⟨ counit.commute (counit.η (F.F₀ Z)) ⟩∘⟨refl ⟩
      𝒟 [ 𝒟 [ counit.η (F.F₀ Z) ∘ (counit.η (F.F₀ (G.F₀ (F.F₀ Z)))) ] ∘ 𝒟 [ F.F₁ (G.F₁ (F.F₁ g)) ∘ F.F₁ f ] ] ≈⟨ extend² (counit.commute (F.F₁ g))  ⟩
      𝒟 [ 𝒟 [ counit.η (F.F₀ Z) ∘ F.F₁ g ] ∘ 𝒟 [ counit.η (F.F₀ Y) ∘ F.F₁ f ] ]                               ∎
    ; F-resp-≈ = λ eq → 𝒟.∘-resp-≈ʳ (F.F-resp-≈ eq)
    }
    where
      open 𝒟.HomReasoning
      open 𝒟.Equiv
      open MR 𝒟
-}
  private
    L = ComparisonF
    module L = Functor L
    module Gₜ = Functor (Forgetful T)
    module Fₜ = Functor (Cofree T)

  G∘L≡Forgetful : (F ∘F L) ≡F Forgetful T
  G∘L≡Forgetful = {!   !}
  -- record
  --   { eq₀ = λ X → ≡.refl
  --   ; eq₁ = λ {A} {B} f → begin
  --     𝒞 [ 𝒞.id ∘ G.F₁ (𝒟 [ counit.η (F.F₀ B) ∘ F.F₁ f ]) ]        ≈⟨ 𝒞.identityˡ ⟩
  --     G.F₁ (𝒟 [ counit.η (F.F₀ B) ∘ F.F₁ f ])                      ≈⟨ G.homomorphism ⟩
  --     𝒞 [ G.F₁ (counit.η (F.F₀ B)) ∘ G.F₁ (F.F₁ f) ]               ≈˘⟨ 𝒞.identityʳ ⟩
  --     𝒞 [ 𝒞 [ G.F₁ (counit.η (F.F₀ B)) ∘ G.F₁ (F.F₁ f) ] ∘ 𝒞.id ] ∎

  --   }
  --   where
  --     open 𝒞.HomReasoning

  L∘Free≡F : (L ∘F Cofree T) ≡F G
  L∘Free≡F = {!   !}
  -- record
  --   { eq₀ = λ X → ≡.refl
  --   ; eq₁ = λ {A} {B} f → begin
  --     𝒟 [ 𝒟.id ∘ 𝒟 [ counit.η (F.F₀ B) ∘ F.F₁ (𝒞 [ unit.η B ∘ f ]) ] ] ≈⟨ 𝒟.identityˡ ⟩
  --     𝒟 [ counit.η (F.F₀ B) ∘ F.F₁ (𝒞 [ unit.η B ∘ f ]) ]               ≈⟨ pushʳ F.homomorphism ⟩
  --     𝒟 [ 𝒟 [ counit.η (F.F₀ B) ∘ F.F₁ (unit.η B) ] ∘ F.F₁ f ]          ≈⟨ elimˡ zig ⟩
  --     F.F₁ f                                                              ≈˘⟨ 𝒟.identityʳ ⟩
  --     𝒟 [ F.F₁ f ∘ 𝒟.id ]                                               ∎
  --   }
  --   where
  --     open 𝒟.HomReasoning
  --     open MR 𝒟
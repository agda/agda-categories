{-# OPTIONS --without-K --safe #-}
module Categories.Functor.Limits where

open import Level

open import Categories.Category
open import Categories.Functor
open import Categories.Functor.Properties
open import Categories.Object.Terminal
open import Categories.Object.Initial

import Categories.Diagram.Duality as Duality

open import Categories.Category.Construction.Cones
open import Categories.Category.Construction.Cocones

private
  variable
    o ℓ e : Level
    𝒞 𝒟 ℐ : Category o ℓ e

-- Whiskering of Functors onto Cones
_∘Cone_ : (F : Functor 𝒞 𝒟) → {J : Functor ℐ 𝒞} → Cone J → Cone (F ∘F J)
_∘Cone_ {𝒞 = 𝒞} {𝒟 = 𝒟} F {J} C = record
  { N = F.F₀ C.N
  ; apex = record
    { ψ = λ X → F.F₁ (C.ψ X)
    ; commute = λ f → [ F ]-resp-∘ (C.commute f)
    }
  }
  where
    module F = Functor F
    module J = Functor J
    module C = Cone J C
    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟
    open 𝒟.HomReasoning

-- Whiskering of Functors onto Cocones
_∘Cocone_ : (F : Functor 𝒞 𝒟) → {J : Functor ℐ 𝒞} → Cocone J → Cocone (F ∘F J)
_∘Cocone_ {𝒞 = 𝒞} {𝒟 = 𝒟} F {J} C = Duality.coCone⇒Cocone 𝒟 (F.op ∘Cone Duality.Cocone⇒coCone 𝒞 C)
  where
    module 𝒟 = Category 𝒟
    module F = Functor F

module Whiskering {o ℓ e} {o′ ℓ′ e′} {o″ ℓ″ e″}
                  {𝒞 : Category o ℓ e} {𝒟 : Category o′ ℓ′ e′} {ℐ : Category o″ ℓ″ e″}
                  (F : Functor 𝒞 𝒟) (J : Functor ℐ 𝒞) where

  PreservesLimits : Set _
  PreservesLimits = ∀ (C : Cone J) → IsTerminal (Cones J) C → IsTerminal (Cones (F ∘F J)) (F ∘Cone C)

  PreservesColimits : Set _
  PreservesColimits = ∀ (C : Cocone J) → IsInitial (Cocones J) C → IsInitial (Cocones (F ∘F J)) (F ∘Cocone C)

  ReflectsLimits : Set _
  ReflectsLimits = ∀ (C : Cone J) → IsTerminal (Cones (F ∘F J)) (F ∘Cone C) → IsTerminal (Cones J) C

  ReflectsColimits : Set _
  ReflectsColimits = ∀ (C : Cocone J) → IsInitial (Cocones (F ∘F J)) (F ∘Cocone C) → IsInitial (Cocones J) C

  record CreatesLimits : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ o″ ⊔ ℓ″) where
    field
      preserves-limits : PreservesLimits
      reflects-limits  : ReflectsLimits

  record CreatesColimits : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ o″ ⊔ ℓ″) where
    field
      preserves-colimits : PreservesColimits
      reflects-colimits  : ReflectsColimits

open Whiskering

Continuous : ∀ o ℓ e → (F : Functor 𝒞 𝒟) → Set _
Continuous {𝒞 = 𝒞} o ℓ e F = ∀ {𝒥 : Category o ℓ e} (J : Functor 𝒥 𝒞) → PreservesLimits F J

Cocontinuous : ∀ o ℓ e → (F : Functor 𝒞 𝒟) → Set _
Cocontinuous {𝒞 = 𝒞} o ℓ e F = ∀ {𝒥 : Category o ℓ e} (J : Functor 𝒥 𝒞) → PreservesColimits F J

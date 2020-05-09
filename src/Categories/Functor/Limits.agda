{-# OPTIONS --without-K --safe #-}
module Categories.Functor.Limits where

open import Level

open import Categories.Category
open import Categories.Functor
open import Categories.Object.Terminal
open import Categories.Object.Initial

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
    ; commute = λ {X} {Y} f → begin
      𝒟 [ F.F₁ (J.F₁ f) ∘ F.F₁ (C.ψ X) ] ≈˘⟨ F.homomorphism ⟩
      F.F₁ (𝒞 [ J.F₁ f ∘ C.ψ X ]) ≈⟨ F.F-resp-≈ (C.commute f) ⟩
      F.F₁ (C.ψ Y) ∎
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
_∘Cocone_ {𝒞 = 𝒞} {𝒟 = 𝒟} F {J} C = record
  { coapex = record
    { ψ = λ X → F.F₁ (C.ψ X)
    ; commute = λ {X} {Y} f → begin
      𝒟 [ F.F₁ (C.ψ Y) ∘ F.F₁ (J.F₁ f) ] ≈˘⟨ F.homomorphism ⟩
      F.F₁ (𝒞 [ C.ψ Y ∘ J.F₁ f ]) ≈⟨ F.F-resp-≈ (C.commute f) ⟩
      F.F₁ (C.ψ X) ∎
    }
  }
  where
    module F = Functor F
    module J = Functor J
    module C = Cocone J C
    module 𝒞 = Category 𝒞
    module 𝒟 = Category 𝒟
    open 𝒟.HomReasoning

module Whiskering {o ℓ e} {o′ ℓ′ e′} {o″ ℓ″ e″}
                  {𝒞 : Category o ℓ e} {𝒟 : Category o′ ℓ′ e′} {ℐ : Category o″ ℓ″ e″}
                  (F : Functor 𝒞 𝒟) (J : Functor ℐ 𝒞) where

  PreservesLimits : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ o″ ⊔ ℓ″)
  PreservesLimits = ∀ (C : Cone J) → IsTerminal (Cones J) C → IsTerminal (Cones (F ∘F J)) (F ∘Cone C)

  PreservesColimits : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ o″ ⊔ ℓ″)
  PreservesColimits = ∀ (C : Cocone J) → IsInitial (Cocones J) C → IsInitial (Cocones (F ∘F J)) (F ∘Cocone C)

  ReflectsLimits : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ o″ ⊔ ℓ″)
  ReflectsLimits = ∀ (C : Cone J) → IsTerminal (Cones (F ∘F J)) (F ∘Cone C) → IsTerminal (Cones J) C

  ReflectsColimits : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ o″ ⊔ ℓ″)
  ReflectsColimits = ∀ (C : Cocone J) → IsInitial (Cocones (F ∘F J)) (F ∘Cocone C) → IsInitial (Cocones J) C

  record CreatesLimits : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ o″ ⊔ ℓ″) where
    field
      preserves-limits : PreservesLimits
      reflects-limits  : ReflectsLimits

  record CreatesColimits : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ o″ ⊔ ℓ″) where
    field
      preserves-colimits : PreservesColimits
      reflects-colimits  : ReflectsColimits

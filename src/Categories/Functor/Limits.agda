{-# OPTIONS --without-K --safe #-}
module Categories.Functor.Limits where

open import Level

open import Categories.Category
open import Categories.Functor
open import Categories.Functor.Properties
open import Categories.Object.Terminal
open import Categories.Object.Initial

open import Categories.Diagram.Limit
open import Categories.Diagram.Colimit
open import Categories.Diagram.Cone.Properties
open import Categories.Diagram.Cocone.Properties

open import Categories.Category.Construction.Cones
open import Categories.Category.Construction.Cocones

private
  variable
    o ℓ e : Level
    𝒞 𝒟 ℐ : Category o ℓ e

module _ (F : Functor 𝒞 𝒟) {J : Functor ℐ 𝒞} where

  PreservesLimit : (L : Limit J) → Set _
  PreservesLimit L = IsTerminal (Cones (F ∘F J)) (F-map-Coneˡ F limit)
    where open Limit L

  PreservesColimit : (L : Colimit J) → Set _
  PreservesColimit L = IsInitial (Cocones (F ∘F J)) (F-map-Coconeˡ F colimit)
    where open Colimit L

  ReflectsLimits : Set _
  ReflectsLimits = ∀ (K : Cone J) → IsTerminal (Cones (F ∘F J)) (F-map-Coneˡ F K) → IsTerminal (Cones J) K

  ReflectsColimits : Set _
  ReflectsColimits = ∀ (K : Cocone J) → IsInitial (Cocones (F ∘F J)) (F-map-Coconeˡ F K) → IsInitial (Cocones J) K

--   record CreatesLimits : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ o″ ⊔ ℓ″) where
--     field
--       preserves-limits : PreservesLimit
--       reflects-limits  : ReflectsLimits

--   record CreatesColimits : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ o″ ⊔ ℓ″) where
--     field
--       preserves-colimits : PreservesColimit
--       reflects-colimits  : ReflectsColimits

Continuous : ∀ o ℓ e → (F : Functor 𝒞 𝒟) → Set _
Continuous {𝒞 = 𝒞} o ℓ e F = ∀ {𝒥 : Category o ℓ e} {J : Functor 𝒥 𝒞} (L : Limit J) → PreservesLimit F L

Cocontinuous : ∀ o ℓ e → (F : Functor 𝒞 𝒟) → Set _
Cocontinuous {𝒞 = 𝒞} o ℓ e F = ∀ {𝒥 : Category o ℓ e} {J : Functor 𝒥 𝒞} (L : Colimit J) → PreservesColimit F L

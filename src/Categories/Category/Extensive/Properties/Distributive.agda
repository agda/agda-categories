{-# OPTIONS --without-K --safe #-}

open import Level
open import Categories.Category.Core
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Category.Cocartesian using (Cocartesian)
open import Categories.Category.Distributive using (Distributive)
open import Categories.Category.Extensive using (Extensive)
open import Categories.Diagram.Pullback using (Pullback)

import Categories.Morphism as M
import Categories.Morphism.Reasoning as MR
import Categories.Object.Coproduct as CP
open CP using (Coproduct; IsCoproduct; IsCoproduct⇒Coproduct)

import Categories.Object.Duality as Duality

module Categories.Category.Extensive.Properties.Distributive {o ℓ e} (𝒞 : Category o ℓ e) where
  open Category 𝒞
  open Pullback using (p₁∘universal≈h₁)
  open M 𝒞
  open MR 𝒞
  open HomReasoning
  open Equiv
  open Duality 𝒞

  -- Any extensive cartesian category is also distributive
  -- To show this we construct the following two pullbacks and then show by pullback-of-cp-is-cp
  -- that the top row must be a coproduct, and thereby isomorphic to A × B + A × C
  {-
  A × B -- id ×₁ i₁ --> A × (B + C) <-- id ×₁ i₂ -- A × C
    |                       |                        |
    π₂        pb₁           π₂           pb₂         π₂
    |                       |                        |
    V                       V                        V
    B  ------- i₁ -------> B + C <------- i₂ ------  C
  -}
  Extensive×Cartesian⇒Distributive : Extensive 𝒞 → Cartesian 𝒞 → Distributive 𝒞
  Extensive×Cartesian⇒Distributive extensive cartesian = record
    { cartesian = cartesian
    ; cocartesian = cocartesian
    ; isIsoˡ = record { inv = distrib.to ; iso = distrib.iso }
    }
    where
      open Extensive extensive
      open Cocartesian cocartesian
      open Cartesian cartesian using (products)
      module BP = BinaryProducts products
      open BP

      module _ {A B C : Obj} where
        -- we can even proof that the square is a pullback for any g
        -- then the left and right square are just instances with g = i₁ and g = i₂
        pb : ∀ {D} (g : D ⇒ B + C) → Pullback 𝒞 (π₂ {A = A} {B = B + C}) g
        pb g = record { p₁ = id ×₁ g ; p₂ = π₂ ; isPullback = record
          { commute = π₂∘×₁
          ; universal = λ {_} {h₁} {h₂} H → ⟨ π₁ ∘ h₁ , h₂ ⟩
          ; p₁∘universal≈h₁ = λ {X} {h₁} {h₂} {eq} → begin
              (id ×₁ g) ∘ ⟨ π₁ ∘ h₁ , h₂ ⟩ ≈⟨ ×₁∘⟨⟩ ⟩
              ⟨ id ∘ π₁ ∘ h₁ , g ∘ h₂ ⟩    ≈⟨ ⟨⟩-congʳ identityˡ ⟩
              ⟨ π₁ ∘ h₁ , g ∘ h₂ ⟩         ≈˘⟨ ⟨⟩-congˡ eq ⟩
              ⟨ π₁ ∘ h₁ , π₂ ∘ h₁ ⟩        ≈⟨ g-η ⟩
              h₁                           ∎
          ; p₂∘universal≈h₂ = project₂
          ; unique-diagram = λ {X} {h₁} {h₂} eq₁ eq₂ → BP.unique′ (begin
              π₁ ∘ h₁             ≈⟨ pushˡ (introˡ refl) ⟩
              id ∘ π₁ ∘ h₁        ≈⟨ extendʳ π₁∘×₁  ⟨
              π₁ ∘ (id ×₁ g) ∘ h₁ ≈⟨ refl⟩∘⟨ eq₁ ⟩
              π₁ ∘ (id ×₁ g) ∘ h₂ ≈⟨ extendʳ π₁∘×₁  ⟩
              id ∘ π₁ ∘ h₂        ≈⟨ pullˡ (elimˡ refl) ⟩
              π₁ ∘ h₂             ∎) eq₂
          } }

        -- by the diagram we get the canonical distributivity (iso-)morphism
        distrib : (A × B) + (A × C) ≅ A × (B + C)
        distrib = CP.up-to-iso 𝒞
          coproduct
          (IsCoproduct⇒Coproduct 𝒞 (pullback-of-cp-is-cp' (pb i₁) (pb i₂)))
        module distrib  = _≅_ distrib

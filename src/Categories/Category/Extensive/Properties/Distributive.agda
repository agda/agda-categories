{-# OPTIONS --without-K --safe #-}

open import Level
open import Categories.Category.Core
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Category.Cocartesian using (Cocartesian)
open import Categories.Category.Distributive using (Distributive)
open import Categories.Category.Extensive using (Extensive)

import Categories.Morphism as M
import Categories.Morphism.Reasoning as MR
import Categories.Diagram.Pullback as PB
open PB using (Pullback)
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
  A × B -- id ⁂ i₁ --> A × (B + C) <-- id ⁂ i₂ -- A × C
    |                       |                        |
    π₂        pb₁           π₂           pb₂         π₂
    |                       |                        |
    V                       V                        V
    B  ------ i₁ -------> B + C <------- i₂ ------  C  
  -}
  Extensive×Cartesian⇒Distributive : Extensive 𝒞 → Cartesian 𝒞 → Distributive 𝒞
  Extensive×Cartesian⇒Distributive extensive cartesian = record 
    { cartesian = cartesian 
    ; cocartesian = cocartesian 
    ; isIsoˡ = λ {A B C} → record { inv = distrib.to ; iso = record 
      { isoˡ = trans (∘-resp-≈ʳ (sym distrib-canon)) distrib.isoˡ 
      ; isoʳ = trans (∘-resp-≈ˡ (sym distrib-canon)) distrib.isoʳ 
      } } }
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
        pb g = record { p₁ = id ⁂ g ; p₂ = π₂ ; isPullback = record
          { commute = π₂∘⁂
          ; universal = λ {_} {h₁} {h₂} H → ⟨ π₁ ∘ h₁ , h₂ ⟩
          ; unique = λ {X} {h₁} {h₂} {i} {eq} H1 H2 → sym (BP.unique (begin 
              π₁ ∘ i              ≈˘⟨ identityˡ ⟩∘⟨refl ⟩ 
              ((id ∘ π₁) ∘ i)     ≈˘⟨ pullˡ π₁∘⁂ ⟩
              (π₁ ∘ (id ⁂ g) ∘ i) ≈⟨ refl⟩∘⟨ H1 ⟩
              π₁ ∘ h₁             ∎) H2)
          ; p₁∘universal≈h₁ = λ {X} {h₁} {h₂} {eq} → begin
              (id ⁂ g) ∘ ⟨ π₁ ∘ h₁ , h₂ ⟩ ≈⟨ ⁂∘⟨⟩ ⟩
              ⟨ id ∘ π₁ ∘ h₁ , g ∘ h₂ ⟩   ≈⟨ ⟨⟩-congʳ identityˡ ⟩
              ⟨ π₁ ∘ h₁ , g ∘ h₂ ⟩        ≈˘⟨ ⟨⟩-congˡ eq ⟩
              ⟨ π₁ ∘ h₁ , π₂ ∘ h₁ ⟩       ≈⟨ g-η ⟩
              h₁                          ∎
          ; p₂∘universal≈h₂ = project₂
          } }
        
        -- by the diagram we gain a distributivity (iso-)morphism
        distrib : (A × B) + (A × C) ≅ A × (B + C)
        distrib = CP.up-to-iso 𝒞 coproduct (CP.Mobile 𝒞 
          (IsCoproduct⇒Coproduct 𝒞 (pullback-of-cp-is-cp (π₂ {A = A} {B = B + C}))) 
          (PB.up-to-iso 𝒞 (pullback₁ (π₂ {A = A} {B = B + C})) (pb i₁)) 
          (PB.up-to-iso 𝒞 (pullback₂ (π₂ {A = A} {B = B + C})) (pb i₂)))
        module distrib  = _≅_ distrib
        
        -- which is actually the canonical distributivity morphism
        distrib-canon : distrib.from ≈ [ id ⁂ i₁ , id ⁂ i₂ ]
        distrib-canon = sym (Coproduct.unique coproduct 
          (trans inject₁ (p₁∘universal≈h₁ (pullback₁ (π₂ {A = A} {B = B + C}))))
          (trans inject₂ (p₁∘universal≈h₁ (pullback₂ (π₂ {A = A} {B = B + C})))))

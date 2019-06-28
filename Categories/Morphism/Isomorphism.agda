{-# OPTIONS --without-K --safe #-}
open import Categories.Category

module Categories.Morphism.Isomorphism {o ℓ e} (𝒞 : Category o ℓ e) where

open import Relation.Binary using (Rel; _Preserves_⟶_)
open import Relation.Binary.Construct.Closure.Transitive
open import Relation.Binary.PropositionalEquality as ≡

open import Categories.Category.Groupoid
open import Categories.Morphism 𝒞
open import Categories.Morphism.Properties 𝒞
import Categories.Square as Square

open Category 𝒞

private
  variable
    A B C : Obj

infixr 9 _∘ᵢ_
_∘ᵢ_ : B ≅ C → A ≅ B → A ≅ C
_∘ᵢ_ = Category._∘_ Isos

sym∘ᵢ≃refl : ∀ {f : A ≅ B} → ≅-sym f ∘ᵢ f ≃ ≅-refl
sym∘ᵢ≃refl {f = f} = record
  { from-≈ = isoˡ
  ; to-≈   = isoˡ
  }
  where open _≅_ f

∘ᵢsym≃refl : ∀ {f : A ≅ B} → f ∘ᵢ ≅-sym f ≃ ≅-refl
∘ᵢsym≃refl {f = f} = record
  { from-≈ = isoʳ
  ; to-≈   = isoʳ
  }
  where open _≅_ f

Isos-groupoid : Groupoid Isos
Isos-groupoid = record
  { _⁻¹ = ≅-sym
  ; iso = record
    { isoˡ = sym∘ᵢ≃refl
    ; isoʳ = ∘ᵢsym≃refl
    }
  }

∘ᵢ-tc : A ⟨ _≅_ ⟩⁺ B → A ≅ B
∘ᵢ-tc [ f ] = f
∘ᵢ-tc (f ∷ f⁺) = ∘ᵢ-tc f⁺ ∘ᵢ f

infix 4 _≃⁺_
_≃⁺_ : Rel (A ⟨ _≅_ ⟩⁺ B) _
f⁺ ≃⁺ g⁺ = ∘ᵢ-tc f⁺ ≃ ∘ᵢ-tc g⁺

module _ where
  open _≅_
  
  ≅⁺⇒⇒⁺ : A ⟨ _≅_ ⟩⁺ B → A ⟨ _⇒_ ⟩⁺ B
  ≅⁺⇒⇒⁺ [ f ]    = [ from f ]
  ≅⁺⇒⇒⁺ (f ∷ f⁺) = (from f) ∷ ≅⁺⇒⇒⁺ f⁺
  
  from-∘ᵢ-tc : (f⁺ : A ⟨ _≅_ ⟩⁺ B) → from (∘ᵢ-tc f⁺) ≡ ∘-tc (≅⁺⇒⇒⁺ f⁺)
  from-∘ᵢ-tc [ f ]        = ≡.refl
  from-∘ᵢ-tc (f ∷ f⁺)
    rewrite from-∘ᵢ-tc f⁺ = ≡.refl

  ≅*⇒⇒*-cong : ≅⁺⇒⇒⁺ {A} {B} Preserves _≃⁺_ ⟶ _≈⁺_
  ≅*⇒⇒*-cong {i = f⁺} {g⁺} f⁺≃⁺g⁺ = begin
    ∘-tc (≅⁺⇒⇒⁺ f⁺) ≡˘⟨ from-∘ᵢ-tc f⁺ ⟩
    from (∘ᵢ-tc f⁺) ≈⟨ _≃_.from-≈ f⁺≃⁺g⁺ ⟩
    from (∘ᵢ-tc g⁺) ≡⟨ from-∘ᵢ-tc g⁺ ⟩
    ∘-tc (≅⁺⇒⇒⁺ g⁺) ∎
    where open HomReasoning

  ≅-shift : ∀ {f : A ≅ B} {f⁺ : B ⟨ _≅_ ⟩⁺ C} {g⁺ : A ⟨ _≅_ ⟩⁺ C} →
              f ∷ f⁺ ≃⁺ g⁺ → f⁺ ≃⁺ ≅-sym f ∷ g⁺
  ≅-shift {f = f} {f⁺ = f⁺} {g⁺ = g⁺} eq = begin
    ∘ᵢ-tc f⁺                   ≈⟨ introʳ sym∘ᵢ≃refl ⟩
    ∘ᵢ-tc f⁺ ∘ᵢ (f ∘ᵢ ≅-sym f) ≈⟨ pullˡ eq ⟩
    ∘ᵢ-tc g⁺ ∘ᵢ ≅-sym f        ∎
    where open Groupoid.HomReasoning Isos-groupoid
          open Square Isos

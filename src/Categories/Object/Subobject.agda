{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Object.Subobject {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level
open import Data.Product
open import Data.Unit

open import Relation.Binary using (Poset)

open import Categories.Functor
open import Categories.Category.Construction.Comma
open import Categories.Category.SubCategory
open import Categories.Category.Construction.Thin
import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR
open import Categories.Morphism.Notation

private
  module 𝒞 = Category 𝒞

-- The Full Subcategory of the over category 𝒞/c on monomorphisms
over-mono : 𝒞.Obj → Category _ _ _
over-mono c = FullSubCategory (𝒞 / c) {I = Σ[ α ∈ 𝒞.Obj ](α ↣ c)} λ (_ , i) → record
  { f = mor i
  }
  where open Mor 𝒞
        open _↣_

-- Poset of subobjects for some c ∈ 𝒞
Subobjects : 𝒞.Obj → Poset _ _ _
Subobjects c = record
  { Carrier = 𝒞ᶜ.Obj
  ; _≈_ = 𝒞ᶜ [_≅_]
  ; _≤_ = 𝒞ᶜ [_,_]
  ; isPartialOrder = record
    { isPreorder = record
      { isEquivalence = Mor.≅-isEquivalence 𝒞ᶜ
      ; reflexive = λ iso → Mor._≅_.from iso
      ; trans = λ {(α , f) (β , g) (γ , h)} i j → record
        { g = 𝒞 [ Comma⇒.g j ∘ Comma⇒.g i ]
        ; h = lift tt
        ; commute =  𝒞.identityˡ ○ ⟺ (chase f g h i j)
        }
      }
    ; antisym = λ {(α , f) (β , g)} h i → record
      { from = h
      ; to = i
      ; iso = record
        { isoˡ = mono f _ _ (chase f g f h i ○ ⟺ 𝒞.identityʳ) , lift tt
        ; isoʳ = mono g _ _ (chase g f g i h ○ ⟺ 𝒞.identityʳ) , lift tt
        }
      }
    }
  }
  where
    𝒞ᶜ : Category _ _ _
    𝒞ᶜ = over-mono c

    module 𝒞ᶜ = Category 𝒞ᶜ

    open Mor 𝒞 using (_↣_)
    open MR 𝒞
    open 𝒞.HomReasoning
    open _↣_

    chase : ∀ {α β γ : 𝒞.Obj} (f : 𝒞 [ α ↣ c ]) (g : 𝒞 [ β ↣ c ]) (h : 𝒞 [ γ ↣ c ])
            → (i : 𝒞ᶜ [ (α , f) , (β , g) ]) → (j : 𝒞ᶜ [ (β , g) , (γ , h) ])
            → 𝒞 [ 𝒞 [ mor h ∘ 𝒞 [ Comma⇒.g j ∘ Comma⇒.g i ] ] ≈ mor f ]
    chase f g h i j = begin
      𝒞 [ mor h ∘ 𝒞 [ Comma⇒.g j ∘ Comma⇒.g i ] ] ≈⟨ pullˡ (⟺ (Comma⇒.commute j)) ⟩
      𝒞 [ 𝒞 [ 𝒞.id ∘ mor g ] ∘ Comma⇒.g i ]       ≈⟨ 𝒞.identityˡ ⟩∘⟨refl ⟩
      𝒞 [ mor g ∘ Comma⇒.g i ]                    ≈˘⟨ Comma⇒.commute i ⟩
      𝒞 [ 𝒞.id ∘ mor f ]                          ≈⟨ 𝒞.identityˡ ⟩
      mor f ∎

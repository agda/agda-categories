{-# OPTIONS --safe --without-K #-}

open import Categories.Category.Core
open import Categories.Category.Displayed

module Categories.Morphism.Displayed.Properties {o ℓ e o′ ℓ′ e′} {B : Category o ℓ e} (C : Displayed B o′ ℓ′ e′) where

open import Categories.Morphism B
open import Categories.Morphism.Displayed C
open import Categories.Morphism.Displayed.Reasoning C
open import Categories.Morphism.Properties B

open Category B
open Displayed C
open HomReasoning′

private
  variable
    X Y : Obj
    X′ Y′ Z′ : Obj[ X ]
    f g h i : X ⇒ Y
    h′ i′ : X′ ⇒[ f ] Y′

module _ {f′ : X′ ⇒[ f ] Y′} {g′ : Y′ ⇒[ g ] X′} {iso : Iso f g} (diso : DisplayedIso f′ g′ iso) where

  open DisplayedIso diso

  DisplayedIso-resp-≈[] : {f≈h : f ≈ h} {g≈i : g ≈ i} → f′ ≈[ f≈h ] h′ → g′ ≈[ g≈i ] i′ → DisplayedIso h′ i′ (Iso-resp-≈ iso f≈h g≈i)
  DisplayedIso-resp-≈[] {h′ = h′} {i′ = i′} f′≈h′ g′≈i′ = record
    { isoˡ′ = begin′
      i′ ∘′ h′ ≈˘[]⟨ g′≈i′ ⟩∘′⟨ f′≈h′ ⟩
      g′ ∘′ f′ ≈[]⟨ isoˡ′ ⟩
      id′      ∎′
    ; isoʳ′ = begin′
      h′ ∘′ i′ ≈˘[]⟨ f′≈h′ ⟩∘′⟨ g′≈i′ ⟩
      f′ ∘′ g′ ≈[]⟨ isoʳ′ ⟩
      id′      ∎′
    }

DisplayedIso-∘′ : {f′ : X′ ⇒[ f ] Y′} {g′ : Y′ ⇒[ g ] X′} {h′ : Y′ ⇒[ h ] Z′} {i′ : Z′ ⇒[ i ] Y′}
                → {f≅g : Iso f g} {h≅i : Iso h i}
                → DisplayedIso f′ g′ f≅g → DisplayedIso h′ i′ h≅i
                → DisplayedIso (h′ ∘′ f′) (g′ ∘′ i′) (Iso-∘ f≅g h≅i)
DisplayedIso-∘′ {f′ = f′} {g′ = g′} {h′ = h′} {i′ = i′} f′≅g′ h′≅i′ = record
  { isoˡ′ = begin′
    (g′ ∘′ i′) ∘′ (h′ ∘′ f′) ≈[]⟨ cancelInner′ (isoˡ′ h′≅i′) ⟩
    g′ ∘′ f′                 ≈[]⟨ isoˡ′ f′≅g′ ⟩
    id′                      ∎′
  ; isoʳ′ = begin′
    (h′ ∘′ f′) ∘′ (g′ ∘′ i′) ≈[]⟨ cancelInner′ (isoʳ′ f′≅g′) ⟩
    h′ ∘′ i′                 ≈[]⟨ isoʳ′ h′≅i′ ⟩
    id′                      ∎′
  }
  where open DisplayedIso

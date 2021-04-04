{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Construction.FreeCategory where

-- "Free Category on a Quiver" Construction.

open import Level
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (refl; sym)
open import Relation.Binary.PropositionalEquality.Subst.Properties using (module TransportStar)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties
open import Data.Quiver
open import Data.Quiver.Paths
import Data.Quiver.Morphism as QM
open QM using (Morphism; _≃_)

open import Categories.Category
import Categories.Category.Construction.FreeQuiver as FQ
open import Categories.Category.Construction.Quivers
open import Categories.Category.Instance.StrictCats
open import Categories.Functor using (Functor)
import Categories.Morphism.HeterogeneousIdentity as HId
import Categories.Morphism.Reasoning as MR

private
  variable
    o o′ ℓ ℓ′ e e′ : Level

FreeCategory : Functor (Quivers o ℓ e) (Cats o (o ⊔ ℓ) (o ⊔ ℓ ⊔ e))
FreeCategory = record
  { F₀ = FQ.PathCategory
  ; F₁ = λ {G₁} {G₂} G⇒ → record
    { F₀ = F₀ G⇒
    ; F₁ = qmap G⇒
    ; identity = Paths.refl G₂
    ; homomorphism = λ {_} {_} {_} {f} {g} → FQ.≡⇒≈* G₂ $ gmap-◅◅ (F₀ G⇒) (F₁ G⇒) f g
    ; F-resp-≈ = λ { {f = f} → map-resp G⇒ f}
    }
  ; identity = λ {G} → record
    { eq₀ = λ _ → refl
    ; eq₁ = λ f → toSquare (FQ.PathCategory G) (FQ.≡⇒≈* G $ gmap-id f)
    }
  ; homomorphism = λ {_} {_} {G} {f} {g} → record
    { eq₀ = λ _ → refl
    ; eq₁ = λ h → toSquare (FQ.PathCategory G) (FQ.≡⇒≈* G (sym $ gmap-∘ (F₀ g) (F₁ g) (F₀ f) (F₁ f) h) )
    }
  ; F-resp-≈ = λ {_} {G} {f} {g} f≈g → record
    { eq₀ = λ _ → F₀≡ f≈g
    ; eq₁ = λ h →
      let open Category (FQ.PathCategory G)
          open HId      (FQ.PathCategory G)
          open TransportStar (Quiver._⇒_ G)
          open HomReasoning
      in begin
        qmap f h ◅◅ (hid $ F₀≡ f≈g) ≈˘⟨ hid-subst-cod (qmap f h) (F₀≡ f≈g) ⟩
        qmap f h ▸* F₀≡ f≈g          ≈⟨ map-F₁≡ f≈g h ⟩
        F₀≡ f≈g ◂* qmap g h          ≈⟨ hid-subst-dom (F₀≡ f≈g) (qmap g h) ⟩
        (hid $ F₀≡ f≈g) ◅◅ qmap g h ∎
    }
  }
  where
  open Morphism
  open _≃_
  open MR

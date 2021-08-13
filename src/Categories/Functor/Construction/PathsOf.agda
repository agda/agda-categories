{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Construction.PathsOf where

-- "Free Category on a Quiver" Construction, i.e. the category of paths of the quiver.

-- Note the use of Categories.Morphism.HeterogeneousIdentity as well as
-- Relation.Binary.PropositionalEquality.Subst.Properties which are needed
-- for F-resp-≈.
open import Level
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (refl; sym)
open import Relation.Binary.PropositionalEquality.Subst.Properties using (module TransportStar)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties
open import Data.Quiver
open import Data.Quiver.Morphism
open import Data.Quiver.Paths using (module Paths)

open import Categories.Category
import Categories.Category.Construction.PathCategory as PC
open import Categories.Category.Instance.Quivers
open import Categories.Category.Instance.StrictCats
open import Categories.Functor using (Functor)
open import Categories.Functor.Equivalence using (_≡F_)
import Categories.Morphism.HeterogeneousIdentity as HId
import Categories.Morphism.Reasoning as MR

private
  variable
    o o′ ℓ ℓ′ e e′ : Level
    G₁ G₂ : Quiver o ℓ e

⇒toPathF : {G₁ G₂ : Quiver o ℓ e} → Morphism G₁ G₂ → Functor (PC.PathCategory G₁) (PC.PathCategory G₂)
⇒toPathF {G₁ = G₁} {G₂} G⇒ = record
    { F₀ = F₀ G⇒
    ; F₁ = qmap G⇒
    ; identity = Paths.refl G₂
    ; homomorphism = λ {_} {_} {_} {f} {g} → Paths.≡⇒≈* G₂ $ gmap-◅◅ (F₀ G⇒) (F₁ G⇒) f g
    ; F-resp-≈ = λ { {f = f} → map-resp G⇒ f}
    }
    where open Morphism

⇒toPathF-resp-≃ : {f g : Morphism G₁ G₂} → f ≃ g → ⇒toPathF f ≡F ⇒toPathF g
⇒toPathF-resp-≃ {G₂ = G} {f} {g} f≈g = record
  { eq₀ = λ _ → F₀≡
  ; eq₁ = λ h →
    let open Category.HomReasoning (PC.PathCategory G)
        open HId      (PC.PathCategory G)
        open TransportStar (Quiver._⇒_ G)
    in begin
      qmap f h ◅◅ (hid F₀≡) ≈˘⟨ hid-subst-cod (qmap f h) F₀≡ ⟩
      qmap f h ▸* F₀≡       ≈⟨ map-F₁≡ f≈g h ⟩
      F₀≡ ◂* qmap g h       ≈⟨ hid-subst-dom F₀≡ (qmap g h) ⟩
      hid F₀≡ ◅◅ qmap g h   ∎
  }
  where
    open _≃_ f≈g

PathsOf : Functor (Quivers o ℓ e) (StrictCats o (o ⊔ ℓ) (o ⊔ ℓ ⊔ e))
PathsOf = record
  { F₀ = PC.PathCategory
  ; F₁ = ⇒toPathF
  ; identity = λ {G} → record
    { eq₀ = λ _ → refl
    ; eq₁ = λ f → toSquare (PC.PathCategory G) (Paths.≡⇒≈* G $ gmap-id f)
    }
  ; homomorphism = λ {_} {_} {G} {f} {g} → record
    { eq₀ = λ _ → refl
    ; eq₁ = λ h → toSquare (PC.PathCategory G) (Paths.≡⇒≈* G (sym $ gmap-∘ (F₀ g) (F₁ g) (F₀ f) (F₁ f) h) )
    }
  ; F-resp-≈ = ⇒toPathF-resp-≃
  }
  where
  open Morphism using (F₀; F₁)
  open MR using (toSquare)

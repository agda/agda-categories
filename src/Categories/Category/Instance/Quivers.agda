{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Quivers where

-- The Category of Quivers

open import Level using (Level; suc; _⊔_)
open import Function using (_$_; flip)
open import Relation.Binary.PropositionalEquality as ≡
open import Relation.Binary.PropositionalEquality.Subst.Properties
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties hiding (trans)
open import Data.Quiver
open import Data.Quiver.Paths
import Data.Quiver.Morphism as QM
open QM using (Morphism; _≃_; ≃-Equivalence; ≃-resp-∘)

open import Categories.Category
import Categories.Category.Construction.PathCategory as PC
open import Categories.NaturalTransformation hiding (id)
open import Categories.NaturalTransformation.NaturalIsomorphism
  hiding (refl; sym; trans; isEquivalence; _≃_)
import Categories.Morphism.HeterogeneousIdentity as HId

private
  variable
    o ℓ e o′ ℓ′ e′ : Level

Quivers : ∀ o ℓ e → Category (suc (o ⊔ ℓ ⊔ e)) (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
Quivers o ℓ e = record
  { Obj       = Quiver o ℓ e
  ; _⇒_       = Morphism
  ; _≈_       = _≃_
  ; id        = QM.id
  ; _∘_       = QM._∘_
  ; assoc     = λ {_ _ _ G} → record { F₀≡ = refl ; F₁≡ = Equiv.refl G }
  ; sym-assoc = λ {_ _ _ G} → record { F₀≡ = refl ; F₁≡ = Equiv.refl G }
  ; identityˡ = λ {_ G}     → record { F₀≡ = refl ; F₁≡ = Equiv.refl G }
  ; identityʳ = λ {_ G}     → record { F₀≡ = refl ; F₁≡ = Equiv.refl G }
  ; identity² = λ {G}       → record { F₀≡ = refl ; F₁≡ = Equiv.refl G }
  ; equiv     = ≃-Equivalence
  ; ∘-resp-≈  = QM.≃-resp-∘
  }
  where open Quiver

-- define these ahead of time
module _ {G₁ G₂ : Quiver o ℓ e} (G⇒ : Morphism G₁ G₂) where
  open Quiver G₁ renaming (_⇒_ to _⇒₁_; Obj to Obj₁)
  open Quiver G₂ renaming (_⇒_ to _⇒₂_; Obj to Obj₂; module Equiv to Equiv₂)
  open PC
  open Morphism G⇒
  open Paths renaming (_≈*_ to [_]_≈*_)

  qmap : {A B : Obj₁} → Star _⇒₁_ A B → Star _⇒₂_ (F₀ A) (F₀ B)
  qmap = gmap F₀ F₁

  -- this is needed, because this uses F-resp-≈ and not ≡
  -- unlike gmap-cong
  map-resp : {A B : Obj₁} (f : Star _⇒₁_ A B) {g : Star _⇒₁_ A B} →
      [ G₁ ] f ≈* g → [ G₂ ] qmap f ≈* qmap g
  map-resp ε ε = ε
  map-resp (x ◅ f) (f≈* ◅ eq) = F-resp-≈ f≈* ◅ map-resp f eq

module _ {G H : Quiver o ℓ e} {f g : Morphism G H}
         (f≈g : f ≃ g) where
  open Quiver G
  open Paths H using (_≈*_; _◅_)
  open Morphism
  open _≃_ f≈g
  open Transport (Quiver._⇒_ H)
  open TransportStar (Quiver._⇒_ H)

  map-F₁≡ : {A B : Obj} (hs : Star _⇒_ A B) →
            qmap f hs ▸* F₀≡ ≈* F₀≡ ◂* qmap g hs
  map-F₁≡ ε        = Paths.≡⇒≈* H (◂*-▸*-ε F₀≡)
  map-F₁≡ (hs ◅ h) = begin
    (F₁ f hs ◅ qmap f h) ▸* F₀≡   ≡⟨ ◅-▸* (F₁ f hs) _ F₀≡ ⟩
    F₁ f hs ◅ (qmap f h ▸* F₀≡)   ≈⟨ Quiver.Equiv.refl H ◅ map-F₁≡ h ⟩
    F₁ f hs ◅ (F₀≡ ◂* qmap g h)   ≡⟨ ◅-◂*-▸ (F₁ f hs) F₀≡ _ ⟩
    (F₁ f hs ▸ F₀≡) ◅ qmap g h    ≈⟨ F₁≡ ◅ (Paths.refl H) ⟩
    (F₀≡ ◂ F₁ g hs) ◅ qmap g h    ≡˘⟨ ◂*-◅ F₀≡ (F₁ g hs) _ ⟩
    F₀≡ ◂* (F₁ g hs ◅ qmap g h)   ∎
    where open Paths.PathEqualityReasoning H

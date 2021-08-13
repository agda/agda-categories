{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Instance.UnderlyingQuiver where

-- The forgetful functor from categories to its underlying quiver
-- **except** that this functor only goes from **StrictCats**,
-- i.e. where Functor equivalence is propositional equality, not
-- NaturalIsomorphism.

open import Level using (Level)
-- open import Function using (_$_; flip)
open import Relation.Binary.PropositionalEquality
  using (refl)
open import Relation.Binary.PropositionalEquality.Subst.Properties
  using (module Transport)
open import Data.Quiver using (Quiver)
open import Data.Quiver.Morphism using (Morphism; _≃_)

open import Categories.Category.Core using (Category)
open import Categories.Category.Instance.Quivers using (Quivers)
open import Categories.Category.Instance.StrictCats
open import Categories.Functor using (Functor)
open import Categories.Functor.Equivalence using (_≡F_)
import Categories.Morphism.HeterogeneousIdentity as HId

private
  variable
    o ℓ e o′ ℓ′ e′ : Level
    A B : Category o ℓ e

Underlying₀ : Category o ℓ e → Quiver o ℓ e
Underlying₀ C = record { Category C }

Underlying₁ : Functor A B → Morphism (Underlying₀ A) (Underlying₀ B)
Underlying₁ F = record { Functor F }

private
 ≡F-resp-≃ : {F G : Functor A B} → F ≡F G → Underlying₁ F ≃ Underlying₁ G
 ≡F-resp-≃ {B = B} {F} {G} F≈G = record
    { F₀≡ = λ {X} → eq₀ F≈G X
    ; F₁≡ = λ {x} {y} {f} →
      let open Category B using (_∘_)
          open HId B
          UB = Underlying₀ B
          open Transport (Quiver._⇒_ UB) using (_▸_; _◂_)
          module F = Functor F using (₁)
          module G = Functor G using (₁)
          open Quiver.EdgeReasoning (Underlying₀ B)
      in begin
        F.₁ f ▸ eq₀ F≈G y         ≈⟨ hid-subst-cod (F.₁ f) (eq₀ F≈G y) ⟩
        hid (eq₀ F≈G y) ∘ F.₁ f   ≈⟨ eq₁ F≈G f ⟩
        G.₁ f ∘ hid (eq₀ F≈G x)   ≈˘⟨ hid-subst-dom (eq₀ F≈G x) (G.₁ f) ⟩
        eq₀ F≈G x ◂ G.₁ f         ∎
    }
    where open _≡F_

Underlying : Functor (StrictCats o ℓ e) (Quivers o ℓ e)
Underlying = record
  { F₀ = Underlying₀
  ; F₁ = Underlying₁
  ; identity = λ {A} → record { F₀≡ = refl ; F₁≡ = Category.Equiv.refl A }
  ; homomorphism = λ where {Z = Z} → record { F₀≡ = refl ; F₁≡ = Category.Equiv.refl Z }
  ; F-resp-≈ = ≡F-resp-≃
  }

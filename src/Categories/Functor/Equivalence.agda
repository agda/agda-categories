{-# OPTIONS --without-K --safe #-}
module Categories.Functor.Equivalence where

-- A 'strict' equality relation for Functors.

open import Level
open import Data.Product using (Σ; curry) renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality as ≡
open import Relation.Binary using (IsEquivalence)
open import Function using (_$_) renaming (_∘_ to _⊚_)

open import Categories.Category using (Category; _[_,_]; _[_≈_]; module Definitions)
open import Categories.Category.Product
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Bifunctor
open import Categories.Functor.Properties using ([_]-resp-square)
open import Categories.NaturalTransformation using (ntHelper)
import Categories.Morphism as Morphism
import Categories.Morphism.HeterogeneousIdentity as HId
import Categories.Morphism.HeterogeneousIdentity.Properties as HIdProps
import Categories.Morphism.IsoEquiv as IsoEquiv
import Categories.Morphism.Reasoning as MorphismReasoning
import Categories.NaturalTransformation.NaturalIsomorphism as NatIso

private
  variable
    o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ o‴ ℓ‴ e‴ : Level

-- "Strict" equality of Functors.
--
-- It's helpful to think of a functor equality (P : F ≡F G) as a
-- special natural isomorphism where every component (hid $ eq₀ P X)
-- is a 'heterogeneous' identity.

infix  4 _≡F_

record _≡F_ {C : Category o ℓ e}
            {D : Category o′ ℓ′ e′}
            (F G : Functor C D) : Set (ℓ ⊔ o ⊔ o′ ⊔ e′) where
  private
    module C = Category C
    module D = Category D
    module F = Functor F
    module G = Functor G
  open F using (F₀; F₁)
  open G using () renaming (F₀ to G₀; F₁ to G₁)
  open HId D
  open Definitions D

  field
    eq₀ : ∀ X → F₀ X ≡ G₀ X

    eq₁ : ∀ {X Y} (f : C [ X , Y ]) →
          CommutativeSquare (F₁ f) (hid $ eq₀ X) (hid $ eq₀ Y) (G₁ f)

  eq₀⁻¹ : ∀ X → G₀ X ≡ F₀ X
  eq₀⁻¹ X = sym $ eq₀ X

  eq₁⁻¹ : ∀ {X Y} (f : C [ X , Y ]) →
          CommutativeSquare (G₁ f) (hid $ eq₀⁻¹ X) (hid $ eq₀⁻¹ Y) (F₁ f)
  eq₁⁻¹ {X} {Y} f = begin
      τ⁻¹ Y ∘   G₁ f                      ≈˘⟨ identityʳ ⟩
     (τ⁻¹ Y ∘   G₁ f) ∘  id               ≈˘⟨ ∘-resp-≈ʳ $ hid-symʳ _ ⟩
     (τ⁻¹ Y ∘   G₁ f) ∘ (τ X   ∘ τ⁻¹ X)   ≈⟨ assoc ⟩
      τ⁻¹ Y ∘  (G₁ f  ∘ (τ X   ∘ τ⁻¹ X))  ≈⟨ ∘-resp-≈ʳ sym-assoc ⟩
      τ⁻¹ Y ∘ ((G₁ f  ∘  τ X)  ∘ τ⁻¹ X)   ≈˘⟨ ∘-resp-≈ʳ $ ∘-resp-≈ˡ $ eq₁ f ⟩
      τ⁻¹ Y ∘ ((τ Y   ∘ F₁ f)  ∘ τ⁻¹ X)   ≈⟨ sym-assoc ⟩
     (τ⁻¹ Y ∘  (τ Y   ∘ F₁ f)) ∘ τ⁻¹ X    ≈⟨ ∘-resp-≈ˡ sym-assoc ⟩
    ((τ⁻¹ Y ∘   τ Y)  ∘ F₁ f)  ∘ τ⁻¹ X    ≈⟨ ∘-resp-≈ˡ $ ∘-resp-≈ˡ $ hid-symˡ _ ⟩
    (id               ∘ F₁ f)  ∘ τ⁻¹ X    ≈⟨ ∘-resp-≈ˡ identityˡ ⟩
    F₁ f                       ∘ τ⁻¹ X    ∎
    where
      τ   = λ X → hid $ eq₀   X
      τ⁻¹ = λ X → hid $ eq₀⁻¹ X
      open D
      open HomReasoning

  open NatIso using (_≃_)

  -- the family (hid eq₀) is a natural isomorphism

  natIso : F ≃ G
  natIso = record
    { F⇒G = ntHelper record { η = hid ⊚ eq₀   ; commute = eq₁   }
    ; F⇐G = ntHelper record { η = hid ⊚ eq₀⁻¹ ; commute = eq₁⁻¹ }
    ; iso = λ X → hid-iso $ eq₀ X
    }

module _ {C : Category o ℓ e} {D : Category o′ ℓ′ e′} where

  open Functor
  open Category D
  open HomReasoning
  open MorphismReasoning D
  open HId D
  open _≡F_

  -- Strict functor equality is an equivalence.

  ≡F-equiv : IsEquivalence (_≡F_ {C = C} {D})
  ≡F-equiv = record
    { refl  = record { eq₀ = λ _ → refl ; eq₁ = λ _ → id-comm-sym }
    ; sym   = λ F≡G → record { eq₀ = eq₀⁻¹ F≡G ; eq₁ = eq₁⁻¹ F≡G }
    ; trans = λ {F G H} F≡G G≡H → record
      { eq₀ = λ X → trans (eq₀ F≡G X) (eq₀ G≡H X)
      ; eq₁ = λ {X} {Y} f → begin
          hid (trans (eq₀ F≡G Y) (eq₀ G≡H Y)) ∘ F₁ F f
        ≈˘⟨ ∘-resp-≈ˡ (hid-trans _ _) ⟩
          (hid (eq₀ G≡H Y) ∘ hid (eq₀ F≡G Y)) ∘ F₁ F f
        ≈⟨ glue (eq₁ G≡H f) (eq₁ F≡G f) ⟩
          F₁ H f ∘ (hid (eq₀ G≡H X) ∘ hid (eq₀ F≡G X))
        ≈⟨ ∘-resp-≈ʳ (hid-trans _ _) ⟩
          F₁ H f ∘ hid (trans (eq₀ F≡G X) (eq₀ G≡H X))
        ∎
      }
    }

  ≡F-identityˡ : {F : Functor C D} → idF ∘F F ≡F F
  ≡F-identityˡ = record { eq₀ = λ _ → refl ; eq₁ = λ _ → id-comm-sym }

  ≡F-identityʳ : {F : Functor C D} → F ∘F idF ≡F F
  ≡F-identityʳ = record { eq₀ = λ _ → refl ; eq₁ = λ _ → id-comm-sym }

module _ {C : Category o ℓ e} where
  open MorphismReasoning C

  ≡F-identity² : idF ∘F idF ≡F idF {C = C}
  ≡F-identity² = record { eq₀ = λ _ → refl ; eq₁ = λ _ → id-comm-sym }

module _ {C : Category o ℓ e} {D : Category o′ ℓ′ e′}
         {E : Category o″ ℓ″ e″}
         where

  open Functor
  open Category E
  open HomReasoning
  open MorphismReasoning E
  open HId
  open HIdProps
  open _≡F_

  ∘F-resp-≡F : {H I : Functor D E} {F G : Functor C D} →
               H ≡F I → F ≡F G → H ∘F F ≡F I ∘F G
  ∘F-resp-≡F {H} {I} {F} {G} H≡I F≡G = record
    { eq₀ = λ X → trans (HF≡HG X) (HG≡IG X)
    ; eq₁ = λ {X Y} f → begin
        hid E (trans (HF≡HG Y) (HG≡IG Y)) ∘ F₁ H (F₁ F f)
      ≈˘⟨ ∘-resp-≈ˡ (hid-trans E _ _) ⟩
        (hid E (HG≡IG Y) ∘ hid E (HF≡HG Y)) ∘ F₁ H (F₁ F f)
      ≈˘⟨ ∘-resp-≈ˡ $ ∘-resp-≈ʳ (F-hid H (eq₀ F≡G Y)) ⟩
        (hid E (HG≡IG Y) ∘ F₁ H (hid D (eq₀ F≡G Y))) ∘ F₁ H (F₁ F f)
      ≈⟨ glue (eq₁ H≡I (F₁ G f)) ([ H ]-resp-square (eq₁ F≡G f)) ⟩
        F₁ I (F₁ G f) ∘ (hid E (HG≡IG X) ∘ F₁ H (hid D (eq₀ F≡G X)))
      ≈⟨ ∘-resp-≈ʳ $ ∘-resp-≈ʳ (F-hid H (eq₀ F≡G X)) ⟩
        F₁ I (F₁ G f) ∘ (hid E (HG≡IG X) ∘ hid E (HF≡HG X))
      ≈⟨ ∘-resp-≈ʳ (hid-trans E _ _) ⟩
        F₁ I (F₁ G f) ∘ hid E (trans (HF≡HG X) (HG≡IG X))
      ∎
    }
    where
      HF≡HG = λ X → cong (F₀ H) (eq₀ F≡G X)
      HG≡IG = λ X → eq₀ H≡I (F₀ G X)

module _ {B : Category o ℓ e} {C : Category o′ ℓ′ e′}
         {D : Category o″ ℓ″ e″} {E : Category o‴ ℓ‴ e‴}
         where

  open Functor
  open Category E
  open MorphismReasoning E
  open _≡F_

  ≡F-assoc : {F : Functor B C} {G : Functor C D} {H : Functor D E} →
             (H ∘F G) ∘F F  ≡F  H ∘F (G ∘F F)
  ≡F-assoc = record { eq₀ = λ _ → refl ; eq₁ = λ _ → id-comm-sym }

  ≡F-sym-assoc : {F : Functor B C} {G : Functor C D} {H : Functor D E} →
                 H ∘F (G ∘F F)  ≡F  (H ∘F G) ∘F F
  ≡F-sym-assoc = record { eq₀ = λ _ → refl ; eq₁ = λ _ → id-comm-sym }

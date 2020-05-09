{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Instance.StrictCore where

-- The 'strict' core functor (from StrictCats to StrictGroupoids).
-- This is the right-adjoint of the forgetful functor from
-- StrictGroupoids to StrictCats
-- (see Categories.Functor.Adjoint.Instance.StrictCore)

open import Data.Product
open import Level using (_⊔_)
open import Function.Base using (_on_; _$_) renaming (id to idf)
open import Relation.Binary.PropositionalEquality as ≡ using (cong; cong-id)

open import Categories.Category
import Categories.Category.Construction.Core as C
open import Categories.Category.Instance.StrictCats
open import Categories.Category.Instance.StrictGroupoids
open import Categories.Functor
open import Categories.Functor.Equivalence
open import Categories.Functor.Instance.Core renaming (Core to WeakCore)
open import Categories.Functor.Properties using ([_]-resp-≅)
import Categories.Morphism as Morphism
import Categories.Morphism.Reasoning as MR
import Categories.Morphism.HeterogeneousIdentity as HId
import Categories.Morphism.HeterogeneousIdentity.Properties as HIdProps
open import Categories.Morphism.IsoEquiv using (⌞_⌟)

Core : ∀ {o ℓ e} → Functor (Cats o ℓ e) (Groupoids o (ℓ ⊔ e) e)
Core {o} {ℓ} {e} = record
   { F₀ = F₀
   ; F₁ = F₁
   ; identity = λ {A} →
       record { eq₀ = λ _ → ≡.refl ; eq₁ = λ _ → ⌞ MR.id-comm-sym A ⌟ }
   ; homomorphism = λ {A B C} →
       record { eq₀ = λ _ → ≡.refl ; eq₁ = λ _ → ⌞ MR.id-comm-sym C ⌟ }
   ; F-resp-≈ = λ {A B F G} → CoreRespFEq {A} {B} {F} {G}
   }
   where
     open Functor WeakCore

     CoreRespFEq : {A B : Category o ℓ e} {F G : Functor A B} →
                   F ≡F G → F₁ F ≡F F₁ G
     CoreRespFEq {A} {B} {F} {G} F≡G = record
       { eq₀ = eq₀
       ; eq₁ = λ {X} {Y} f → ⌞ begin
           (from $ hid BC $ eq₀ Y) ∘ F.F₁ (from f)
         ≈⟨ ∘-resp-≈ˡ (hid-identity BC B from Equiv.refl (eq₀ Y)) ⟩
           (hid B $ ≡.cong idf $ eq₀ Y) ∘ F.F₁ (from f)
         ≡⟨ cong (λ p → hid B p ∘ _) (cong-id (eq₀ Y)) ⟩
           hid B (eq₀ Y) ∘ F.F₁ (from f)
         ≈⟨ eq₁ (from f) ⟩
           G.F₁ (from f) ∘ hid B (eq₀ X)
         ≡˘⟨ cong (λ p → _ ∘ hid B p) (cong-id (eq₀ X)) ⟩
           G.F₁ (from f) ∘ (hid B $ cong idf $ eq₀ X)
         ≈˘⟨ ∘-resp-≈ʳ (hid-identity BC B from Equiv.refl (eq₀ X)) ⟩
           G.F₁ (from f) ∘ (from $ hid BC $ eq₀ X)
         ∎ ⌟
       }
       where
         BC = C.Core B
         module F = Functor F
         module G = Functor G
         open Category B
         open HomReasoning
         open HId
         open HIdProps
         open _≡F_ F≡G
         open Morphism._≅_

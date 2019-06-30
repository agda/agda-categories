{-# OPTIONS --without-K --safe #-}
open import Categories.Category
import Categories.Category.Monoidal as M

module Categories.Category.Monoidal.Properties
  {o ℓ e} {C : Category o ℓ e} (MC : M.Monoidal C) where

open import Data.Product as , using (_,_; Σ)

open Category C
open M.Monoidal MC
open import Categories.Category.Product
open import Categories.Functor.Bifunctor
open import Categories.Functor.Properties
open import Categories.Category.Groupoid
open import Categories.Morphism C
open import Categories.Morphism.Isomorphism C
import Categories.Square as Square

private
  module C = Category C
  variable
    A B : Obj

⊗-iso : Bifunctor Isos Isos Isos
⊗-iso = record
  { F₀           = λ where
    (X , Y) → X ⊗₀ Y
  ; F₁           = λ where
    (f , g) → f ⊗ᵢ g
  ; identity     = refl⊗refl≃refl
  ; homomorphism = record { from-≈ = homomorphism ; to-≈ = homomorphism }
  ; F-resp-≈     = λ where
    (eq₁ , eq₂) → record
      { from-≈ = F-resp-≈ (from-≈ eq₁ , from-≈ eq₂)
      ; to-≈   = F-resp-≈ (to-≈ eq₁ , to-≈ eq₂)
      }
    
  }
  where open Functor ⊗
        open _≃_

_⊗ᵢ- : Obj → Functor Isos Isos
X ⊗ᵢ- = appˡ ⊗-iso X

-⊗ᵢ_ : Obj → Functor Isos Isos
-⊗ᵢ X = appʳ ⊗-iso X

module Coherence  {X Y : Obj} where
  open Groupoid.HomReasoning Isos-groupoid
  open Groupoid.Commutation Isos-groupoid
  open Functor

  private
    variable
          f f′ g h h′ i i′ j k : A ≅ B

  -- TS: following three isos commute

  ua : unit ⊗₀ (unit ⊗₀ X) ⊗₀ Y ≅ unit ⊗₀ unit ⊗₀ X ⊗₀ Y
  ua = ≅-refl ⊗ᵢ associator

  u[λY] : unit ⊗₀ (unit ⊗₀ X) ⊗₀ Y ≅ unit ⊗₀ X ⊗₀ Y
  u[λY] = ≅-refl ⊗ᵢ unitorˡ ⊗ᵢ ≅-refl

  uλ : unit ⊗₀ unit ⊗₀ X ⊗₀ Y ≅ unit ⊗₀ X ⊗₀ Y
  uλ = ≅-refl ⊗ᵢ unitorˡ

  -- setups

  perimeter : [ ((unit ⊗₀ unit) ⊗₀ X) ⊗₀ Y ⇒ unit ⊗₀ X ⊗₀ Y ]⟨
                (unitorʳ ⊗ᵢ ≅-refl) ⊗ᵢ ≅-refl               ⇒⟨ (unit ⊗₀ X) ⊗₀ Y ⟩
                associator
              ≈ associator                                  ⇒⟨ (unit ⊗₀ unit) ⊗₀ X ⊗₀ Y ⟩
                associator                                  ⇒⟨ unit ⊗₀ unit ⊗₀ X ⊗₀ Y ⟩
                uλ
              ⟩
  perimeter = sym (glue◃◽′ triangle-iso
                           (sym (lift-square′ (Equiv.trans assoc-commute-from
                                                           (∘-resp-≈ˡ (F-resp-≈ ⊗ (Equiv.refl , identity ⊗)))))))
    where open Square Isos

  [uλ]Y : (unit ⊗₀ (unit ⊗₀ X)) ⊗₀ Y ≅ (unit ⊗₀ X) ⊗₀ Y
  [uλ]Y = (≅-refl ⊗ᵢ unitorˡ) ⊗ᵢ ≅-refl
  
  aY : ((unit ⊗₀ unit) ⊗₀ X) ⊗₀ Y ≅ (unit ⊗₀ unit ⊗₀ X) ⊗₀ Y
  aY    = associator ⊗ᵢ ≅-refl
  
  [ρX]Y : ((unit ⊗₀ unit) ⊗₀ X) ⊗₀ Y ≅ (unit ⊗₀ X) ⊗₀ Y
  [ρX]Y = (unitorʳ ⊗ᵢ ≅-refl) ⊗ᵢ ≅-refl

  a₁ : (unit ⊗₀ (unit ⊗₀ X)) ⊗₀ Y ≅ unit ⊗₀ (unit ⊗₀ X) ⊗₀ Y
  a₁ = associator

  a₂ : (unit ⊗₀ X) ⊗₀ Y ≅ unit ⊗₀ X ⊗₀ Y
  a₂ = associator

  tri : [uλ]Y ∘ᵢ aY ≃ [ρX]Y
  tri = lift-triangle′ ([ appʳ ⊗ Y ]-resp-triangle triangle)

  sq : a₂ ∘ᵢ [uλ]Y ≃ u[λY] ∘ᵢ a₁
  sq = lift-square′ assoc-commute-from

  -- proofs

  perimeter′ : [ ((unit ⊗₀ unit) ⊗₀ X) ⊗₀ Y ⇒ unit ⊗₀ X ⊗₀ Y ]⟨
                 (unitorʳ ⊗ᵢ ≅-refl) ⊗ᵢ ≅-refl               ⇒⟨ (unit ⊗₀ X) ⊗₀ Y ⟩
                 associator
               ≈ aY                                          ⇒⟨ (unit ⊗₀ (unit ⊗₀ X)) ⊗₀ Y ⟩
                 associator                                  ⇒⟨ unit ⊗₀ (unit ⊗₀ X) ⊗₀ Y ⟩
                 ua                                          ⇒⟨ unit ⊗₀ unit ⊗₀ X ⊗₀ Y ⟩
                 uλ
               ⟩
  perimeter′ = begin
    associator ∘ᵢ (unitorʳ ⊗ᵢ ≅-refl) ⊗ᵢ ≅-refl              ≈⟨ perimeter ⟩
    uλ ∘ᵢ associator ∘ᵢ associator                           ≈˘⟨ refl ⟩∘⟨ pentagon-iso ⟩
    uλ ∘ᵢ ua ∘ᵢ associator ∘ᵢ aY                             ∎

  top-face : uλ ∘ᵢ ua ≃ u[λY]
  top-face = elim-triangle′ (sym perimeter′) (glue◽◃ (sym sq) tri)
    where open Square Isos

  coherence-iso : [ (unit ⊗₀ X) ⊗₀ Y ⇒ X ⊗₀ Y ]⟨
                  associator                ⇒⟨ unit ⊗₀ X ⊗₀ Y ⟩
                  unitorˡ
                ≈ unitorˡ ⊗ᵢ ≅-refl
                ⟩
  coherence-iso = triangle-prism top-face square₁ square₂ square₃
    where square₁ : [ unit ⊗₀ X ⊗₀ Y ⇒ unit ⊗₀ X ⊗₀ Y ]⟨
                      ≅-sym unitorˡ ∘ᵢ unitorˡ
                    ≈ ≅-refl ⊗ᵢ unitorˡ ∘ᵢ ≅-sym unitorˡ
                    ⟩
          square₁ = lift-square′ unitorˡ-commute-to
          
          square₂ : [ (unit ⊗₀ X) ⊗₀ Y ⇒ unit ⊗₀ unit ⊗₀ X ⊗₀ Y ]⟨
                      ≅-sym unitorˡ ∘ᵢ associator
                    ≈ ≅-refl ⊗ᵢ associator ∘ᵢ ≅-sym unitorˡ
                    ⟩
          square₂ = lift-square′ unitorˡ-commute-to
            
          square₃ : [ (unit ⊗₀ X) ⊗₀ Y ⇒ unit ⊗₀ X ⊗₀ Y ]⟨
                      ≅-sym unitorˡ ∘ᵢ unitorˡ ⊗ᵢ ≅-refl
                    ≈ ≅-refl ⊗ᵢ unitorˡ ⊗ᵢ ≅-refl ∘ᵢ ≅-sym unitorˡ
                    ⟩
          square₃ = lift-square′ unitorˡ-commute-to

  coherence : unitorˡ.from ∘ associator.from ≈ unitorˡ.from {X} ⊗₁ C.id {Y}
  coherence = project-triangle coherence-iso

open Coherence using (coherence; coherence-iso)

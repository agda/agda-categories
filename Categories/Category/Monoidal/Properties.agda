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
open import Categories.Morphism.IsoEquiv C
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

module Kelly's  {X Y : Obj} where
  open Groupoid.HomReasoning Isos-groupoid
  open Groupoid.Commutation Isos-groupoid
  open Functor

  private
    assoc′ = Groupoid.assoc Isos-groupoid
    variable
          f f′ g h h′ i i′ j k : A ≅ B

  -- TS: following three isos commute

  ua : unit ⊗₀ (unit ⊗₀ X) ⊗₀ Y ≅ unit ⊗₀ unit ⊗₀ X ⊗₀ Y
  ua = ≅.refl ⊗ᵢ associator

  u[λY] : unit ⊗₀ (unit ⊗₀ X) ⊗₀ Y ≅ unit ⊗₀ X ⊗₀ Y
  u[λY] = ≅.refl ⊗ᵢ unitorˡ ⊗ᵢ ≅.refl

  uλ : unit ⊗₀ unit ⊗₀ X ⊗₀ Y ≅ unit ⊗₀ X ⊗₀ Y
  uλ = ≅.refl ⊗ᵢ unitorˡ

  -- setups

  perimeter : [ ((unit ⊗₀ unit) ⊗₀ X) ⊗₀ Y ⇒ unit ⊗₀ X ⊗₀ Y ]⟨
                (unitorʳ ⊗ᵢ ≅.refl) ⊗ᵢ ≅.refl               ⇒⟨ (unit ⊗₀ X) ⊗₀ Y ⟩
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
  [uλ]Y = (≅.refl ⊗ᵢ unitorˡ) ⊗ᵢ ≅.refl

  aY : ((unit ⊗₀ unit) ⊗₀ X) ⊗₀ Y ≅ (unit ⊗₀ unit ⊗₀ X) ⊗₀ Y
  aY = associator ⊗ᵢ ≅.refl

  [ρX]Y : ((unit ⊗₀ unit) ⊗₀ X) ⊗₀ Y ≅ (unit ⊗₀ X) ⊗₀ Y
  [ρX]Y = (unitorʳ ⊗ᵢ ≅.refl) ⊗ᵢ ≅.refl

  tri : [uλ]Y ∘ᵢ aY ≃ [ρX]Y
  tri = lift-triangle′ ([ appʳ ⊗ Y ]-resp-triangle triangle)

  sq : associator ∘ᵢ [uλ]Y ≃ u[λY] ∘ᵢ associator
  sq = lift-square′ assoc-commute-from

  -- proofs

  perimeter′ : [ ((unit ⊗₀ unit) ⊗₀ X) ⊗₀ Y ⇒ unit ⊗₀ X ⊗₀ Y ]⟨
                 (unitorʳ ⊗ᵢ ≅.refl) ⊗ᵢ ≅.refl               ⇒⟨ (unit ⊗₀ X) ⊗₀ Y ⟩
                 associator
               ≈ aY                                          ⇒⟨ (unit ⊗₀ (unit ⊗₀ X)) ⊗₀ Y ⟩
                 associator                                  ⇒⟨ unit ⊗₀ (unit ⊗₀ X) ⊗₀ Y ⟩
                 ua                                          ⇒⟨ unit ⊗₀ unit ⊗₀ X ⊗₀ Y ⟩
                 uλ
               ⟩
  perimeter′ = begin
    associator ∘ᵢ (unitorʳ ⊗ᵢ ≅.refl) ⊗ᵢ ≅.refl              ≈⟨ perimeter ⟩
    uλ ∘ᵢ associator ∘ᵢ associator                           ≈˘⟨ refl ⟩∘⟨ pentagon-iso ⟩
    uλ ∘ᵢ ua ∘ᵢ associator ∘ᵢ aY                             ∎

  top-face : uλ ∘ᵢ ua ≃ u[λY]
  top-face = elim-triangleˡ′ (sym perimeter′) (glue◽◃ (sym sq) tri)
    where open Square Isos

  coherence-iso₁ : [ (unit ⊗₀ X) ⊗₀ Y ⇒ X ⊗₀ Y ]⟨
                  associator                ⇒⟨ unit ⊗₀ X ⊗₀ Y ⟩
                  unitorˡ
                ≈ unitorˡ ⊗ᵢ ≅.refl
                ⟩
  coherence-iso₁ = triangle-prism top-face square₁ square₂ square₃
    where square₁ : [ unit ⊗₀ X ⊗₀ Y ⇒ unit ⊗₀ X ⊗₀ Y ]⟨
                      ≅.sym unitorˡ ∘ᵢ unitorˡ
                    ≈ ≅.refl ⊗ᵢ unitorˡ ∘ᵢ ≅.sym unitorˡ
                    ⟩
          square₁ = lift-square′ unitorˡ-commute-to

          square₂ : [ (unit ⊗₀ X) ⊗₀ Y ⇒ unit ⊗₀ unit ⊗₀ X ⊗₀ Y ]⟨
                      ≅.sym unitorˡ ∘ᵢ associator
                    ≈ ≅.refl ⊗ᵢ associator ∘ᵢ ≅.sym unitorˡ
                    ⟩
          square₂ = lift-square′ unitorˡ-commute-to

          square₃ : [ (unit ⊗₀ X) ⊗₀ Y ⇒ unit ⊗₀ X ⊗₀ Y ]⟨
                      ≅.sym unitorˡ ∘ᵢ unitorˡ ⊗ᵢ ≅.refl
                    ≈ ≅.refl ⊗ᵢ unitorˡ ⊗ᵢ ≅.refl ∘ᵢ ≅.sym unitorˡ
                    ⟩
          square₃ = lift-square′ unitorˡ-commute-to

  coherence₁ : unitorˡ.from ∘ associator.from ≈ unitorˡ.from {X} ⊗₁ C.id {Y}
  coherence₁ = project-triangle coherence-iso₁

  -- another coherence property

  -- TS : the following three commute

  ρu : ((X ⊗₀ Y) ⊗₀ unit) ⊗₀ unit ≅ (X ⊗₀ Y) ⊗₀ unit
  ρu = unitorʳ ⊗ᵢ ≅.refl

  au : ((X ⊗₀ Y) ⊗₀ unit) ⊗₀ unit ≅ (X ⊗₀ Y ⊗₀ unit) ⊗₀ unit
  au = associator ⊗ᵢ ≅.refl

  [Xρ]u : (X ⊗₀ Y ⊗₀ unit) ⊗₀ unit ≅ (X ⊗₀ Y) ⊗₀ unit
  [Xρ]u = (≅.refl ⊗ᵢ unitorʳ) ⊗ᵢ ≅.refl


  perimeter″ : [ ((X ⊗₀ Y) ⊗₀ unit) ⊗₀ unit ⇒ X ⊗₀ Y ⊗₀ unit ]⟨
                 associator                                  ⇒⟨ (X ⊗₀ Y) ⊗₀ unit ⊗₀ unit ⟩
                 associator                                  ⇒⟨ X ⊗₀ Y ⊗₀ unit ⊗₀ unit ⟩
                 ≅.refl ⊗ᵢ ≅.refl ⊗ᵢ unitorˡ
               ≈ ρu                                          ⇒⟨ (X ⊗₀ Y) ⊗₀ unit ⟩
                 associator
               ⟩
  perimeter″ = glue▹◽ triangle-iso (sym (lift-square′ (Equiv.trans (∘-resp-≈ʳ (F-resp-≈ ⊗ (Equiv.sym (identity ⊗) , Equiv.refl)))
                                                                   assoc-commute-from)))
    where open Square Isos

  perimeter‴ : [ ((X ⊗₀ Y) ⊗₀ unit) ⊗₀ unit ⇒ X ⊗₀ Y ⊗₀ unit                                    ]⟨
                 associator ⊗ᵢ ≅.refl                                                           ⇒⟨ (X ⊗₀ (Y ⊗₀ unit)) ⊗₀ unit ⟩
                 (associator                                                                    ⇒⟨ X ⊗₀ (Y ⊗₀ unit) ⊗₀ unit ⟩
                 ≅.refl ⊗ᵢ associator                                                           ⇒⟨ X ⊗₀ Y ⊗₀ unit ⊗₀ unit ⟩
                 ≅.refl ⊗ᵢ ≅.refl ⊗ᵢ unitorˡ)
               ≈ ρu                                                                             ⇒⟨ (X ⊗₀ Y) ⊗₀ unit ⟩
                 associator
               ⟩
  perimeter‴ = begin
    (≅.refl ⊗ᵢ ≅.refl ⊗ᵢ unitorˡ ∘ᵢ ≅.refl ⊗ᵢ associator ∘ᵢ associator) ∘ᵢ associator ⊗ᵢ ≅.refl ≈⟨ assoc′ ⟩
    ≅.refl ⊗ᵢ ≅.refl ⊗ᵢ unitorˡ ∘ᵢ (≅.refl ⊗ᵢ associator ∘ᵢ associator) ∘ᵢ associator ⊗ᵢ ≅.refl ≈⟨ refl ⟩∘⟨ assoc′ ⟩
    ≅.refl ⊗ᵢ ≅.refl ⊗ᵢ unitorˡ ∘ᵢ ≅.refl ⊗ᵢ associator ∘ᵢ associator ∘ᵢ associator ⊗ᵢ ≅.refl   ≈⟨ refl ⟩∘⟨ pentagon-iso ⟩
    ≅.refl ⊗ᵢ ≅.refl ⊗ᵢ unitorˡ ∘ᵢ associator ∘ᵢ associator                                     ≈⟨ perimeter″ ⟩
    associator ∘ᵢ ρu                                                                            ∎

  top-face′ : [Xρ]u ∘ᵢ au ≃ ρu
  top-face′ = cut-squareʳ perimeter‴ (sym (glue◃◽′ tri′ (sym (lift-square′ assoc-commute-from))))
    where open Square Isos
          tri′ : [ X ⊗₀ (Y ⊗₀ unit) ⊗₀ unit ⇒ X ⊗₀ Y ⊗₀ unit ]⟨
                 (≅.refl ⊗ᵢ ≅.refl ⊗ᵢ unitorˡ ∘ᵢ ≅.refl ⊗ᵢ associator)
               ≈ ≅.refl ⊗ᵢ unitorʳ ⊗ᵢ ≅.refl
               ⟩
          tri′ = lift-triangle′ ([ X ⊗- ]-resp-triangle triangle)

  coherence-iso₂ : [ (X ⊗₀ Y) ⊗₀ unit ⇒ X ⊗₀ Y ]⟨
                     ≅.refl ⊗ᵢ unitorʳ ∘ᵢ associator
                   ≈ unitorʳ
                   ⟩
  coherence-iso₂ = triangle-prism top-face′ square₁ square₂ (lift-square′ unitorʳ-commute-to)
    where square₁ : [ X ⊗₀ Y ⊗₀ unit ⇒ (X ⊗₀ Y) ⊗₀ unit ]⟨
                      ≅.sym unitorʳ ∘ᵢ ≅.refl ⊗ᵢ unitorʳ
                    ≈ (≅.refl ⊗ᵢ unitorʳ) ⊗ᵢ ≅.refl ∘ᵢ ≅.sym unitorʳ
                    ⟩
          square₁ = lift-square′ unitorʳ-commute-to

          square₂ : [ (X ⊗₀ Y) ⊗₀ unit ⇒ (X ⊗₀ Y ⊗₀ unit) ⊗₀ unit ]⟨
                      ≅.sym unitorʳ ∘ᵢ associator
                    ≈ associator ⊗ᵢ ≅.refl ∘ᵢ ≅.sym unitorʳ
                    ⟩
          square₂ = lift-square′ unitorʳ-commute-to

  coherence₂ : C.id {X} ⊗₁ unitorʳ.from {Y} ∘ associator.from ≈ unitorʳ.from
  coherence₂ = project-triangle coherence-iso₂

open Kelly's using (coherence₁; coherence-iso₁; coherence₂; coherence-iso₂)

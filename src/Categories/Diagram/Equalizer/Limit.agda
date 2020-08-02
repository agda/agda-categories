{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Diagram.Equalizer.Limit {o ℓ e} (C : Category o ℓ e) where

open import Level
open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base hiding (lift)
open import Data.Fin.Patterns

open import Categories.Category.Lift
open import Categories.Category.Finite.Fin
open import Categories.Category.Finite.Fin.Instance.Parallel
open import Categories.Category.Complete
open import Categories.Diagram.Equalizer C
open import Categories.Diagram.Limit
open import Categories.Functor.Core

import Categories.Category.Construction.Cones as Co
import Categories.Morphism.Reasoning as MR

private
  module C = Category C
  open C
  open MR C
  open HomReasoning
  open Equiv

module _ {o′ ℓ′ e′} {F : Functor (liftC o′ ℓ′ e′ Parallel) C} where
  private
    module F = Functor F
    open F

  limit⇒equalizer : Limit F → Equalizer {B = F₀ (lift 1F)} (F₁ (lift 0F)) (F₁ (lift 1F))
  limit⇒equalizer L = record
    { obj       = apex
    ; arr       = proj (lift 0F)
    ; equality  = limit-commute (lift 0F) ○ ⟺ (limit-commute (lift 1F))
    ; equalize  = λ {_} {h} eq → rep record
      { apex = record
        { ψ       = λ { (lift 0F) → h
                      ; (lift 1F) → F₁ (lift 1F) ∘ h }
        ; commute = λ { {lift 0F} {lift 0F} (lift 0F) → elimˡ identity
                      ; {lift 0F} {lift 1F} (lift 0F) → eq
                      ; {lift 0F} {lift 1F} (lift 1F) → refl
                      ; {lift 1F} {lift 1F} (lift 0F) → elimˡ identity }
        }
      }
    ; universal = ⟺ commute
    ; unique    = λ {_} {h i} eq → ⟺ (terminal.!-unique record
      { arr = i
      ; commute = λ { {lift 0F} → ⟺ eq
                    ; {lift 1F} → begin
                      proj (lift 1F) ∘ i                ≈˘⟨ pullˡ (limit-commute (lift 1F)) ⟩
                      F₁ (lift 1F) ∘ proj (lift 0F) ∘ i ≈˘⟨ refl⟩∘⟨ eq ⟩
                      F₁ (lift 1F) ∘ h                  ∎ }
      })
    }
    where open Limit L

module _ o′ ℓ′ e′ {X Y} (f g : X ⇒ Y) where

  equalizer⇒limit-F : Functor (liftC o′ ℓ′ e′ Parallel) C
  equalizer⇒limit-F = record
    { F₀           = λ { (lift 0F) → X
                       ; (lift 1F) → Y }
    ; F₁           = λ { {lift 0F} {lift 0F} (lift 0F) → C.id
                       ; {lift 0F} {lift 1F} (lift 0F) → f
                       ; {lift 0F} {lift 1F} (lift 1F) → g
                       ; {lift 1F} {lift 1F} (lift 0F) → C.id }
    ; identity     = λ { {lift 0F} → refl
                       ; {lift 1F} → refl }
    ; homomorphism = λ { {lift 0F} {lift 0F} {lift 0F} {lift 0F} {lift 0F} → ⟺ identity²
                       ; {lift 0F} {lift 0F} {lift 1F} {lift 0F} {lift 0F} → ⟺ identityʳ
                       ; {lift 0F} {lift 0F} {lift 1F} {lift 0F} {lift 1F} → ⟺ identityʳ
                       ; {lift 0F} {lift 1F} {lift 1F} {lift 0F} {lift 0F} → ⟺ identityˡ
                       ; {lift 0F} {lift 1F} {lift 1F} {lift 1F} {lift 0F} → ⟺ identityˡ
                       ; {lift 1F} {lift 1F} {lift 1F} {lift 0F} {lift 0F} → ⟺ identity² }
    ; F-resp-≈     = λ { {lift 0F} {lift 0F} {lift 0F} {lift 0F} _ → refl
                       ; {lift 0F} {lift 1F} {lift 0F} {lift 0F} _ → refl
                       ; {lift 0F} {lift 1F} {lift 1F} {lift 1F} _ → refl
                       ; {lift 1F} {lift 1F} {lift 0F} {lift 0F} _ → refl }
    }

module _ o′ ℓ′ e′ {X Y} {f g : X ⇒ Y} (e : Equalizer f g) where
  open Equalizer e
  private
    F = equalizer⇒limit-F o′ ℓ′ e′ f g

  equalizer⇒limit : Limit F
  equalizer⇒limit = record
    { terminal = record
      { ⊤        = record
        { N    = obj
        ; apex = record
          { ψ       = λ { (lift 0F) → arr
                        ; (lift 1F) → g ∘ arr }
          ; commute = λ { {lift 0F} {lift 0F} (lift 0F) → identityˡ
                        ; {lift 0F} {lift 1F} (lift 0F) → equality
                        ; {lift 0F} {lift 1F} (lift 1F) → refl
                        ; {lift 1F} {lift 1F} (lift 0F) → identityˡ }
          }
        }
      ; ⊤-is-terminal = record
        { !        = λ {K} →
          let open Co.Cone F K
          in record
          { arr     = equalize (commute (lift 0F) ○ ⟺ (commute (lift 1F)))
          ; commute = λ { {lift 0F} → ⟺ universal
                        ; {lift 1F} → pullʳ (⟺ universal) ○ commute (lift 1F) }
          }
        ; !-unique = λ f →
          let open Co.Cone⇒ F f
          in ⟺ (unique (⟺ commute))
        }
      }
    }

module _ {o′ ℓ′ e′} (Com : Complete o′ ℓ′ e′ C) where

  complete⇒equalizer : ∀ {A B} (f g : A ⇒ B) → Equalizer f g
  complete⇒equalizer f g = limit⇒equalizer (Com (equalizer⇒limit-F _ _ _ f g))

{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Diagram.Pullback.Limit {o ℓ e} (C : Category o ℓ e) where

open import Data.Product using (∃₂; _,_)
open import Function using (_$_)

open import Categories.Category.Instance.Cospan
open import Categories.Functor
open import Categories.Diagram.Pullback C
open import Categories.Morphism.Reasoning C as MR hiding (center)

import Categories.Diagram.Cone as Con
import Categories.Diagram.Limit as Lim

private
  open Category C
  variable
    X Y Z : Obj
    f g h : X ⇒ Y

open HomReasoning

module _ {F : Functor Cospan C} where
  open Functor F
  open Lim F
  open Con F

  private
    W = F₀ center
    A = F₀ left
    B = F₀ right

    A⇒W : A ⇒ W
    A⇒W = F₁ cospan-arrˡ

    B⇒W : B ⇒ W
    B⇒W = F₁ cospan-arrʳ

  limit⇒pullback : Limit → Pullback A⇒W B⇒W
  limit⇒pullback lim = record
    { p₁              = proj left
    ; p₂              = proj right
    ; commute         = trans (limit-commute cospan-arrˡ) (sym (limit-commute cospan-arrʳ))
    ; universal       = universal
    ; unique          = commute′
    ; p₁∘universal≈h₁ = commute
    ; p₂∘universal≈h₂ = commute
    }
    where open Limit lim
          universal : A⇒W ∘ f ≈ B⇒W ∘ g → dom f ⇒ apex
          universal {f = f} {g = g} eq = rep $ record
            { apex = record
              { ψ       = λ { center → B⇒W ∘ g
                            ; left   → f
                            ; right  → g
                            }
            ; commute = λ { {center} {center} cospan-id  → elimˡ identity
                          ; {left} {center} cospan-arrˡ  → eq
                          ; {left} {left} cospan-id      → elimˡ identity
                          ; {right} {center} cospan-arrʳ → refl
                          ; {right} {right} cospan-id    → elimˡ identity
                          }
              }
            }

          proj-center : proj center ≈ B⇒W ∘ proj right
          proj-center = sym (limit-commute cospan-arrʳ)

          commute′ : ∀ {eq : A⇒W ∘ f ≈ B⇒W ∘ g} → proj left ∘ h ≈ f → proj right ∘ h ≈ g → h ≈ universal eq
          commute′ {f = f} {g = g} {h = h} {eq = eq} eq₁ eq₂ = sym $ terminal.!-unique $ record
            { arr     = h
            ; commute = λ { {center} → begin
                              proj center ∘ h      ≈⟨ pushˡ proj-center ⟩
                              B⇒W ∘ proj right ∘ h ≈⟨ refl⟩∘⟨ eq₂ ⟩
                              B⇒W ∘ g              ∎
                          ; {left}   → eq₁
                          ; {right}  → eq₂
                          }
            }


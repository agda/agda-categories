{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)

module Categories.Diagram.Pullback.Limit {o ℓ e} (C : Category o ℓ e) where

open import Data.Product using (∃₂; _,_)
open import Function.Base using (_$_)

open import Categories.Category using (_[_≈_])
open import Categories.Category.Instance.Span
open import Categories.Functor.Core
open import Categories.Diagram.Pullback C
open import Categories.Morphism.Reasoning C as MR hiding (center)

import Relation.Binary.PropositionalEquality.Core as ≡

import Categories.Category.Construction.Cones as Con
import Categories.Diagram.Limit as Lim

private
  module C = Category C
  module Span = Category Span
  open Category C
  variable
    X Y Z : Obj
    f g h : X ⇒ Y

open HomReasoning

module _ {F : Functor Span.op C} where
  open Functor F
  open Lim F
  open Con F

  private
    W = F₀ center
    A = F₀ left
    B = F₀ right

    A⇒W : A ⇒ W
    A⇒W = F₁ span-arrˡ

    B⇒W : B ⇒ W
    B⇒W = F₁ span-arrʳ

  limit⇒pullback : Limit → Pullback A⇒W B⇒W
  limit⇒pullback lim = record
    { p₁              = proj left
    ; p₂              = proj right
    ; commute         = trans (limit-commute span-arrˡ) (sym (limit-commute span-arrʳ))
    ; universal       = universal
    ; unique          = commute′
    ; p₁∘universal≈h₁ = commute
    ; p₂∘universal≈h₂ = commute
    }
    where open Limit lim
          open Equiv
          universal : {D : Obj} {f : D ⇒ A} {g : D ⇒ B} → A⇒W ∘ f ≈ B⇒W ∘ g → D ⇒ apex
          universal {f = f} {g = g} eq = rep $ record
            { apex = record
              { ψ       = λ { center → B⇒W ∘ g
                            ; left   → f
                            ; right  → g
                            }
            ; commute = λ { {center} {center} span-id  → elimˡ identity
                          ; {left} {center} span-arrˡ  → eq
                          ; {left} {left} span-id      → elimˡ identity
                          ; {right} {center} span-arrʳ → refl
                          ; {right} {right} span-id    → elimˡ identity
                          }
              }
            }

          proj-center : proj center ≈ B⇒W ∘ proj right
          proj-center = sym (limit-commute span-arrʳ)

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

module _ {fA fB gA : Obj} {f : fA ⇒ fB} {g : gA ⇒ fB} (p : Pullback f g) where
  open Pullback p
  open Equiv

  pullback⇒limit-F : Functor Span.op C
  pullback⇒limit-F = record
    { F₀           = λ { center → fB
                       ; left   → fA
                       ; right  → gA
                       }
    ; F₁           = λ { {center} {.center} span-id   → C.id
                       ; {left} {.left} span-id       → C.id
                       ; {right} {.right} span-id     → C.id
                       ; {.left} {.center} span-arrˡ  → f
                       ; {.right} {.center} span-arrʳ → g
                       }
    ; identity     = λ { {center} → refl
                       ; {left}   → refl
                       ; {right}  → refl
                       }
    ; homomorphism = λ { {center} {.center} {.center} {span-id} {span-id}   → sym identityˡ
                       ; {left} {.left} {.left} {span-id} {span-id}         → sym identityˡ
                       ; {right} {.right} {.right} {span-id} {span-id}      → sym identityˡ
                       ; {.left} {.left} {.center} {span-id} {span-arrˡ}    → sym identityʳ
                       ; {.right} {.right} {.center} {span-id} {span-arrʳ}  → sym identityʳ
                       ; {.left} {.center} {.center} {span-arrˡ} {span-id}  → sym identityˡ
                       ; {.right} {.center} {.center} {span-arrʳ} {span-id} → sym identityˡ
                       }
    ; F-resp-≈     = λ { {center} {.center} {span-id} {.span-id} ≡.refl     → refl
                       ; {left} {.left} {span-id} {.span-id} ≡.refl         → refl
                       ; {right} {.right} {span-id} {.span-id} ≡.refl       → refl
                       ; {.left} {.center} {span-arrˡ} {.span-arrˡ} ≡.refl  → refl
                       ; {.right} {.center} {span-arrʳ} {.span-arrʳ} ≡.refl → refl
                       }
    }

  open Functor pullback⇒limit-F
  open Lim pullback⇒limit-F
  open Con pullback⇒limit-F

  pullback⇒limit : Limit
  pullback⇒limit = record
    { terminal = record
      { ⊤        = ⊤
      ; ⊤-is-terminal = record
        { !        = !
        ; !-unique = !-unique
        }
      }
    }
    where ⊤ : Cone
          ⊤ = record
            { apex = record
              { ψ       = λ { center → g ∘ p₂
                            ; left   → p₁
                            ; right  → p₂
                            }
              ; commute = λ { {center} {.center} span-id   → identityˡ
                            ; {left} {.left} span-id       → identityˡ
                            ; {right} {.right} span-id     → identityˡ
                            ; {.left} {.center} span-arrˡ  → commute
                            ; {.right} {.center} span-arrʳ → refl
                            }
              }
            }

          ! : ∀ {A : Cone} → Cone⇒ A ⊤
          ! {A} = record
            { arr     = universal commute′
            ; commute = λ { {center} → begin
                            (g ∘ p₂) ∘ universal _ ≈⟨ pullʳ p₂∘universal≈h₂ ⟩
                            g ∘ A.ψ right          ≈⟨ A.commute span-arrʳ ⟩
                            A.ψ center             ∎
                          ; {left}   → p₁∘universal≈h₁
                          ; {right}  → p₂∘universal≈h₂
                          }
            }
            where module A = Cone A
                  commute′ = trans (A.commute span-arrˡ) (sym (A.commute span-arrʳ))

          !-unique : ∀ {A : Cone} (h : Cone⇒ A ⊤) → Cones [ ! ≈ h ]
          !-unique {A} h = sym (unique h.commute h.commute)
            where module h = Cone⇒ h

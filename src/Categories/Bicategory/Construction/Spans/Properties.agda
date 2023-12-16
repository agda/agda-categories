{-# OPTIONS --without-K --safe #-}

module Categories.Bicategory.Construction.Spans.Properties where

open import Level

open import Data.Product using (_,_; _×_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.Reasoning.Setoid as SR

open import Categories.Category
open import Categories.Category.Helper
open import Categories.Category.Instance.Setoids
open import Categories.Category.Instance.Properties.Setoids.Limits.Canonical

open import Categories.Diagram.Pullback

open import Categories.Bicategory
open import Categories.Bicategory.Monad

import Categories.Category.Diagram.Span as Span
import Categories.Bicategory.Construction.Spans as Spans

--------------------------------------------------------------------------------
-- Monads in the Bicategory of Spans are Categories

module _ {o ℓ : Level} (T : Monad (Spans.Spans (pullback o ℓ))) where

  private
    module T = Monad T

    open Span (Setoids (o ⊔ ℓ) ℓ)
    open Spans (pullback o ℓ)
    open Span⇒
    open Bicategory Spans

    open Setoid renaming (_≈_ to [_][_≈_])


  -- We can view the roof of the span as a hom set! However, we need to partition
  -- this big set up into small chunks with known domains/codomains.
  record Hom (X Y : Carrier T.C) : Set (o ⊔ ℓ) where
    field
      hom : Carrier (Span.M T.T)
      dom-eq : [ T.C ][ Span.dom T.T ⟨$⟩ hom ≈ X ]
      cod-eq : [ T.C ][ Span.cod T.T ⟨$⟩ hom ≈ Y ]

  open Hom

  private
    ObjSetoid : Setoid (o ⊔ ℓ) ℓ
    ObjSetoid = T.C

    HomSetoid : Setoid (o ⊔ ℓ) ℓ
    HomSetoid = Span.M T.T

    module ObjSetoid = Setoid ObjSetoid
    module HomSetoid = Setoid HomSetoid

    id⇒ : (X : Carrier T.C) → Hom X X
    id⇒ X = record
      { hom = arr T.η ⟨$⟩ X
      ; dom-eq = commute-dom T.η (refl T.C)
      ; cod-eq = commute-cod T.η (refl T.C)
      }

    _×ₚ_ : ∀ {A B C} → (f : Hom B C) → (g : Hom A B) → FiberProduct (Span.cod T.T) (Span.dom T.T)
    _×ₚ_ {B = B} f g = record
      { elem₁ = hom g
      ; elem₂ = hom f
      ; commute = begin
        Span.cod T.T ⟨$⟩ hom g ≈⟨ cod-eq g ⟩
        B                      ≈⟨ ObjSetoid.sym (dom-eq f) ⟩
        Span.dom T.T ⟨$⟩ hom f ∎
      }
      where
        open SR ObjSetoid

    _∘⇒_ : ∀ {A B C} (f : Hom B C) → (g : Hom A B) → Hom A C
    _∘⇒_ {A = A} {C = C} f g = record
      { hom = arr T.μ ⟨$⟩ (f ×ₚ g)
      ; dom-eq = begin
        Span.dom T.T ⟨$⟩ (arr T.μ ⟨$⟩ (f ×ₚ g)) ≈⟨ (commute-dom T.μ {f ×ₚ g} {f ×ₚ g} (HomSetoid.refl , HomSetoid.refl)) ⟩
        Span.dom T.T ⟨$⟩ hom g                  ≈⟨ dom-eq g ⟩
        A                                       ∎
      ; cod-eq = begin
        Span.cod T.T ⟨$⟩ (arr T.μ ⟨$⟩ (f ×ₚ g)) ≈⟨ commute-cod T.μ {f ×ₚ g} {f ×ₚ g} (HomSetoid.refl , HomSetoid.refl) ⟩
        Span.cod T.T ⟨$⟩ hom f                  ≈⟨ cod-eq f ⟩
        C                                       ∎
      }
      where
        open SR ObjSetoid

  SpanMonad⇒Category : Category (o ⊔ ℓ) (o ⊔ ℓ) ℓ
  SpanMonad⇒Category = categoryHelper record
    { Obj = Setoid.Carrier T.C
    ; _⇒_ = Hom
    ; _≈_ = λ f g → [ HomSetoid ][ hom f ≈ hom g ]
    ; id = λ {X} → id⇒ X
    ; _∘_ = _∘⇒_
    ; assoc = λ {A} {B} {C} {D} {f} {g} {h} →
      let f×ₚ⟨g×ₚh⟩ = record
            { elem₁ = record
              { elem₁ = hom f
              ; elem₂ = hom g
              ; commute = FiberProduct.commute (g ×ₚ f)
              }
            ; elem₂ = hom h
            ; commute = FiberProduct.commute (h ×ₚ g)
            }
      in begin
        arr T.μ ⟨$⟩ ((h ∘⇒ g) ×ₚ f) ≈⟨ Func.cong (arr T.μ) (HomSetoid.refl , Func.cong (arr T.μ) (HomSetoid.refl , HomSetoid.refl)) ⟩
        arr T.μ ⟨$⟩ _                ≈⟨ T.sym-assoc {f×ₚ⟨g×ₚh⟩} {f×ₚ⟨g×ₚh⟩} ((HomSetoid.refl , HomSetoid.refl) , HomSetoid.refl) ⟩
        arr T.μ ⟨$⟩ _                ≈⟨ (Func.cong (arr T.μ) (Func.cong (arr T.μ) (HomSetoid.refl , HomSetoid.refl) , HomSetoid.refl)) ⟩
        arr T.μ ⟨$⟩ (h ×ₚ (g ∘⇒ f)) ∎
    ; identityˡ = λ {A} {B} {f} → begin
      arr T.μ ⟨$⟩ (id⇒ B ×ₚ f) ≈⟨ Func.cong (arr T.μ) (HomSetoid.refl , Func.cong (arr T.η) (ObjSetoid.sym (cod-eq f))) ⟩
      arr T.μ ⟨$⟩ _             ≈⟨ T.identityʳ HomSetoid.refl ⟩
      hom f                     ∎
    ; identityʳ = λ {A} {B} {f} → begin
      arr T.μ ⟨$⟩ (f ×ₚ id⇒ A) ≈⟨ Func.cong (arr T.μ) (Func.cong (arr T.η) (ObjSetoid.sym (dom-eq f)) , HomSetoid.refl) ⟩
      arr T.μ ⟨$⟩ _             ≈⟨ T.identityˡ HomSetoid.refl ⟩
      hom f                     ∎
    ; equiv = record
      { refl = HomSetoid.refl
      ; sym = HomSetoid.sym
      ; trans = HomSetoid.trans
      }
    ; ∘-resp-≈ = λ f≈h g≈i → Func.cong (arr T.μ) (g≈i , f≈h)
    }
      where
        open SR HomSetoid

{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)

module Categories.Adjoint.Instance.BaseChange {o ℓ e} (C : Category o ℓ e) where

open import Categories.Adjoint using (_⊣_)
import Categories.Functor.Slice as Sl
open import Categories.Morphism.Reasoning C
open import Categories.NaturalTransformation using (ntHelper)

import Categories.Category.Slice as S
import Categories.Diagram.Pullback as PB

open Category C
open HomReasoning
open Equiv
open Sl C using (BaseChange!; BaseChange*)

module _ {A : Obj} (pb : ∀ {X Y Z} (h : X ⇒ Z) (i : Y ⇒ Z) → PB.Pullback C h i) where
  open S.SliceObj
  open S.Slice⇒
  open S C
  private
    open PB C
    module pullbacks {X Y Z} h i = Pullback (pb {X} {Y} {Z} h i)

  !⊣* : ∀ {B} (f : B ⇒ A) →  BaseChange! f ⊣ BaseChange* pb f
  !⊣* {B} f = record
    { unit   = ntHelper record
      { η       = P.η-unit
      ; commute = λ {X Y} g → P.unique-diagram Y
                         ((cancelˡ (P.p₁∘universal≈h₁ Y) ○ ⟺ (cancelʳ (P.p₁∘universal≈h₁ X)) ○ pushˡ (⟺ (P.p₁∘universal≈h₁ Y))))
                         (pullˡ (P.p₂-univ Y)  ○ △ g ○ ⟺ (P.p₂-univ X) ○ pushˡ (⟺ (pullbacks.p₂∘universal≈h₂ (f ∘ arr Y) f)))
      }
    ; counit = ntHelper record
      { η       = λ X → slicearr (Q.commute X)
      ; commute = λ {_ Y} _ → Q.p₁∘universal≈h₁ Y
      }
    ; zig    = λ {X} → P.p₁∘universal≈h₁ X
    ; zag    = λ {Y} → Q.unique-diagram Y
                         ((pullˡ (pullbacks.p₁∘universal≈h₁ (arr Y) f) ○ pullʳ (pullbacks.p₁∘universal≈h₁ (f ∘ pullbacks.p₂ (arr Y) f) f)))
                         (pullˡ (pullbacks.p₂∘universal≈h₂ (arr Y) f) ○ pullbacks.p₂∘universal≈h₂ (f ∘ pullbacks.p₂ (arr Y) f) f ○ ⟺ identityʳ)
    }
    where
      -- here the pullbacks are between (f ∘ arr X) and f with X a slice over B
      module P (X : SliceObj B) where
        open pullbacks (f ∘ arr X) f using (p₂; p₂∘universal≈h₂; universal)
        open pullbacks (f ∘ arr X) f using (p₁∘universal≈h₁; unique-diagram) public
        p₂-univ : p₂ ∘ universal identityʳ ≈ arr X
        p₂-univ = p₂∘universal≈h₂ {eq = identityʳ}
        η-unit : Slice⇒ X (sliceobj p₂)
        η-unit = slicearr p₂-univ

      -- here the pullbacks are between arr Y and f with Y a slice over A
      module Q (Y : SliceObj A) where
        open pullbacks (arr Y) f using (commute; p₁∘universal≈h₁; unique-diagram) public

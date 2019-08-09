{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Functor.Slice {o ℓ e} (C : Category o ℓ e) where

open import Categories.Category.Slice C
open import Categories.Diagram.Pullback C
open import Categories.Functor
open import Categories.Morphism.Reasoning C
open Category C
open HomReasoning

module _ (A : Obj) where
  open SliceObj
  open Slice⇒
  
  Forgetful : Functor (Slice A) C
  Forgetful = record
    { F₀           = λ X → Y X
    ; F₁           = λ f → h f
    ; identity     = refl
    ; homomorphism = refl
    ; F-resp-≈     = λ eq → eq
    }

  module _ (pullbacks : ∀ {X Y Z} (h : X ⇒ Z) (i : Y ⇒ Z) → Pullback h i) where
    private
      module pullbacks {X Y Z} h i = Pullback (pullbacks {X} {Y} {Z} h i)
    open pullbacks

    BaseChange : ∀ {B} (f : B ⇒ A) → Functor (Slice A) (Slice B)
    BaseChange f = record
      { F₀           = λ X → sliceobj (p₂ (arr X) f)
      ; F₁           = λ {X Y} g → slicearr {h = Pullback.p₂ (unglue (pullbacks (arr Y) f)
                                                                     (Pullback-resp-≈ (pullbacks (arr X) f) (△ g) refl))}
                                            (p₂∘universal≈h₂ (arr Y) f)
      ; identity     = λ {X} → ⟺ (unique (arr X) f id-comm identityʳ)
      ; homomorphism = λ {X Y Z} {h i} → unique-diagram (arr Z) f (p₁∘universal≈h₁ (arr Z) f ○ assoc ○ ⟺ (pullʳ (p₁∘universal≈h₁ (arr Y) f)) ○ ⟺ (pullˡ (p₁∘universal≈h₁ (arr Z) f)))
                                                                  (p₂∘universal≈h₂ (arr Z) f ○ ⟺ (p₂∘universal≈h₂ (arr Y) f) ○ ⟺ (pullˡ (p₂∘universal≈h₂ (arr Z) f)))
      ; F-resp-≈     = λ {X Y} eq″ → unique (arr Y) f (p₁∘universal≈h₁ (arr Y) f ○ ∘-resp-≈ˡ eq″) (p₂∘universal≈h₂ (arr Y) f)
      }
      

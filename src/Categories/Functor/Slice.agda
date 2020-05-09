{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Functor.Slice {o ℓ e} (C : Category o ℓ e) where

open import Data.Product using (_,_)

open import Categories.Adjoint
open import Categories.Category.CartesianClosed
open import Categories.Category.CartesianClosed.Locally
open import Categories.Functor
open import Categories.Functor.Properties
open import Categories.Morphism.Reasoning C
open import Categories.NaturalTransformation

import Categories.Category.Slice as S
import Categories.Diagram.Pullback as P
import Categories.Category.Construction.Pullbacks as Pbs

open Category C
open HomReasoning
open Equiv

module _ {A : Obj} where
  open S.SliceObj
  open S.Slice⇒

  Base-F : ∀ {o′ ℓ′ e′} {D : Category o′ ℓ′ e′} (F : Functor C D) → Functor (S.Slice C A) (S.Slice D (Functor.F₀ F A))
  Base-F {D = D} F = record
    { F₀           = λ { (S.sliceobj arr) → S.sliceobj (F₁ arr) }
    ; F₁           = λ { (S.slicearr △) → S.slicearr ([ F ]-resp-∘ △) }
    ; identity     = identity
    ; homomorphism = homomorphism
    ; F-resp-≈     = F-resp-≈
    }
    where module D = Category D
          open Functor F

  open S C

  Forgetful : Functor (Slice A) C
  Forgetful = record
    { F₀           = λ X → Y X
    ; F₁           = λ f → h f
    ; identity     = refl
    ; homomorphism = refl
    ; F-resp-≈     = λ eq → eq
    }

  BaseChange! : ∀ {B} (f : B ⇒ A) → Functor (Slice B) (Slice A)
  BaseChange! f = record
    { F₀           = λ X → sliceobj (f ∘ arr X)
    ; F₁           = λ g → slicearr (pullʳ (△ g))
    ; identity     = refl
    ; homomorphism = refl
    ; F-resp-≈     = λ eq → eq
    }


  module _ (pullbacks : ∀ {X Y Z} (h : X ⇒ Z) (i : Y ⇒ Z) → P.Pullback C h i) where
    private
      open P C
      module pullbacks {X Y Z} h i = Pullback (pullbacks {X} {Y} {Z} h i)
      open pullbacks

    BaseChange* : ∀ {B} (f : B ⇒ A) → Functor (Slice A) (Slice B)
    BaseChange* f = record
      { F₀           = λ X → sliceobj (p₂ (arr X) f)
      ; F₁           = λ {X Y} g → slicearr {h = Pullback.p₂ (unglue (pullbacks (arr Y) f)
                                                                     (Pullback-resp-≈ (pullbacks (arr X) f) (△ g) refl))}
                                            (p₂∘universal≈h₂ (arr Y) f)
      ; identity     = λ {X} → ⟺ (unique (arr X) f id-comm identityʳ)
      ; homomorphism = λ {X Y Z} {h i} → unique-diagram (arr Z) f (p₁∘universal≈h₁ (arr Z) f ○ assoc ○ ⟺ (pullʳ (p₁∘universal≈h₁ (arr Y) f)) ○ ⟺ (pullˡ (p₁∘universal≈h₁ (arr Z) f)))
                                                                  (p₂∘universal≈h₂ (arr Z) f ○ ⟺ (p₂∘universal≈h₂ (arr Y) f) ○ ⟺ (pullˡ (p₂∘universal≈h₂ (arr Z) f)))
      ; F-resp-≈     = λ {X Y} eq″ → unique (arr Y) f (p₁∘universal≈h₁ (arr Y) f ○ ∘-resp-≈ˡ eq″) (p₂∘universal≈h₂ (arr Y) f)
      }


    !⊣* : ∀ {B} (f : B ⇒ A) →  BaseChange! f ⊣ BaseChange* f
    !⊣* f = record
      { unit   = ntHelper record
        { η       = λ X → slicearr (p₂∘universal≈h₂ (f ∘ arr X) f {eq = identityʳ})
        ; commute = λ {X Y} g → unique-diagram (f ∘ arr Y) f
                                               (cancelˡ (p₁∘universal≈h₁ (f ∘ arr Y) f) ○ ⟺ (cancelʳ (p₁∘universal≈h₁ (f ∘ arr X) f)) ○ pushˡ (⟺ (p₁∘universal≈h₁ (f ∘ arr Y) f)))
                                               (pullˡ (p₂∘universal≈h₂ (f ∘ arr Y) f) ○ △ g ○ ⟺ (p₂∘universal≈h₂ (f ∘ arr X) f) ○ pushˡ (⟺ (p₂∘universal≈h₂ (f ∘ arr Y) f)))
        }
      ; counit = ntHelper record
        { η       = λ X → slicearr (pullbacks.commute (arr X) f)
        ; commute = λ {X Y} g → p₁∘universal≈h₁ (arr Y) f
        }
      ; zig    = λ {X} → p₁∘universal≈h₁ (f ∘ arr X) f
      ; zag    = λ {Y} → unique-diagram (arr Y) f
                                        (pullˡ (p₁∘universal≈h₁ (arr Y) f) ○ pullʳ (p₁∘universal≈h₁ (f ∘ pullbacks.p₂ (arr Y) f) f))
                                        (pullˡ (p₂∘universal≈h₂ (arr Y) f) ○ p₂∘universal≈h₂ (f ∘ pullbacks.p₂ (arr Y) f) f ○ ⟺ identityʳ)
      }

    pullback-functorial : ∀ {B} (f : B ⇒ A) → Functor (Slice A) C
    pullback-functorial f = record
      { F₀           = λ X → p.P X
      ; F₁           = λ f → p⇒ _ _ f
      ; identity     = λ {X} → sym (p.unique X id-comm id-comm)
      ; homomorphism = λ {_ Y Z} →
        p.unique-diagram Z (p.p₁∘universal≈h₁ Z ○ ⟺ identityˡ ○ ⟺ (pullʳ (p.p₁∘universal≈h₁ Y)) ○ ⟺ (pullˡ (p.p₁∘universal≈h₁ Z)))
                           (p.p₂∘universal≈h₂ Z ○ assoc ○ ⟺ (pullʳ (p.p₂∘universal≈h₂ Y)) ○ ⟺ (pullˡ (p.p₂∘universal≈h₂ Z)))
      ; F-resp-≈     = λ {_ B} {h i} eq →
        p.unique-diagram B (p.p₁∘universal≈h₁ B ○ ⟺ (p.p₁∘universal≈h₁ B))
                           (p.p₂∘universal≈h₂ B ○ ∘-resp-≈ˡ eq ○ ⟺ (p.p₂∘universal≈h₂ B))
      }
      where p : ∀ X → Pullback f (arr X)
            p X        = pullbacks f (arr X)
            module p X = Pullback (p X)

            p⇒ : ∀ X Y (g : Slice⇒ X Y) → p.P X ⇒ p.P Y
            p⇒ X Y g = Pbs.Pullback⇒.pbarr pX⇒pY
              where pX : Pbs.PullbackObj C A
                    pX = record { pullback = p X }
                    pY : Pbs.PullbackObj C A
                    pY = record { pullback = p Y }
                    pX⇒pY : Pbs.Pullback⇒ C A pX pY
                    pX⇒pY = record
                      { mor₁     = Category.id C
                      ; mor₂     = h g
                      ; commute₁ = identityʳ
                      ; commute₂ = △ g
                      }

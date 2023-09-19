{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)

module Categories.Functor.Slice {o ℓ e} (C : Category o ℓ e) where

open import Function using () renaming (id to id→)

open import Categories.Adjoint
open import Categories.Functor using (Functor)
open import Categories.Functor.Properties using ([_]-resp-∘)
open import Categories.Morphism.Reasoning C
open import Categories.NaturalTransformation hiding (id)
open import Categories.Object.Product C

import Categories.Category.Slice as S
import Categories.Diagram.Pullback as P
import Categories.Category.Construction.Pullbacks as Pbs

open Category C
open HomReasoning
open Equiv

module _ {A : Obj} where
  open S.SliceObj
  open S.Slice⇒

  -- A functor between categories induces one between the corresponding slices at a given object of C.
  Base-F : ∀ {o′ ℓ′ e′} {D : Category o′ ℓ′ e′} (F : Functor C D) → Functor (S.Slice C A) (S.Slice D (Functor.F₀ F A))
  Base-F F = record
    { F₀           = λ s → S.sliceobj (F₁ (arr s))
    ; F₁           = λ s⇒ → S.slicearr ([ F ]-resp-∘ (△ s⇒))
    ; identity     = identity
    ; homomorphism = homomorphism
    ; F-resp-≈     = F-resp-≈
    }
    where open Functor F

  open S C

  Forgetful : Functor (Slice A) C
  Forgetful = record
    { F₀           = Y
    ; F₁           = h
    ; identity     = refl
    ; homomorphism = refl
    ; F-resp-≈     = id→
    }

  -- any morphism induces a Functor between slices
  BaseChange! : ∀ {B} (f : B ⇒ A) → Functor (Slice B) (Slice A)
  BaseChange! f = record
    { F₀           = λ X → sliceobj (f ∘ arr X)
    ; F₁           = λ g → slicearr (pullʳ (△ g))
    ; identity     = refl
    ; homomorphism = refl
    ; F-resp-≈     = id→
    }


  module _ (pullback : ∀ {X} {Y} {Z} (h : X ⇒ Z) (i : Y ⇒ Z) → P.Pullback C h i) where
    private
      open P C using (Pullback; unglue; Pullback-resp-≈)
      -- open Pullbacks pb using (pullback)
      module pullbacks {X Y Z} h i = Pullback (pullback {X} {Y} {Z} h i)
      open pullbacks using (p₂; p₂∘universal≈h₂; unique; unique-diagram; p₁∘universal≈h₁)

    -- pieces that recur below and elsewhere, so name them
    module _ {B} (f : B ⇒ A) where
      q : (X : S.SliceObj C A)  → Pullback (arr X) f
      q X = pullback (arr X) f

      derived-pb : {X Y : SliceObj A} (g : Slice⇒ X Y) → Pullback (h g) (Pullback.p₁ (q Y))
      derived-pb {X} {Y} g = unglue (q Y) (Pullback-resp-≈ (q X) (△ g) refl)

    BaseChange* : ∀ {B} (f : B ⇒ A) → Functor (Slice A) (Slice B)
    BaseChange* f = record
      { F₀           = λ X → sliceobj (Q.p₂ X)
      ; F₁           = λ {X Y} g → slicearr {h = Pullback.p₂ (derived-pb f g)} (p₂∘universal≈h₂ (arr Y) f)
      ; identity     = λ {X} → {!⟺ (unique (arr X) f id-comm identityʳ)!}
      ; homomorphism = λ {X Y Z} {h i} → unique-diagram (arr Z) f (p₁∘universal≈h₁ (arr Z) f ○ assoc ○ ⟺ (pullʳ (p₁∘universal≈h₁ (arr Y) f)) ○ ⟺ (pullˡ (p₁∘universal≈h₁ (arr Z) f)))
                                                                  (p₂∘universal≈h₂ (arr Z) f ○ ⟺ (p₂∘universal≈h₂ (arr Y) f) ○ ⟺ (pullˡ (p₂∘universal≈h₂ (arr Z) f)))
      ; F-resp-≈     = λ {X Y} eq″ → unique (arr Y) f (p₁∘universal≈h₁ (arr Y) f ○ ∘-resp-≈ˡ eq″) (p₂∘universal≈h₂ (arr Y) f)
      }
      where
        module Q X = Pullback (q f X)


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
            p X        = pullback f (arr X)
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

  module _ (product : {X : Obj} → Product A X) where

    -- this is adapted from proposition 1.33 of Aspects of Topoi (Freyd, 1972)
    Free : Functor C (Slice A)
    Free = record
      { F₀ = λ _ → sliceobj [ product ]π₁
      ; F₁ = λ f → slicearr ([ product ⇒ product ]π₁∘× ○ identityˡ)
      ; identity = id×id product
      ; homomorphism = sym [ product ⇒ product ⇒ product ]id×∘id×
      ; F-resp-≈ = λ f≈g → Product.⟨⟩-cong₂ product refl (∘-resp-≈ˡ f≈g)
      }

    Forgetful⊣Free : Forgetful ⊣ Free
    Forgetful⊣Free = record
      { unit = ntHelper record
        { η = λ _ → slicearr (Product.project₁ product)
        ; commute = λ {X} {Y} f → begin
          [ product ]⟨ arr Y , id ⟩ ∘ h f                            ≈⟨ [ product ]⟨⟩∘ ⟩
          [ product ]⟨ arr Y ∘ h f , id ∘ h f ⟩                      ≈⟨ Product.⟨⟩-cong₂ product (△ f) identityˡ ⟩
          [ product ]⟨ arr X , h f ⟩                                 ≈˘⟨ Product.⟨⟩-cong₂ product identityˡ identityʳ ⟩
          [ product ]⟨ id ∘ arr X , h f ∘ id ⟩                       ≈˘⟨ [ product ⇒ product ]×∘⟨⟩ ⟩
          [ product ⇒ product ] id × h f ∘ [ product ]⟨ arr X , id ⟩ ∎
        }
      ; counit = ntHelper record
        { η = λ _ → Product.π₂ product
        ; commute = λ _ → Product.project₂ product
        }
      ; zig = Product.project₂ product
      ; zag = begin
        [ product ⇒ product ]id× [ product ]π₂ ∘ [ product ]⟨ [ product ]π₁ , id ⟩ ≈⟨ [ product ⇒ product ]×∘⟨⟩ ⟩
        [ product ]⟨ id ∘ [ product ]π₁ , [ product ]π₂ ∘ id ⟩                     ≈⟨ Product.⟨⟩-cong₂ product identityˡ identityʳ ⟩
        [ product ]⟨ [ product ]π₁ , [ product ]π₂ ⟩                               ≈⟨ Product.η product ⟩
        id                                                                         ∎
      }

{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Functor.Slice {o ℓ e} (C : Category o ℓ e) where

open import Data.Product using (_,_)

open import Categories.Adjoint
open import Categories.Category.BinaryProducts
open import Categories.Category.Cartesian
open import Categories.Category.CartesianClosed
open import Categories.Category.CartesianClosed.Locally
open import Categories.Functor hiding (id)
open import Categories.Functor.Properties
open import Categories.Morphism.Reasoning C
open import Categories.NaturalTransformation hiding (id)
open import Categories.Object.Product C
open import Categories.Object.Terminal C

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

  module _ (CCC : CartesianClosed C) (pullbacks : ∀ {X Y Z} (h : X ⇒ Z) (i : Y ⇒ Z) → P.Pullback C h i) where

    open CartesianClosed CCC renaming (cartesian to C-cartesian)
    open Cartesian C-cartesian
    open Terminal terminal
    open BinaryProducts products hiding (unique)
    open P C hiding (swap)
    private module pullbacks {X Y Z} h i = Pullback (pullbacks {X} {Y} {Z} h i)
    private module A⇨ = Functor (A ⇨-)
    open pullbacks

    Coforgetful : Functor (Slice A) C
    Coforgetful = record
      { F₀ = F₀
      ; F₁ = F₁
      ; identity = sym (unique (λg π₂) (A⇨.₁ _) !-unique₂ (id-comm ○ (∘-resp-≈ˡ (sym A⇨.identity))))
      ; homomorphism = sym (unique (λg π₂) (A⇨.₁ _) !-unique₂ (homomorphism-lemma _ _))
      ; F-resp-≈ = λ p → universal-resp-≈ (λg π₂) (A⇨.₁ _) !-unique₂ (∘-resp-≈ˡ (A⇨.F-resp-≈ p))
      }
      module Coforgetful where 
        F₀ : SliceObj A → Obj
        F₀ (sliceobj arr) = P (λg π₂) (A⇨.₁ arr)

        F₁-lemma : ∀ {X Y} (f : Slice⇒ X Y) → λg π₂ ∘ p₁ (λg π₂) (A⇨.₁ (arr X)) ≈ A⇨.₁ (arr Y) ∘ A⇨.₁ (h f) ∘ p₂ (λg π₂) (A⇨.₁ (arr X))
        F₁-lemma (slicearr {h} △) = begin
          λg π₂ ∘ p₁ (λg π₂) (A⇨.₁ _)           ≈⟨ commute (λg π₂) (A⇨.₁ _) ⟩
          A⇨.₁ _ ∘ p₂ (λg π₂) (A⇨.₁ _)          ≈˘⟨ A⇨.F-resp-≈ △ ⟩∘⟨refl ⟩
          A⇨.₁ (_ ∘ h) ∘ p₂ (λg π₂) (A⇨.₁ _)    ≈⟨ pushˡ A⇨.homomorphism ⟩
          A⇨.₁ _ ∘ A⇨.₁ h ∘ p₂ (λg π₂) (A⇨.₁ _) ∎

        F₁ : ∀ {X Y} → Slice⇒ X Y → F₀ X ⇒ F₀ Y
        F₁ f = universal (λg π₂) (A⇨.₁ _) (F₁-lemma f)

        homomorphism-lemma : ∀ {X Y Z} (f : Slice⇒ X Y) (g : Slice⇒ Y Z) → p₂ (λg π₂) (A⇨.₁ (arr Z)) ∘ F₁ g ∘ F₁ f ≈ A⇨.₁ (h g ∘ h f) ∘ p₂ (λg π₂) (A⇨.₁ (arr X))
        homomorphism-lemma f g = begin
          p₂ (λg π₂) (A⇨.₁ _) ∘ F₁ g ∘ F₁ f             ≈⟨ extendʳ (p₂∘universal≈h₂ (λg π₂) (A⇨.₁ _)) ⟩
          A⇨.₁ (h g) ∘ p₂ (λg π₂) (A⇨.₁ _) ∘ F₁ f       ≈⟨ refl⟩∘⟨ (p₂∘universal≈h₂ (λg π₂) (A⇨.₁ _)) ⟩
          A⇨.₁ (h g) ∘ A⇨.₁ (h f) ∘ p₂ (λg π₂) (A⇨.₁ _) ≈˘⟨ pushˡ A⇨.homomorphism ⟩
          A⇨.₁ (h g ∘ h f) ∘ p₂ (λg π₂) (A⇨.₁ _)        ∎


    Free⊣Coforgetful : Free product ⊣ Coforgetful
    Free⊣Coforgetful = record
      { unit = ntHelper record
        { η = unit/η
        ; commute = {!!}
        }
      ; counit = ntHelper record
        { η = {!!}
        ; commute = {!!}
        }
      ; zig = {!!}
      ; zag = {!!}
      }
      where
        s : ∀ α → eval′ ∘ first (λg π₂ ∘ !) ≈ eval′ ∘ first (λg (π₁ {A} {α} ∘ eval′ ∘ second id) ∘ λg swap)
        s α = begin
          eval′ ∘ first (λg π₂ ∘ !)                                     ≈˘⟨ refl⟩∘⟨ first∘first ⟩
          eval′ ∘ first (λg π₂) ∘ first !                               ≈⟨ pullˡ β′ ⟩
          π₂ ∘ first !                                                  ≈⟨ project₂ ⟩
          id ∘ π₂                                                       ≈⟨ identityˡ ⟩
          π₂                                                            ≈˘⟨ project₁ ⟩
          π₁ ∘ swap                                                     ≈˘⟨ refl⟩∘⟨ β′ ⟩
          π₁ ∘ eval′ ∘ first (λg swap)                                  ≈˘⟨ pull-last second∘first ⟩
          (π₁ ∘ eval′ ∘ second id) ∘ first (λg swap)                    ≈˘⟨ pullˡ β′ ⟩
          eval′ ∘ first (λg (π₁ ∘ eval′ ∘ second id)) ∘ first (λg swap) ≈⟨ refl ⟩∘⟨ first∘first ⟩
          eval′ ∘ first (λg (π₁ ∘ eval′ ∘ second id) ∘ λg swap)         ∎

        unit/η : ∀ α → α ⇒ P {X = ⊤} (λg π₂) (A⇨.₁ (π₁ {A} {α}))
        unit/η α = universal (λg π₂) (A⇨.₁ π₁) (λ-unique₂′ (s α))

        unit/commute : ∀ {α β} (f : α ⇒ β) → unit/η β ∘ f ≈ Functor.₁ Coforgetful (Functor.₁ (Free product) f) ∘ unit/η α
        unit/commute {α} {β} f = begin
          universal (λg π₂) (A⇨.₁ π₁) (λ-unique₂′ (s β)) ∘ f
            ≈⟨ unique (λg π₂) (A⇨.₁ π₁) (sym (!-unique (p₁ (λg π₂) (A⇨.₁ π₁) ∘ universal (λg π₂) (A⇨.₁ π₁) (λ-unique₂′ (s β)) ∘ f))) l₁ ⟩
          universal (λg π₂) (A⇨.₁ π₁) (λ-unique₂′ p)
            ≈˘⟨ unique (λg π₂) (A⇨.₁ π₁) (sym (!-unique (p₁ (λg π₂) (A⇨.₁ π₁) ∘ universal (λg π₂) (A⇨.₁ π₁) (Coforgetful.F₁-lemma (Functor.₁ (Free product) f)) ∘ universal (λg π₂) (A⇨.₁ π₁) (λ-unique₂′ (s α))))) l₂ ⟩
          universal (λg π₂) (A⇨.₁ π₁) (Coforgetful.F₁-lemma (Functor.₁ (Free product) f)) ∘ universal (λg π₂) (A⇨.₁ π₁) (λ-unique₂′ (s α))
            ∎
            where
            p : eval′ ∘ first (λg π₂ ∘ !) ≈ eval′ ∘ first (A⇨.₁ π₁ ∘ λg swap ∘ f)
            p = begin
              eval′ ∘ first (λg π₂ ∘ !)                                         ≈˘⟨ refl⟩∘⟨ first∘first ⟩
              eval′ ∘ first (λg π₂) ∘ first !                                   ≈⟨ pullˡ β′ ⟩
              π₂ ∘ first !                                                      ≈⟨ project₂ ⟩
              id ∘ π₂                                                           ≈˘⟨ project₂ ⟩
              π₂ ∘ first f                                                      ≈˘⟨ pullˡ project₁ ⟩
              π₁ ∘ swap ∘ first f                                               ≈⟨ push-center β′ ⟩
              π₁ ∘ eval′ ∘ first (λg swap) ∘ first f                            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ first∘first ⟩
              π₁ ∘ eval′ ∘ first (λg swap ∘ f)                                  ≈˘⟨ pull-last second∘first ⟩
              (π₁ ∘ eval′ ∘ second id) ∘ first (λg swap ∘ f)                    ≈˘⟨ pullˡ β′ ⟩
              eval′ ∘ first (λg (π₁ ∘ eval′ ∘ second id)) ∘ first (λg swap ∘ f) ≈⟨ refl⟩∘⟨ first∘first ⟩
              eval′ ∘ first (λg (π₁ ∘ eval′ ∘ second id) ∘ λg swap ∘ f)         ∎
            
            l₁ : p₂ (λg π₂) (A⇨.₁ π₁) ∘ universal (λg π₂) (A⇨.₁ π₁) (λ-unique₂′ (s β)) ∘ f ≈ λg swap ∘ f
            l₁ = begin
              p₂ (λg π₂) (A⇨.₁ π₁) ∘ universal (λg π₂) (A⇨.₁ π₁) (λ-unique₂′ (s β)) ∘ f ≈⟨ pullˡ (p₂∘universal≈h₂ (λg π₂) (A⇨.₁ π₁)) ⟩
              λg swap ∘ f                                                 ∎

            l₂ : p₂ (λg π₂) (A⇨.₁ π₁) ∘ universal (λg π₂) (A⇨.₁ π₁) (Coforgetful.F₁-lemma (Functor.₁ (Free product) f)) ∘ universal (λg π₂) (A⇨.₁ π₁) (λ-unique₂′ (s α)) ≈ λg swap ∘ f
            l₂ = begin
              p₂ (λg π₂) (A⇨.₁ π₁) ∘ universal (λg π₂) (A⇨.₁ π₁) (Coforgetful.F₁-lemma (Functor.₁ (Free product) f)) ∘ universal (λg π₂) (A⇨.₁ π₁) (λ-unique₂′ (s α))  ≈⟨ extendʳ (p₂∘universal≈h₂ (λg π₂) (A⇨.₁ π₁)) ⟩
              λg (second f ∘ eval′ ∘ second id) ∘ p₂ (λg π₂) (A⇨.₁ π₁) ∘ universal (λg π₂) (A⇨.₁ π₁) (λ-unique₂′ (s α)) ≈⟨ refl⟩∘⟨ p₂∘universal≈h₂ (λg π₂) (A⇨.₁ π₁) ⟩
              λg (second f ∘ eval′ ∘ second id)  ∘ λg swap                                                              ≈⟨ λ-unique₂′ t ⟩
              λg swap ∘ f                                                                                               ∎
              where
                t : eval′ ∘ first (λg (second f ∘ eval′ ∘ second id) ∘ λg swap) ≈ eval′ ∘ first (λg swap ∘ f)
                t = begin
                  eval′ ∘ first (λg (second f ∘ eval′ ∘ second id) ∘ λg swap)         ≈˘⟨ refl⟩∘⟨ first∘first ⟩
                  eval′ ∘ first (λg (second f ∘ eval′ ∘ second id)) ∘ first (λg swap) ≈⟨ pullˡ β′ ⟩
                  (second f ∘ eval′ ∘ second id) ∘ first (λg swap)                    ≈⟨ pull-last second∘first ⟩
                  second f ∘ eval′ ∘ first (λg swap)                                  ≈⟨ refl⟩∘⟨ β′ ⟩
                  second f ∘ swap                                                     ≈˘⟨ swap∘⁂ ⟩
                  swap ∘ first f                                                      ≈˘⟨ pullˡ β′ ⟩
                  eval′ ∘ first (λg swap) ∘ first f                                   ≈⟨ refl⟩∘⟨ first∘first ⟩
                  eval′ ∘ first (λg swap ∘ f)                                         ∎
    {-
        counit/η : (X : SliceObj A) → Slice⇒ (sliceobj {Y = A × P {X = ⊤} (λg π₂) (A⇨.₁ (arr X))} π₁) X 
        counit/η X = record
          { h = {!A⇨.₁ (arr X)!}
          ; △ = {!!}
          }
    -}

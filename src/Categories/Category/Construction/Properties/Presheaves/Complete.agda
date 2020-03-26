{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Category.Construction.Properties.Presheaves.Complete {o ℓ e} (C : Category o ℓ e) where

open import Data.Product
open import Function.Equality using (Π)
open import Relation.Binary

open import Categories.Category.Complete
open import Categories.Category.Construction.Presheaves
open import Categories.Category.Instance.Setoids
open import Categories.Category.Instance.Properties.Setoids
open import Categories.Diagram.Limit as Lim
open import Categories.Functor
open import Categories.NaturalTransformation

import Categories.Category.Construction.Cones as Co
import Relation.Binary.Reasoning.Setoid as SetoidR

private
  module C = Category C
  open C
  open Π using (_⟨$⟩_)

module _ o′ where
  private
    P = Presheaves′ o′ o′ C
    module P = Category P

    module _ {J : Category o′ o′ o′} (F : Functor J P) where
      module J = Category J
      module F = Functor F
      open F
      module F₀ j = Functor (F₀ j)
      module F₁ {a b} (f : a J.⇒ b) = NaturalTransformation (F₁ f)

      F[-,_] : Obj → Functor J (Setoids o′ o′)
      F[-, X ] = record
        { F₀           = λ j → F₀.₀ j X
        ; F₁           = λ f → F₁.η f X
        ; identity     = identity
        ; homomorphism = homomorphism
        ; F-resp-≈     = λ eq → F-resp-≈ eq -- this application cannot be eta reduced
        }

      module LimFX X = Limit (Setoids-Complete _ _ _ o′ o′ F[-, X ])

      module FCone (K : Co.Cone F) where
        open Co.Cone F K public
        module N = Functor N
        module ψ j = NaturalTransformation (ψ j)

      module FCone⇒ {K K′ : Co.Cone F} (K⇒K′ : Co.Cone⇒ F K K′) where
        open Co.Cone⇒ F K⇒K′ public
        module arr = NaturalTransformation arr

      FXcone : ∀ X → (K : Co.Cone F) → Co.Cone F[-, X ]
      FXcone X K = record
        { N    = N.₀ X
        ; apex = record
          { ψ       = λ j → ψ.η j X
          ; commute = λ f → commute f -- this application cannot be eta reduced
          }
        }
        where open FCone K

      ⊤ : Co.Cone F
      ⊤ = record
        { N    = record
          { F₀           = λ X → LimFX.apex X
          ; F₁           = λ {A B} f → record
            { _⟨$⟩_ = λ { (S , eq) → (λ j → F₀.₁ j f ⟨$⟩ S j) , λ {X Y} g →
              let open SetoidR (F₀.₀ Y B)
              in begin
                F₁.η g B ⟨$⟩ (F₀.₁ X f ⟨$⟩ S X) ≈⟨ F₁.commute g f (Setoid.refl (F₀.₀ X A)) ⟩
                F₀.₁ Y f ⟨$⟩ (F₁.η g A ⟨$⟩ S X) ≈⟨ Π.cong (F₀.₁ Y f) (eq g) ⟩
                F₀.₁ Y f ⟨$⟩ S Y ∎ }
            ; cong  = λ eq j → Π.cong (F₀.₁ j f) (eq j)
            }
          ; identity     = λ eq j → F₀.identity j (eq j)
          ; homomorphism = λ eq j → F₀.homomorphism j (eq j)
          ; F-resp-≈     = λ eq eq′ j → F₀.F-resp-≈ j eq (eq′ j)
          }
        ; apex = record
          { ψ       = λ j → ntHelper record
            { η       = λ X → record
              { _⟨$⟩_ = λ { (S , eq) → S j }
              ; cong  = λ eq → eq j
              }
            ; commute = λ f eq → Π.cong (F₀.₁ j f) (eq j)
            }
          ; commute = λ { {Y} {Z} f {W} {S₁ , eq₁} {S₂ , eq₂} eq →
            let open SetoidR (F₀.₀ Z W)
            in begin
              F₁.η f W ⟨$⟩ S₁ Y ≈⟨ eq₁ f ⟩
              S₁ Z              ≈⟨ eq Z ⟩
              S₂ Z              ∎ }
          }
        }

      K⇒⊤′ : ∀ X {K} → Co.Cones F [ K , ⊤ ] → Co.Cones F[-, X ] [ FXcone X K , LimFX.limit X ]
      K⇒⊤′ X {K} K⇒⊤ = record
        { arr     = arr.η X
        ; commute = comm
        }
        where open FCone K
              open FCone⇒ K⇒⊤ renaming (commute to comm)

      complete : Limit F
      complete = record
        { terminal = record
          { ⊤        = ⊤
          ; !        = λ {K} →
            let module K = FCone K
            in record
            { arr     = ntHelper record
              { η       = λ X → LimFX.rep X (FXcone X K)
              ; commute = λ {X Y} f eq j → K.ψ.commute j f eq
              }
            ; commute = λ eq → Π.cong (K.ψ.η _ _) eq
            }
          ; !-unique = λ {K} K⇒⊤ {X} {x y} eq j →
            let module K   = FCone K
                module K⇒⊤ = FCone⇒ K⇒⊤
            in LimFX.terminal.!-unique X (K⇒⊤′ X K⇒⊤) eq j
          }
        }      
  
  Presheaves-Complete : Complete o′ o′ o′ P
  Presheaves-Complete F = complete F

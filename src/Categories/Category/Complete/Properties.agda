{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Category.Complete.Properties {o ℓ e} (C : Category o ℓ e) where

open import Data.Product
open import Relation.Binary

open import Categories.Category.Complete
open import Categories.Category.Construction.Functors
open import Categories.Diagram.Limit as Lim
open import Categories.Diagram.Cone.Properties
open import Categories.Functor
open import Categories.Functor.Properties
open import Categories.NaturalTransformation

import Categories.Category.Construction.Cones as Co
import Categories.Morphism.Reasoning as MR

module _ {o′ ℓ′ e′ o″ ℓ″ e″} {D : Category o′ ℓ′ e′} (Com : Complete o″ ℓ″ e″ D) where
  private
    D^C = Functors C D
    module D^C = Category D^C
    module D   = Category D    
    module C   = Category C

    module _ {J : Category o″ ℓ″ e″} (F : Functor J D^C) where
      module J = Category J
      module F = Functor F
      open F
      module F₀ j = Functor (F₀ j)
      module F₁ {a b} (f : a J.⇒ b) = NaturalTransformation (F₁ f)

      F[-,_] : C.Obj → Functor J D
      F[-, X ] = record
        { F₀           = λ j → F₀.₀ j X
        ; F₁           = λ f → F₁.η f X
        ; identity     = identity
        ; homomorphism = homomorphism
        ; F-resp-≈     = λ eq → F-resp-≈ eq -- this application cannot be eta reduced
        }

      F[-,-] : Functor C (Functors J D)
      F[-,-] = record
        { F₀           = F[-,_]
        ; F₁           = λ f → ntHelper record
          { η       = λ j → F₀.₁ j f
          ; commute = λ g → F₁.sym-commute g f
          }
        ; identity     = F₀.identity _
        ; homomorphism = F₀.homomorphism _
        ; F-resp-≈     = λ eq → F₀.F-resp-≈ _ eq
        }

      module F[-,-] = Functor F[-,-]

      module LimFX X = Limit (Com F[-, X ])
      open LimFX hiding (commute)

      K⇒lim : ∀ {X Y} (f : X C.⇒ Y) K → Co.Cones F[-, Y ] [ nat-map-Cone (F[-,-].₁ f) K , limit Y ]
      K⇒lim f K = rep-cone _ (nat-map-Cone (F[-,-].₁ f) K)

      lim⇒lim : ∀ {X Y} (f : X C.⇒ Y) → Co.Cones F[-, Y ] [ nat-map-Cone (F[-,-].₁ f) (limit X) , limit Y ]
      lim⇒lim f = K⇒lim f (limit _)

      module lim⇒lim {X Y} (f : X C.⇒ Y) = Co.Cone⇒ F[-, Y ] (lim⇒lim f)

      module FCone (K : Co.Cone F) where
        open Co.Cone F K public
        module N   = Functor N
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
          { F₀           = λ X → apex X
          ; F₁           = λ {A B} f → lim⇒lim.arr f
          ; identity     = λ {X} →
            terminal.!-unique X record
            { arr     = D.id
            ; commute = D.identityʳ ○ ⟺ (elimˡ (F₀.identity _))
            }
          ; homomorphism = λ {X Y Z} {f g} →
            terminal.!-unique₂ Z
              {nat-map-Cone (F[-,-].₁ (g C.∘ f)) (limit X)}
              {terminal.! Z}
              {record { commute = λ {j} →
              begin
                proj Z j ∘ lim⇒lim.arr g ∘ lim⇒lim.arr f
                  ≈⟨ pullˡ (lim⇒lim.commute g) ⟩
                (F₀.₁ j g ∘ proj Y j) ∘ lim⇒lim.arr f
                  ≈⟨ pullʳ (lim⇒lim.commute f) ⟩
                F₀.₁ j g ∘ F₀.₁ j f ∘ proj X j
                  ≈˘⟨ pushˡ (F₀.homomorphism j) ⟩
                F₀.₁ j (g C.∘ f) ∘ proj X j
                  ∎ }}
          ; F-resp-≈     = λ {A B} {f g} eq → terminal.!-unique B record
            { commute = lim⇒lim.commute g ○ ∘-resp-≈ˡ (F₀.F-resp-≈ _ (C.Equiv.sym eq)) }
          }
        ; apex = record
          { ψ       = λ j → ntHelper record
            { η       = λ X → proj X j
            ; commute = λ _ → LimFX.commute _
            }
          ; commute = λ f {X} → limit-commute X f
          }
        }
        where open D
              open D.HomReasoning
              open MR D

      K⇒⊤′ : ∀ X {K} → Co.Cones F [ K , ⊤ ] → Co.Cones F[-, X ] [ FXcone X K , LimFX.limit X ]
      K⇒⊤′ X {K} K⇒⊤ = record
        { arr     = arr.η X
        ; commute = comm
        }
        where open FCone⇒ K⇒⊤ renaming (commute to comm)

      complete : Limit F
      complete = record
        { terminal = record
          { ⊤        = ⊤
          ; !        = λ {K} →
            let module K = FCone K
            in record
            { arr     = ntHelper record
              { η       = λ X → rep X (FXcone X K)
              ; commute = λ {X Y} f →
                terminal.!-unique₂ Y
                  {nat-map-Cone (F[-,-].₁ f) (FXcone X K)}
                  {record { commute = λ {j} →
                  begin
                    proj Y j ∘ rep Y (FXcone Y K) ∘ K.N.₁ f ≈⟨ pullˡ (LimFX.commute Y) ⟩
                    K.ψ.η j Y ∘ K.N.F₁ f                    ≈⟨ K.ψ.commute j f ⟩
                    F₀.₁ j f ∘ K.ψ.η j X                    ∎ }}
                  {record { commute = λ {j} →
                  begin
                    proj Y j ∘ lim⇒lim.arr f ∘ rep X (FXcone X K) ≈⟨ pullˡ (lim⇒lim.commute f) ⟩
                    (F₀.₁ j f ∘ proj X j) ∘ rep X (FXcone X K)    ≈⟨ pullʳ (LimFX.commute X) ⟩
                    F₀.₁ j f ∘ K.ψ.η j X                          ∎ }}
              }
            ; commute = λ {_} {X} → LimFX.commute X
            }
          ; !-unique = λ K⇒⊤ {X} → terminal.!-unique X (K⇒⊤′ X K⇒⊤)
          }
        }      
        where open D
              open D.HomReasoning
              open MR D

  Functors-Complete : Complete o″ ℓ″ e″ D^C
  Functors-Complete F = complete F

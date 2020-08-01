{-# OPTIONS --without-K --safe #-}

-- Adjoint Functor Theorem
module Categories.Adjoint.AFT where

open import Level
open import Data.Product
open import Data.Product using (Σ)

open import Categories.Category
open import Categories.Category.Complete
open import Categories.Category.Complete.Properties
open import Categories.Category.Construction.Cones
open import Categories.Category.Construction.Comma
open import Categories.Functor
open import Categories.Functor.Continuous
open import Categories.Adjoint
open import Categories.Adjoint.Properties
open import Categories.Diagram.Limit as Lim
open import Categories.Diagram.Cone.Properties
open import Categories.Morphism as Mor
open import Categories.Morphism.Universal

import Categories.Adjoint.AFT.SolutionSet as SS

private
  variable
    o ℓ e : Level
    C D : Category o ℓ e

module _ {R : Functor C D} where
  private
    module C = Category C
    module D = Category D
    module R = Functor R

    o-level : Level
    o-level = C.o-level ⊔ C.ℓ-level ⊔ D.ℓ-level ⊔ D.e-level

    ℓ-level : Level
    ℓ-level = C.o-level ⊔ C.ℓ-level ⊔ D.ℓ-level ⊔ D.e-level

    e-level : Level
    e-level = C.o-level ⊔ C.ℓ-level ⊔ D.ℓ-level ⊔ D.e-level

  open SS R using (SolutionSet′)

  module _ {L : Functor D C} (L⊣R : L ⊣ R) where
    private
      module L = Functor L
      open Adjoint L⊣R

    L⊣R⇒solutionSet′ : SolutionSet′
    L⊣R⇒solutionSet′ = record
      { S₀      = λ {_ X} _ → L.₀ X
      ; S₁      = Radjunct
      ; ϕ       = λ _ → unit.η _
      ; commute = λ _ → LRadjunct≈id
      }

  module _ (Com  : Complete o-level ℓ-level e-level C)
           (Rcon : Continuous o-level ℓ-level e-level R)
           (s    : SolutionSet′) where
    open SolutionSet′ s
    open D.Equiv
    open D.HomReasoning

    private
      module _ X where
        X↙R : Category (C.o-level ⊔ D.ℓ-level) (C.ℓ-level ⊔ D.e-level) C.e-level
        X↙R = X ↙ R
        module X↙R = Category X↙R

        s′ : SolutionSet X↙R 
        s′ = record
          { D   = D′
          ; arr = arr′
          }
          where D′ : X↙R.Obj → X↙R.Obj
                D′ Z = record
                  { f = ϕ Z.f
                  }
                  where module Z = CommaObj Z

                arr′ : ∀ Z → X↙R [ D′ Z , Z ]
                arr′ Z = record
                  { h       = S₁ Z.f
                  ; commute = commute _ ○ ⟺ D.identityʳ
                  }
                  where module Z = CommaObj Z
                        open D.HomReasoning

        module _ {J : Category o-level ℓ-level e-level} (F : Functor J X↙R) where
          module J = Category J
          module F = Functor F

          F′ : Functor J C
          F′ = record
            { F₀           = λ j → CommaObj.β (F.₀ j)
            ; F₁           = λ f → Comma⇒.h (F.₁ f)
            ; identity     = proj₂ F.identity 
            ; homomorphism = proj₂ F.homomorphism
            ; F-resp-≈     = λ eq → proj₂ (F.F-resp-≈ eq)
            }

          LimF′ : Limit F′
          LimF′ = Com F′
          module LimF′ = Limit LimF′

          RLimF′ : Cone (R ∘F F′)
          RLimF′ = F-map-Coneˡ R LimF′.limit
          module RLimF′ = Cone _ RLimF′

          LimRF′₁ : Limit (R ∘F F′)
          LimRF′₁ = proj₁ (Rcon LimF′)
          module LimRF′₁ = Limit LimRF′₁

          lim-equiv : _≅_ D (R.₀ LimF′.apex) (LimRF′₁.apex)
          lim-equiv = proj₂ (Rcon LimF′)

          LimRF′₂ : Limit (R ∘F F′)
          LimRF′₂ = transport-by-iso _ LimRF′₁ (≅.sym _ lim-equiv)
          module LimRF′₂ = Limit LimRF′₂

          coneF : Cone (R ∘F F′)
          coneF = record
            { N    = X
            ; apex = record
              { ψ       = λ j → CommaObj.f (F.₀ j)
              ; commute = λ f → Comma⇒.commute (F.₁ f) ○ D.identityʳ
              }
            }

          ⊤-arr : Cone⇒ (R ∘F F′) coneF LimRF′₂.limit
          ⊤-arr = LimRF′₂.rep-cone coneF
          module ⊤-arr = Cone⇒ (R ∘F F′) ⊤-arr

          ⊤ : Cone F
          ⊤ = record
            { N    = record
              { f = ⊤-arr.arr
              }
            ; apex = record
              { ψ       = λ j → record
                { h       = LimF′.proj j
                ; commute = begin
                  R.₁ (LimF′.proj j) D.∘ ⊤-arr.arr ≈⟨ {!!} ⟩∘⟨refl ⟩
                  LimRF′₂.proj j D.∘ ⊤-arr.arr      ≈⟨ ⊤-arr.commute ⟩
                  CommaObj.f (F.₀ j)               ≈˘⟨ D.identityʳ ⟩
                  CommaObj.f (F.₀ j) D.∘ D.id      ∎
                }
              ; commute = λ f → -, LimF′.limit-commute f
              }
            }

    --       complete : Limit F
    --       complete = record
    --         { terminal = record
    --           { ⊤        = ⊤
    --           ; !        = {!!}
    --           ; !-unique = {!!}
    --           }
    --         }

    -- --     solutionSet′⇒universalMorphism : UniversalMorphism X R
    -- --     solutionSet′⇒universalMorphism = record
    -- --       { initial = SolutionSet⇒Initial {o′ = 0ℓ} {0ℓ} {0ℓ} {C = X ↙ R} complete s′
    -- --       }

    -- -- solutionSet⇒adjoint : Σ (Functor D C) (λ L → L ⊣ R)
    -- -- solutionSet⇒adjoint = universalMophisms⇒adjoint solutionSet′⇒universalMorphism

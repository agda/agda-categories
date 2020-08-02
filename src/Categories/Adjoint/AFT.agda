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
open import Categories.Functor.Limits
open import Categories.Functor.Properties
open import Categories.Adjoint
open import Categories.Adjoint.Properties
open import Categories.Diagram.Limit as Lim
open import Categories.Diagram.Cone.Properties
open import Categories.Morphism as Mor
open import Categories.Morphism.Universal

import Categories.Adjoint.AFT.SolutionSet as SS
import Categories.Morphism.Reasoning as MR

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
    open MR D

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
          F′ = Cod _ _ ∘F F

          LimF′ : Limit F′
          LimF′ = Com F′
          module LimF′ = Limit LimF′

          RLimF′ : Cone (R ∘F F′)
          RLimF′ = F-map-Coneˡ R LimF′.limit
          module RLimF′ = Cone _ RLimF′

          LimRF′ : Limit (R ∘F F′)
          LimRF′ = record
            { terminal = record
              { ⊤             = RLimF′
              ; ⊤-is-terminal = Rcon LimF′
              }
            }
          module LimRF′ = Limit LimRF′

          coneF : Cone (R ∘F F′)
          coneF = record
            { N    = X
            ; apex = record
              { ψ       = λ j → CommaObj.f (F.₀ j)
              ; commute = λ f → Comma⇒.commute (F.₁ f) ○ D.identityʳ
              }
            }

          ⊤-arr : Cone⇒ (R ∘F F′) coneF RLimF′
          ⊤-arr = LimRF′.rep-cone coneF
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
                  R.₁ (LimF′.proj j) D.∘ ⊤-arr.arr ≈⟨ ⊤-arr.commute ⟩
                  CommaObj.f (F.₀ j)               ≈˘⟨ D.identityʳ ⟩
                  CommaObj.f (F.₀ j) D.∘ D.id      ∎
                }
              ; commute = λ f → -, LimF′.limit-commute f
              }
            }

          K-conv : Cone F → Cone F′
          K-conv = F-map-Coneˡ (Cod _ _)

          K-conv′ : Cone F → Cone (R ∘F F′)
          K-conv′ K = F-map-Coneˡ R (K-conv K)

          ! : (K : Cone F) → Cones F [ K , ⊤ ]
          ! K = record
            { arr     = record
              { h       = LimF′.rep (K-conv K)
              ; commute = ⟺ (LimRF′.terminal.!-unique (record
                { arr     = R.₁ (LimF′.rep (K-conv K)) D.∘ CommaObj.f N
                ; commute = λ {j} → begin
                  LimRF′.proj j D.∘ R.₁ (LimF′.rep (K-conv K)) D.∘ CommaObj.f N
                    ≈⟨ pullˡ ([ R ]-resp-∘ LimF′.commute) ⟩
                  R.₁ (Comma⇒.h (ψ j)) D.∘ CommaObj.f N
                    ≈⟨ Comma⇒.commute (ψ j) ⟩
                  CommaObj.f (F.F₀ j) D.∘ D.id
                    ≈⟨ D.identityʳ ⟩
                  CommaObj.f (F.₀ j)
                    ∎
                })) ○ ⟺ D.identityʳ
              }
            ; commute = -, LimF′.commute
            }
            where open Cone _ K

          !-unique : {K : Cone F} (f : Cones F [ K , ⊤ ]) → Cones F [ ! K ≈ f ]
          !-unique f = -, LimF′.terminal.!-unique record
            { arr     = Comma⇒.h f.arr
            ; commute = proj₂ f.commute
            }
            where module f = Cone⇒ _ f

          complete : Limit F
          complete = record
            { terminal = record
              { ⊤             = ⊤
              ; ⊤-is-terminal = record
                { !        = ! _
                ; !-unique = !-unique
                }
              }
            }

        solutionSet′⇒universalMorphism : UniversalMorphism X R
        solutionSet′⇒universalMorphism = record
          { initial = SolutionSet⇒Initial {o′ = 0ℓ} {0ℓ} {0ℓ} {C = X ↙ R} complete s′
          }

    solutionSet⇒adjoint : Σ (Functor D C) (λ L → L ⊣ R)
    solutionSet⇒adjoint = universalMophisms⇒adjoint solutionSet′⇒universalMorphism

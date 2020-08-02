{-# OPTIONS --without-K --safe #-}

module Categories.Adjoint.Equivalence.Properties where

open import Level

open import Categories.Category
open import Categories.Adjoint.Equivalence
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Properties
open import Categories.NaturalTransformation.NaturalIsomorphism as ≃ using (_≃_; NaturalIsomorphism)

import Categories.Morphism.Reasoning as MR
import Categories.Category.Construction.Cones as Co
import Categories.Diagram.Limit as Lim

private
  variable
    o ℓ e : Level
    C D E : Category o ℓ e

-- diagrams are preserved by adjoint equivalence
--
-- if categories C and D are adjoint equivalent, then a limit from one determines one from another
module _  (⊣equiv : ⊣Equivalence C D) (F : Functor C E) where
  private
    module LF where
      open Co F public
      open Lim F public
    module C = Category C
    module D = Category D
    module E = Category E
    module F = Functor F
    module ⊣equiv = ⊣Equivalence ⊣equiv
    open ⊣equiv
    open E
    open MR E
    open HomReasoning
    open LF
    
    FR = F ∘F R

    module LFR where
      open Co FR public
      open Lim FR public

  module _ (Lm : Limit) where
    private
      module Lm = Lim.Limit Lm
      open Lm
  
      ⊤cone : LFR.Cone
      ⊤cone = record
        { N    = Lm.apex
        ; apex = record
          { ψ       = λ d → proj (R.₀ d)
          ; commute = λ f → limit-commute (R.₁ f)
          }
        }
  
      module _ {K : LFR.Cone} where
        private
          module K = LFR.Cone K

        K′ : Cone
        K′ = record
          { N    = K.N
          ; apex = record
            { ψ       = λ c → F.₁ (unit.⇐.η c) ∘ K.ψ (L.₀ c)
            ; commute = λ {X} {Y} f → begin
              F.₁ f ∘ F.₁ (unit.⇐.η X) ∘ K.ψ (L.₀ X)                         ≈˘⟨ pushˡ ([ F ]-resp-square (unit.⇐.commute f)) ⟩
              (F.₁ (unit.⇐.η Y) ∘ F.₁ (Functor.F₁ (R ∘F L) f)) ∘ K.ψ (L.₀ X) ≈⟨ pullʳ (K.commute (L.₁ f)) ⟩
              F.₁ (unit.⇐.η Y) ∘ K.ψ (L.₀ Y)                                 ∎
            }
          }

        !cone : LFR.Cones [ K , ⊤cone ]
        !cone = record
          { arr     = rep K′
          ; commute = λ {d} → begin
            proj (R.₀ d) ∘ rep K′                          ≈⟨ commute ⟩
            F.₁ (unit.⇐.η (R.₀ d)) ∘ K.ψ (L.₀ (R.₀ d))     ≈˘⟨ F.F-resp-≈ (MR.flip-fromʳ C unit.FX≅GX zag) ⟩∘⟨refl ⟩
            (F.₁ (R.₁ (counit.⇒.η d)) ∘ K.ψ (L.₀ (R.₀ d))) ≈⟨ K.commute (counit.⇒.η d) ⟩
            K.ψ d                                          ∎
          }

      module _ {K : LFR.Cone} (f : LFR.Cones [ K , ⊤cone ]) where
        private
          module K = LFR.Cone K
          module f = LFR.Cone⇒ f

        !cone-unique : LFR.Cones [ !cone ≈ f ]
        !cone-unique = begin
          rep (K′ {K}) ≈⟨ terminal.!-unique {K′ {K}} (record { arr = f.arr ; commute = eq }) ⟩
          f.arr        ∎
          where eq : ∀ {c} → proj c ∘ f.arr ≈ F.₁ (unit.⇐.η c) ∘ K.ψ (L.₀ c)
                eq {c} = begin
                  proj c ∘ f.arr                                ≈˘⟨ pullˡ (limit-commute (unit.⇐.η c)) ⟩
                  F.₁ (unit.⇐.η c) ∘ proj (R.₀ (L.₀ c)) ∘ f.arr ≈⟨ refl⟩∘⟨ f.commute ⟩
                  F.₁ (unit.⇐.η c) ∘ K.ψ (L.₀ c)                ∎

    ⊣equiv-preserves-diagram : Lim.Limit FR
    ⊣equiv-preserves-diagram = record
      { terminal = record
        { ⊤             = ⊤cone
        ; ⊤-is-terminal = record
          { !        = !cone
          ; !-unique = !cone-unique
          }
        }
      }
  

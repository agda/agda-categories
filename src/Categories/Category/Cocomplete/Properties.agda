{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Category.Cocomplete.Properties {o ℓ e} (C : Category o ℓ e) where

open import Level
open import Data.Product using (_,_)

open import Categories.Adjoint.Properties
open import Categories.Category.Complete
open import Categories.Category.Complete.Properties
open import Categories.Category.Cocomplete
open import Categories.Category.Cocomplete.Finitely
open import Categories.Category.Duality
open import Categories.Category.Construction.Functors
open import Categories.Functor
open import Categories.Functor.Duality
open import Categories.NaturalTransformation as N
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_)
open import Categories.Diagram.Limit
open import Categories.Diagram.Limit.Properties
open import Categories.Diagram.Colimit
open import Categories.Diagram.Duality

import Categories.Morphism.Reasoning as MR

private
  variable
    o′ ℓ′ e′ o″ ℓ″ e″ : Level
  module C = Category C
    
Cocomplete⇒FinitelyCocomplete : Cocomplete o′ ℓ′ e′ C → FinitelyCocomplete C
Cocomplete⇒FinitelyCocomplete Coc =
  coFinitelyComplete⇒FinitelyCocomplete C (Complete⇒FinitelyComplete C.op (Cocomplete⇒coComplete C Coc))

module _ {D : Category o′ ℓ′ e′} (Coc : Cocomplete o″ ℓ″ e″ D) where
  private
    module D = Category D

  Functors-Cocomplete : Cocomplete o″ ℓ″ e″ (Functors C D)
  Functors-Cocomplete {J} F = coLimit⇒Colimit (Functors C D) LFop
    where module J = Category J
          module F = Functor F
          open Functor F
          F′ : Functor J.op (Functors C.op D.op)
          F′ = opF⇒ ∘F F.op
  
          L : (H : Functor J.op (Functors C.op D.op)) → Limit H
          L = Functors-Complete C.op {D = D.op} (λ G → Colimit⇒coLimit D (Coc (Functor.op G)))
  
          LF′ : Limit F′
          LF′ = L F′
  
          LF″ : Limit (opF⇐ ∘F F′)
          LF″ = rapl (Functorsᵒᵖ-equiv.L⊣R C.op D.op) F′ LF′
  
          iso : opF⇐ ∘F F′ ≃ F.op
          iso = record
            { F⇒G = ntHelper record
              { η       = λ _ → N.id
              ; commute = λ f → id-comm
              }
            ; F⇐G = ntHelper record
              { η       = λ _ → N.id
              ; commute = λ f → id-comm
              }
            ; iso = λ j → record
              { isoˡ = D.identity²
              ; isoʳ = D.identity²
              }
            }
            where open MR D
  
          LFop : Limit op
          LFop = ≃-resp-lim iso LF″

  -- TODO: need to refactor the where block above to show cocontinuous. there is no need to do it now.
  -- 
  -- evalF-Cocontinuous : ∀ X → Cocontinuous o″ ℓ″ e″ (evalF C D X)
  -- evalF-Cocontinuous X {J} {F} L = Coc (evalF C D X ∘F F) , {!!}
  --   where 

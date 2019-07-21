{-# OPTIONS --without-K --safe #-}

module Categories.NaturalTransformation.Properties where

open import Level
open import Data.Product using (Σ; _,_)

open import Categories.Category
open import Categories.Category.Product
open import Categories.Category.Construction.Functors
open import Categories.Functor
open import Categories.Functor.Bifunctor
open import Categories.NaturalTransformation
open import Categories.NaturalTransformation.NaturalIsomorphism hiding (_≅_)
open import Categories.NaturalTransformation.Dinatural
import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e : Level
    C D   : Category o ℓ e

module _ {F G : Functor C D} where
  private
    module C = Category C
    module D = Category D
    open D
    open MR D
    open HomReasoning
    open Functor

    F′ : Bifunctor C.op C D
    F′ = F ∘F πʳ

    G′ : Bifunctor C.op C D
    G′ = G ∘F πʳ

  NT⇒Dinatural : NaturalTransformation F G → DinaturalTransformation F′ G′
  NT⇒Dinatural β = record
    { α       = η
    ; commute = λ f → ∘-resp-≈ʳ (elimʳ (identity F)) ○ ⟺ (commute f) ○ introˡ (identity G)
    }
    where open NaturalTransformation β

  Dinatural⇒NT : DinaturalTransformation F′ G′ → NaturalTransformation F G
  Dinatural⇒NT θ = record
    { η       = α
    ; commute = λ f → introˡ (identity G) ○ ⟺ (commute f) ○ ∘-resp-≈ʳ (elimʳ (identity F))
    }
    where open DinaturalTransformation θ

  -- isomorphism in Functors category is the same as natural isomorphism
  module _ where
    open Mor (Functors C D)
  
    Functors-iso⇒NI : F ≅ G → NaturalIsomorphism F G
    Functors-iso⇒NI F≅G = record
      { F⇒G = from
      ; F⇐G = to
      ; iso = λ X → record
        { isoˡ = isoˡ
        ; isoʳ = isoʳ
        }
      }
      where open Mor._≅_ F≅G
    
    NI⇒Functors-iso : NaturalIsomorphism F G → F ≅ G
    NI⇒Functors-iso α = record
      { from = F⇒G
      ; to   = F⇐G
      ; iso  = record
        { isoˡ = isoˡ (iso _)
        ; isoʳ = isoʳ (iso _)
        }
      }
      where open NaturalIsomorphism α
            open Mor.Iso


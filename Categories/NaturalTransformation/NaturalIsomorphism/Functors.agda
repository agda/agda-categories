{-# OPTIONS --without-K --safe #-}

module Categories.NaturalTransformation.NaturalIsomorphism.Functors where

open import Level

open import Categories.Category
open import Categories.Category.Construction.Functors
open import Categories.Functor
open import Categories.NaturalTransformation.NaturalIsomorphism

import Categories.Morphism as Mor

private
  variable
    o ℓ e : Level
    C D : Category o ℓ e

-- isomorphism in Functors category is the same as natural isomorphism
module _ {F G : Functor C D} where
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

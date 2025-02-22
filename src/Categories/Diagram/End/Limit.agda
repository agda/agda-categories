{-# OPTIONS --safe --without-K #-}

module Categories.Diagram.End.Limit where

open import Level

open import Categories.Category using (Category)
open import Categories.Category.Construction.TwistedArrow using (Codomain)
open import Categories.Category.Equivalence as SE using (StrongEquivalence)
open import Categories.Category.Equivalence.Preserves using (pres-Terminal)
open import Categories.Diagram.End using () renaming (End to ∫)
open import Categories.Diagram.End.Properties using (End⇒Terminal; Terminal⇒End; end-η; end-unique; end-identity; end-η-resp-≈; end-η-resp-∘)
open import Categories.Diagram.Limit using (Limit)
open import Categories.Diagram.Limit.Properties using (≃-resp-lim)
open import Categories.Diagram.Wedge using (module Wedge-Morphism)
open import Categories.Diagram.Wedge.Properties using (ConesTwist≅Wedges)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Instance.Twisted using (Twist; Twistⁿⁱ)
open import Categories.Functor.Limits using (Continuous)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ᵥ_) renaming (id to idN)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism; sym-associator) renaming (_≃_ to _≃ⁱ_)
open import Categories.Object.Terminal as Terminal

import Categories.Category.Construction.Wedges as Wedges
import Categories.Morphism as M

private
  variable
    o ℓ e : Level
    C D E : Category o ℓ e

-- The real start of the End Calculus. Maybe need to move such properties elsewhere?
-- This is an unpacking of the lhs of Eq. (25) of Loregian's book.
module _ (F : Bifunctor (Category.op C) C D) where
  private
    Eq = ConesTwist≅Wedges F
    module O = M D
  open M (Wedges.Wedges F)
  open Functor

  open StrongEquivalence Eq renaming (F to F⇒; G to F⇐)

  End-yields-limit : ∫ F → Limit (Twist C D F)
  End-yields-limit ef = record { terminal = pres-Terminal (SE.sym Eq) (End⇒Terminal F ef) }

  limit-yields-End : Limit (Twist C D F) → ∫ F
  limit-yields-End l = Terminal⇒End F (pres-Terminal Eq (Limit.terminal l))

  -- Ends and Limits are equivalent, in the category Wedge F
  End-as-Limit : (end : ∫ F) → (l : Limit (Twist C D F)) → ∫.wedge end ≅ F₀ F⇒ (Limit.terminal.⊤ l)
  End-as-Limit end l = Terminal.up-to-iso (Wedges.Wedges F) (End⇒Terminal F end) (pres-Terminal Eq terminal)
    where
    open Limit l

  -- Which then induces that the objects, in D, are also equivalent.
  End-as-Limit-on-Obj : (end : ∫ F) → (l : Limit (Twist C D F)) → ∫.E end O.≅ Limit.apex l
  End-as-Limit-on-Obj end l = record
    { from = Wedge-Morphism.u (M._≅_.from X≅Y)
    ; to = Wedge-Morphism.u (M._≅_.to X≅Y)
    ; iso = record
      { isoˡ = M._≅_.isoˡ X≅Y
      ; isoʳ = M._≅_.isoʳ X≅Y
      }
    }
    where
      X≅Y = End-as-Limit end l
      open Category D

-- A stronger form of Categories.Diagram.End.Properties.end-resp-≅
module _ {F G : Bifunctor (Category.op C) C D} (F≃G : F ≃ⁱ G) where
  ≅-yields-end : ∫ F → ∫ G
  ≅-yields-end ef = limit-yields-End G (≃-resp-lim (Twistⁿⁱ C D F≃G) (End-yields-limit F ef))

-- continuous functors preserve ends
module _ {C : Category o ℓ e}
         (J : Bifunctor (Category.op C) C D) (F : Functor D E)
         {cont : Continuous (o ⊔ ℓ) (ℓ ⊔ e) e F} where
  open Category E
  open M E
  open _≅_
  open Iso
  open ∫ hiding (E)
  private
    module F = Functor F
    module J = Bifunctor J
    module E = Category E
  -- i don't have a better name for this
  -- the converse follows only if J reflects limits
  open import Categories.Diagram.Cone.Properties
  open import Categories.Diagram.Limit.Properties

  module _ (ej : ∫ J) where
    private
      module ej = ∫ ej
      j-limit : Limit (Twist C D J)
      j-limit = End-yields-limit J ej
      --new-limit
      f-limit : Limit (F ∘F (J ∘F Codomain C))
      f-limit .Limit.terminal = record
        { ⊤ = F-map-Coneˡ F (Limit.limit j-limit)
        ; ⊤-is-terminal = cont j-limit
        }
      -- for this we merely need to transport across the associator
      f-limit′ : Limit (Twist C E (F ∘F J))
      f-limit′ = ≃-resp-lim (sym-associator (Codomain C) J F) f-limit

    -- really we want IsEnd `F.₀ (∫.E ej)` (F ∘F J)
    contF-as-end : ∫ (F ∘F J)
    contF-as-end = limit-yields-End (F ∘F J) f-limit′
    _ : F.₀ (∫.E ej) ≅ (∫.E contF-as-end)
    _ =  ≅.refl

  Continuous-pres-End : {ej : ∫ J} {ef : ∫ (F ∘F J)} → F.₀ (∫.E ej) ≅ ∫.E ef
  Continuous-pres-End {ej} {ef} = end-unique (contF-as-end ej) ef

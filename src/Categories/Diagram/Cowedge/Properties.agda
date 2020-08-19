{-# OPTIONS --without-K --safe #-}

-- Constructions of a Cocone from the Twisted Arrow function from a Cowedge
-- and vice-versa, by Duality.
-- Note that the proper functioning of this relies crucially on
-- Functor.op (Functor.op F) being definitionally equal to F.

open import Categories.Category using (Category)
open import Categories.Functor.Bifunctor using (Bifunctor)

module Categories.Diagram.Cowedge.Properties {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′}
  (F : Bifunctor (Category.op C) C D) where

open import Level

open import Categories.Category.Construction.Cocones using (Cocones)
open import Categories.Category.Construction.Cowedges
open import Categories.Category.Construction.TwistedArrow
open import Categories.Category.Equivalence using (StrongEquivalence)
open import Categories.Diagram.Cocone
open import Categories.Diagram.Cowedge
open import Categories.Diagram.Duality
open import Categories.Diagram.Wedge.Properties
open import Categories.Functor hiding (id)
open import Categories.Functor.Instance.Twisted C D
import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation.Dinatural
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)

Cowedge-to-Cocone : (W : Cowedge F) → Cocone (Twist′ F)
Cowedge-to-Cocone W = coCone⇒Cocone D (Wedge-to-Cone (Functor.op F) (Cowedge⇒coWedge D W))

Cocone-to-Cowedge : Cocone (Twist′ F) → Cowedge F
Cocone-to-Cowedge C = coWedge⇒Cowedge D (Cone-to-Wedge (Functor.op F) (Cocone⇒coCone D C))

CooneTwist⇒CowedgeF : Functor (Cocones (Twist′ F)) (Cowedges F)
CooneTwist⇒CowedgeF = record
  { F₀ = Cocone-to-Cowedge
  ; F₁ = λ co⇒ → record { u = arr co⇒ ; commute = commute co⇒ }
  ; identity = Equiv.refl
  ; homomorphism = Equiv.refl
  ; F-resp-≈ = λ f≈g → f≈g
  }
  where
  open Cocone⇒
  open Category D

Cowedge⇒CoconeTwistF : Functor (Cowedges F) (Cocones (Twist′ F))
Cowedge⇒CoconeTwistF = record
  { F₀ = Cowedge-to-Cocone
  ; F₁ = λ we⇒ → record
    { arr = u we⇒
    ; commute = pullˡ (commute we⇒)
    }
  ; identity = Equiv.refl
  ; homomorphism = Equiv.refl
  ; F-resp-≈ = λ f≈g → f≈g
  }
  where
  open Cowedge
  open Cowedge-Morphism
  open Category D
  open MR D

-- The duality here is not just 'op', so spell out some of it.  Note how the proofs need the explicit commutations.
Cowedges≅CoconesTwist : StrongEquivalence (Cowedges F) (Cocones (Twist′ F))
Cowedges≅CoconesTwist = record
  { F = Cowedge⇒CoconeTwistF
  ; G = CooneTwist⇒CowedgeF
  ; weak-inverse = record
    { F∘G≈id = niHelper (record
      { η = λ X → record { arr = id ; commute = λ {Y} → identityˡ ○ Coapex.commute (coapex X) (mor⇒ (MR.elimˡ C C.identity²)) }
      ; η⁻¹ = λ X → record { arr = id ; commute = λ {Y} → identityˡ ○ Equiv.sym (Coapex.commute (coapex X) (mor⇒ (MR.elimˡ C C.identity²))) }
      ; commute = λ _ → MR.id-comm-sym D
      ; iso = λ X → record { isoˡ = identity² ; isoʳ = identity² }
      })
    ; G∘F≈id = niHelper (record
      { η = λ X → record { u = id ; commute = identityˡ ○ MR.elimʳ D identity }
      ; η⁻¹ = λ X → record { u = id ; commute = MR.id-comm-sym D ○ (refl⟩∘⟨ Equiv.sym identity) }
      ; commute = λ _ → MR.id-comm-sym D
      ; iso = λ _ → record { isoˡ = identity² ; isoʳ = identity² }
      })
    }
  }
  where
  module C = Category C
  open Category D
  open HomReasoning
  open Cocone
  open Functor F
  open Cowedge
  open DinaturalTransformation

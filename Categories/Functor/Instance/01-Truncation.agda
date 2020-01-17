{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Instance.01-Truncation where

-- (0,1)-trucation of categories as a functor from Cats to Posets.
--
-- This is the right-adjoint of the inclusion functor from Posets to
-- Cats (see Categories.Functor.Adjoint.Instance.01-Truncation)

open import Level using (_⊔_)
open import Function using (flip)
open import Data.Product as Prod using (_,_; _×_)
open import Relation.Binary.OrderMorphism using (_⇒-Poset_)
open import Relation.Binary using (Poset)

open import Categories.Category using (Category; _[_≈_])
open import Categories.Functor hiding (id)
open import Categories.Category using (Category)
open import Categories.Category.Instance.Cats using (Cats)
open import Categories.Category.Instance.Posets using (Posets)
import Categories.Morphism as Morphism
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (NaturalIsomorphism; _≃_)

Trunc : ∀ {o ℓ e} → Functor (Cats o ℓ e) (Posets o ℓ ℓ)
Trunc {o} {ℓ} {e} = record
   { F₀           = Trunc₀
   ; F₁           = Trunc₁
   ; identity     = λ {C} → id C , id C
   ; homomorphism = λ {_ _ C} → id C , id C
   ; F-resp-≈     = TruncRespNI
   }
   where
     open Functor

     -- The choice of _≈_ below may seem a bit arbitrary.  The
     -- rationale is as follows:
     --
     -- Since we are defining an Agda stdlib-style poset, we have to
     -- pick an equality on the carrier set, i.e. on objects.  But
     -- objects do not come with an equality in this library (that's
     -- considered evil), so we pick isomorphism.  In a poset, any
     -- pair of morphisms f : X ⇒ Y and g : Y ⇒ X constitute an
     -- isomorphism between X and Y.  Hence the definition of _≈_.

     Trunc₀ : Category o ℓ e → Poset o ℓ ℓ
     Trunc₀ C = record
       { Carrier           = Obj
       ; _≈_               = λ x y → x ⇒ y × y ⇒ x
       ; _≤_               = _⇒_
       ; isPartialOrder    = record
         { isPreorder      = record
           { isEquivalence = record
             { refl        = id , id
             ; sym         = Prod.swap
             ; trans       = Prod.zip (flip _∘_) _∘_
             }
           ; reflexive     = Prod.proj₁
           ; trans         = flip _∘_
           }
         ; antisym         = _,_
         }
       }
       where open Category C

     Trunc₁ : ∀ {C D} → Functor C D → Trunc₀ C ⇒-Poset Trunc₀ D
     Trunc₁ F = record { fun = F₀ F ; monotone = F₁ F }

     TruncRespNI : ∀ {C D : Category o ℓ e} {F G : Functor C D} →
                   F ≃ G → Posets o ℓ ℓ [ Trunc₁ F ≈ Trunc₁ G ]
     TruncRespNI μ {X} = ⇒.η X , ⇐.η X
       where open NaturalIsomorphism μ

     open Category

{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Instance.0-Truncation where

-- 0-trucation of groupoids as a functor from Groupoids to Setoids.
--
-- This is the right-adjoint of the inclusion functor from Setoids to
-- Groupoids (see Categories.Functor.Adjoint.Instance.ZeroTruncation)
--
open import Function.Bundles using (Func)
open import Relation.Binary using (Setoid)

open import Categories.Category using (Category; _[_≈_])
open import Categories.Functor using (Functor)
open import Categories.Category.Groupoid using (Groupoid)
open import Categories.Category.Instance.Groupoids using (Groupoids)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (NaturalIsomorphism; _≃_)

Trunc : ∀ {o ℓ e} → Functor (Groupoids o ℓ e) (Setoids o ℓ)
Trunc {o} {ℓ} {e} = record
   { F₀           = TruncSetoid
   ; F₁           = λ {G H} F → TruncMap {G} {H} F
   ; identity     = λ {A} → Category.id (category A)
   ; homomorphism = λ {_} {_} {Z} → Category.id (category Z)
   ; F-resp-≈     = λ {G H} → TruncRespNI {G} {H}
   }
   where
     open Groupoid using (category)
     open Functor

     TruncSetoid : Groupoid o ℓ e → Setoid o ℓ
     TruncSetoid G = record
       { Carrier       = Obj
       ; _≈_           = _⇒_
       ; isEquivalence = record
         { refl  = id
         ; sym   = _⁻¹
         ; trans = λ f g → g ∘ f
         }
       }
       where open Groupoid G

     TruncMap : ∀ {G H} → Functor (category G) (category H) →
                Func (TruncSetoid G) (TruncSetoid H)
     TruncMap F = record { to = F₀ F ; cong  = F₁ F }

     TruncRespNI : ∀ {G H : Groupoid o ℓ e}
                   {E F : Functor (category G) (category H)} →
                   E ≃ F → Setoids o ℓ [ TruncMap {G} {H} E ≈ TruncMap {G} {H} F ]
     TruncRespNI {_} {H} {_} {F} μ {a} = ⇒.η a
       where
         open Groupoid H
         open NaturalIsomorphism μ

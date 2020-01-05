{-# OPTIONS --without-K --safe #-}
module Categories.Category.Instance.Groupoids where

-- The category of groupoids.
--
-- This category should maybe be called "Ho(Groupoids)" or "Ho(Gpd)"
-- instead.  The "homsets" are not the "usual" ones consisting of
-- functors, but consist instead of equivalence classes of functors up
-- to natural isomorphism.  This is because homsets here are really
-- hom-setoids and we pick natural isomorphism as the equivalence
-- relation for these setoids.
--
-- See https://ncatlab.org/nlab/show/Ho%28Cat%29

open import Level
open import Categories.Category
open import Categories.Category.Groupoid
open import Categories.Functor as Fctr using (Functor; _∘F_)
open import Categories.Functor.Properties using ([_]-resp-Iso)
import Categories.Morphism.IsoEquiv as IsoEquiv
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (NaturalIsomorphism; associator; unitorˡ; unitorʳ; unitor²; isEquivalence; _ⓘₕ_; sym)
private
  variable
    o ℓ e : Level

open Groupoid using (category)

-- The category of groupoids.

Groupoids : ∀ o ℓ e → Category (suc (o ⊔ ℓ ⊔  e)) (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
Groupoids o ℓ e = record
  { Obj       = Groupoid o ℓ e
  ; _⇒_       = λ G H → Functor (category G) (category H)
  ; _≈_       = NaturalIsomorphism
  ; id        = Fctr.id
  ; _∘_       = _∘F_
  ; assoc     = λ {_ _ _ _ F G H} → associator F G H
  ; sym-assoc = λ {_ _ _ _ F G H} → sym (associator F G H)
  ; identityˡ = unitorˡ
  ; identityʳ = unitorʳ
  ; identity² = unitor²
  ; equiv     = isEquivalence
  ; ∘-resp-≈  = _ⓘₕ_
  }

module _ {o ℓ e o′ ℓ′ e′} {G : Groupoid o ℓ e} {H : Groupoid o′ ℓ′ e′}
         (F : Functor (category G) (category H))
         where

  private
    module G = Groupoid G
    module H = Groupoid H
  open Functor F
  open IsoEquiv (category H) using (to-unique)

  -- Functors preserve inverses

  F-resp-⁻¹ : ∀ {A B} (f : A G.⇒ B) → F₁ (f G.⁻¹) H.≈ (F₁ f) H.⁻¹
  F-resp-⁻¹ f = to-unique ([ F ]-resp-Iso G.iso) H.iso H.Equiv.refl

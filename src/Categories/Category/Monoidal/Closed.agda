{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Monoidal

-- the definition used here is not very similar to what one usually sees in nLab or
-- any textbook.  the difference is that usually closed monoidal category is defined
-- through a right adjoint of -⊗X, which is [X,-]. then there is an induced bifunctor
-- [-,-].
--
-- but in proof relevant context, the induced bifunctor [-,-] does not have to be
-- exactly the intended bifunctor! in fact, one can probably only show that the
-- intended bifunctor is only naturally isomorphic to the induced one, which is
-- significantly weaker.
--
-- the approach taken here as an alternative is to BEGIN with a bifunctor
-- already. however, is it required to have mates between any given two adjoints. this
-- definition can be shown equivalent to the previous one but just works better.
module Categories.Category.Monoidal.Closed {o ℓ e} {C : Category o ℓ e} (M : Monoidal C) where

private
  module C = Category C
  open Category C

  variable
    X Y A B : Obj

open import Level
open import Data.Product using (_,_)

open import Categories.Adjoint
open import Categories.Adjoint.Equivalents using (Hom-NI′)
open import Categories.Adjoint.Mate
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Bifunctor
open import Categories.Functor.Hom
open import Categories.Category.Instance.Setoids
open import Categories.NaturalTransformation hiding (id)
open import Categories.NaturalTransformation.Properties
open import Categories.NaturalTransformation.NaturalIsomorphism as NI

record Closed : Set (levelOfTerm M) where
  open Monoidal M public

  field
    [-,-]   : Bifunctor C.op C C
    adjoint : (-⊗ X) ⊣ appˡ [-,-] X
    mate    : (f : X ⇒ Y) → Mate (adjoint {X}) (adjoint {Y}) (appʳ-nat ⊗ f) (appˡ-nat [-,-] f)

  module [-,-]        = Functor [-,-]
  module adjoint {X}  = Adjoint (adjoint {X})
  module mate {X Y} f = Mate (mate {X} {Y} f)

  [_,-] : Obj → Functor C C
  [_,-] = appˡ [-,-]

  [-,_] : Obj → Functor C.op C
  [-,_] = appʳ [-,-]

  [_,_]₀ : Obj → Obj → Obj
  [ X , Y ]₀ = [-,-].F₀ (X , Y)

  [_,_]₁ : A ⇒ B → X ⇒ Y → [ B , X ]₀ ⇒ [ A , Y ]₀
  [ f , g ]₁ = [-,-].F₁ (f , g)

  Hom[-⊗_,-] : ∀ X → Bifunctor C.op C (Setoids ℓ e)
  Hom[-⊗ X ,-] = adjoint.Hom[L-,-] {X}

  Hom[-,[_,-]] : ∀ X → Bifunctor C.op C (Setoids ℓ e)
  Hom[-,[ X ,-]] = adjoint.Hom[-,R-] {X}

  Hom-NI : ∀ {X : Obj} → NaturalIsomorphism Hom[-⊗ X ,-] Hom[-,[ X ,-]]
  Hom-NI = Hom-NI′ adjoint

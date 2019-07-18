{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Category.Closed {o ℓ e} (C : Category o ℓ e) where

private
  module C = Category C
  open C
  variable
    A B X Y Z : Obj
    f g : A ⇒ B

  open Commutation

open import Level
open import Data.Product using (Σ; _,_)

open import Categories.Category.Product
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Bifunctor
open import Categories.Functor.Construction.Constant
open import Categories.Functor.Construction.DoubleOp
open import Categories.NaturalTransformation
open import Categories.NaturalTransformation.NaturalIsomorphism
open import Categories.NaturalTransformation.Dinatural

record Closed : Set (levelOfTerm C) where
  field
    -- internal hom
    [-,-] : Bifunctor C.op C C
    unit  : Obj

  [_,-] : Obj → Functor C C
  [_,-] = appˡ [-,-]

  [-,_] : Obj → Functor C.op C
  [-,_] = appʳ [-,-]

  module [-,-] = Functor [-,-]

  [_,_]₀ : Obj → Obj → Obj
  [ X , Y ]₀ = [-,-].F₀ (X , Y)

  [_,_]₁ : A ⇒ B → X ⇒ Y → [ B , X ]₀ ⇒ [ A , Y ]₀
  [ f , g ]₁ = [-,-].F₁ (f , g)

  field
    identity : NaturalIsomorphism [ unit ,-] idF
    diagonal : DinaturalTransformation (const unit) [-,-]

  module identity = NaturalIsomorphism identity
  module diagonal = DinaturalTransformation diagonal

  [[X,-],[X,-]] : Obj → Bifunctor C.op C C
  [[X,-],[X,-]] X = [-,-] ∘F (Functor.op [ X ,-] ⁂ [ X ,-])

  [[-,Y],[-,Z]] : Obj → Obj → Bifunctor C C.op C
  [[-,Y],[-,Z]] Y Z = [-,-] ∘F ((Functor.op [-, Y ] ∘F C⇒opopC) ⁂ [-, Z ])

  -- L needs to be natural in Y and Z while extranatural in Z.
  -- it is better to spell out the conditions and then prove that indeed
  -- the naturality conditions hold.
  field
    L           : ∀ {X Y Z} → [ Y , Z ]₀ ⇒ [ [ X , Y ]₀ , [ X , Z ]₀ ]₀
    L-natural   : NaturalTransformation [-,-] ([[X,-],[X,-]] X)
    L-dinatural : DinaturalTransformation (const [ Y , Z ]₀) (flip-bifunctor ([[-,Y],[-,Z]] Y Z))

  module L-natural {X}     = NaturalTransformation (L-natural {X})
  module L-dinatural {Y Z} = DinaturalTransformation (L-dinatural {Y} {Z})

  field
    Lj≈j : [ unit ⇒ [ [ X , Y ]₀ , [ X , Y ]₀ ]₀ ]⟨
             diagonal.α Y ⇒⟨ [ Y , Y ]₀ ⟩
             L
           ≈ diagonal.α [ X , Y ]₀
           ⟩

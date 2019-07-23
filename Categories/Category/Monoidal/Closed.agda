{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Monoidal

module Categories.Category.Monoidal.Closed {o ℓ e} {C : Category o ℓ e} (M : Monoidal C) where

private
  module C = Category C
  open Category C

  variable
    X : Obj

open import Level
open import Function using (_$_) renaming (id to idFun)
open import Data.Product using (Σ; _,_)
open import Function.Equality as Π using (Π)

open import Categories.Adjoint
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Construction.Constant
open import Categories.Functor.Bifunctor
open import Categories.Functor.Hom
open import Categories.Category.Instance.Setoids
open import Categories.Morphism C
open import Categories.Morphism.Reasoning C
open import Categories.Morphism.Properties C
open import Categories.NaturalTransformation hiding (id)
open import Categories.NaturalTransformation.NaturalIsomorphism as NI hiding (_≅_; refl)
open import Categories.NaturalTransformation.Dinatural using (extranaturalʳ)
open import Categories.NaturalTransformation.Properties
open import Categories.Yoneda
import Categories.Category.Closed as Cl

record Closed : Set (levelOfTerm M) where
  open Monoidal M public
  
  field
    [-,-]   : Bifunctor C.op C C 
    adjoint : (-⊗ X) ⊣ appˡ [-,-] X
    
  module adjoint {X} = Adjoint (adjoint {X})
  module [-,-] = Functor [-,-]

  Hom[-⊗_,-] : ∀ X → Bifunctor C.op C (Setoids ℓ e)
  Hom[-⊗ X ,-] = adjoint.Hom[L-,-] {X}

  Hom[-,[_,-]] : ∀ X → Bifunctor C.op C (Setoids ℓ e)
  Hom[-,[ X ,-]] = adjoint.Hom[-,R-] {X}

  Hom-NI : ∀ {X : Obj} → NaturalIsomorphism Hom[-⊗ X ,-] Hom[-,[ X ,-]]
  Hom-NI = Hom-NI′ adjoint

  -- TODO: show that closed monoidal category is closed.
  module _ where
    open HomReasoning
    open Hom C
    open Π.Π

    private
      [_,-] : Obj → Endofunctor C
      [_,-] = appˡ [-,-]

      identity-NI : NaturalIsomorphism idF [ unit ,-]
      identity-NI = record
        { F⇒G = F∘id⇒F ∘ᵥ ([ unit ,-] ∘ˡ unitorʳ-natural.F⇒G) ∘ᵥ adjoint.unit
        ; F⇐G = adjoint.counit ∘ᵥ (unitorʳ-natural.F⇐G ∘ʳ [ unit ,-]) ∘ᵥ F⇒id∘F
        ; iso = λ X → Iso-resp-≈ (iso X)
                                 (⟺ identityˡ) (⟺ (∘-resp-≈ʳ identityʳ))
        }
        where open Functor
              iso : ∀ X → Iso (adjoint.Ladjunct unitorʳ.from)
                              (adjoint.counit.η X ∘ unitorʳ.to)
              iso X = record
                { isoˡ = begin
                  (adjoint.counit.η X ∘ unitorʳ.to) ∘ adjoint.Ladjunct unitorʳ.from
                    ≈⟨ pullʳ unitorʳ-commute-to ⟩
                  adjoint.counit.η X ∘ adjoint.Ladjunct unitorʳ.from ⊗₁ id ∘ unitorʳ.to
                    ≈˘⟨ assoc ⟩
                  adjoint.Radjunct (adjoint.Ladjunct unitorʳ.from) ∘ unitorʳ.to
                    ≈⟨ adjoint.RLadjunct≈id ⟩∘⟨refl ⟩
                  unitorʳ.from ∘ unitorʳ.to
                    ≈⟨ unitorʳ.isoʳ ⟩
                  id
                    ∎
                ; isoʳ = begin
                  adjoint.Ladjunct unitorʳ.from ∘ adjoint.counit.η X ∘ unitorʳ.to
                    ≈⟨ pullʳ (adjoint.unit.commute _) ⟩
                  [-,-].F₁ (id , unitorʳ.from) ∘ adjoint.Ladjunct ((adjoint.counit.η X ∘ unitorʳ.to) ⊗₁ id)
                    ≈˘⟨ pushˡ (homomorphism [ unit ,-]) ⟩
                  adjoint.Ladjunct (unitorʳ.from ∘ (adjoint.counit.η X ∘ unitorʳ.to) ⊗₁ id)
                    ≈⟨ F-resp-≈ [ unit ,-] unitorʳ-commute-from ⟩∘⟨refl ⟩
                  adjoint.Ladjunct ((adjoint.counit.η X ∘ unitorʳ.to) ∘ unitorʳ.from)
                    ≈⟨ F-resp-≈ [ unit ,-] (cancelʳ unitorʳ.isoˡ) ⟩∘⟨refl ⟩
                  adjoint.Ladjunct (adjoint.counit.η X)
                    ≈⟨ adjoint.zag ⟩
                  id
                    ∎
                }

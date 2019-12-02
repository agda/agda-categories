{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Instance.Core where

-- Core Functor (from Cats to Groupoids).
-- This is the right-adjoint of the forgetful functor from Groupoids to
-- Cats (see Categories.Functor.Adjoint.Instance.Core)

open import Level using (_⊔_)

open import Categories.Category using (Category)
import Categories.Category.Construction.Core as C
open import Categories.Category.Groupoid using (Groupoid)
open import Categories.Category.Instance.Cats using (Cats)
open import Categories.Category.Instance.Groupoids using (Groupoids)
open import Categories.Functor using (Functor; _∘F_; id)
open import Categories.Functor.Properties using ([_]-resp-≅; [_]-resp-≃)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (NaturalIsomorphism)
import Categories.Morphism as Morphism
open import Categories.Morphism.IsoEquiv using (⌞_⌟)
import Categories.Morphism.Reasoning as MR

Core : ∀ {o ℓ e} → Functor (Cats o ℓ e) (Groupoids o (ℓ ⊔ e) e)
Core {o} {ℓ} {e} = record
   { F₀ = CoreGrpd
   ; F₁ = CoreFunctor
   ; identity     = CoreId
   ; homomorphism = λ {A B C F G} → CoreHom {A} {B} {C} {F} {G}
   ; F-resp-≈     = CoreRespNI
   }
   where
     CoreGrpd : Category o ℓ e → Groupoid o (ℓ ⊔ e) e
     CoreGrpd C = record
       { category   = C.Core C
       ; isGroupoid = C.Core-isGroupoid C
       }

     CoreFunctor : {A B : Category o ℓ e} →
                   Functor A B → Functor (C.Core A) (C.Core B)
     CoreFunctor {A} {B} F = record
       { F₀ = F₀
       ; F₁ = [ F ]-resp-≅
       ; identity     = ⌞ identity     ⌟
       ; homomorphism = ⌞ homomorphism ⌟
       ; F-resp-≈     = [ F ]-resp-≃
       }
       where open Functor F

     CoreId : {A : Category o ℓ e} → NaturalIsomorphism (CoreFunctor {A} id) id
     CoreId {A} = record
       { F⇒G = record { η = λ _ → ≅.refl ; commute = λ _ → ⌞ MR.id-comm-sym A ⌟ ; sym-commute = λ _ → ⌞ MR.id-comm A ⌟ }
       ; F⇐G = record { η = λ _ → ≅.refl ; commute = λ _ → ⌞ MR.id-comm-sym A ⌟ ; sym-commute = λ _ → ⌞ MR.id-comm A ⌟ }
       ; iso = λ _ → record { isoˡ = ⌞ identity² ⌟ ; isoʳ = ⌞ identity² ⌟ }
       }
       where
         open Category A
         open Morphism A

     CoreHom : {A B C : Category o ℓ e}
               {F : Functor A B} {G : Functor B C} →
               NaturalIsomorphism (CoreFunctor (G ∘F F))
                                  (CoreFunctor G ∘F CoreFunctor F)
     CoreHom {A} {B} {C} {F} {G} = record
       { F⇒G = record { η = λ _ → ≅.refl ; commute = λ _ → ⌞ MR.id-comm-sym C ⌟ ; sym-commute = λ _ → ⌞ MR.id-comm C ⌟ }
       ; F⇐G = record { η = λ _ → ≅.refl ; commute = λ _ → ⌞ MR.id-comm-sym C ⌟ ; sym-commute = λ _ → ⌞ MR.id-comm C ⌟ }
       ; iso = λ _ → record { isoˡ = ⌞ identity² ⌟ ; isoʳ = ⌞ identity² ⌟ }
       }
       where
         open Category C
         open Morphism C

     CoreRespNI : {A B : Category o ℓ e} {F G : Functor A B} →
                  NaturalIsomorphism F G →
                  NaturalIsomorphism (CoreFunctor F) (CoreFunctor G)
     CoreRespNI {A} {B} {F} {G} μ = record
       { F⇒G = record { η = λ _ →       FX≅GX ; commute = λ _ → ⌞ ⇒.commute _ ⌟ ; sym-commute = λ _ → ⌞ ⇒.sym-commute _ ⌟ }
       ; F⇐G = record { η = λ _ → ≅.sym FX≅GX ; commute = λ _ → ⌞ ⇐.commute _ ⌟ ; sym-commute = λ _ → ⌞ ⇐.sym-commute _ ⌟ }
       ; iso = λ X → record { isoˡ = ⌞ iso.isoˡ X ⌟ ; isoʳ = ⌞ iso.isoʳ X ⌟ }
       }
       where
         open NaturalIsomorphism μ
         open Morphism B

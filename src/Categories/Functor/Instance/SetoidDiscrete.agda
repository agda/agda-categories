{-# OPTIONS --without-K --safe #-}
module Categories.Functor.Instance.SetoidDiscrete where

-- Discrete Functor
--   from Setoids to Cats.

open import Categories.Category
open import Categories.Functor
open import Categories.Category.Instance.Setoids
open import Categories.Category.Instance.Cats
open import Categories.NaturalTransformation.NaturalIsomorphism
  hiding (refl)
import Categories.Category.SetoidDiscrete as D

open import Relation.Binary
open import Function renaming (id to idf; _∘_ to _●_)
open import Function.Equality renaming (id to id⟶)

Discrete : ∀ {o ℓ e} → Functor (Setoids o ℓ) (Cats o ℓ e)
Discrete {o} {ℓ} {e} = record
   { F₀ = D.Discrete
   ; F₁ = DiscreteFunctor
   ; identity = λ {A} → DiscreteId {A}
   ; homomorphism = λ {X} {Y} {Z} {g} {h} → PointwiseHom {X} {Y} {Z} {g} {h}
   ; F-resp-≈ = λ {A} {B} {f} {g} → ExtensionalityNI {A} {B} {f} {g}
   }
   where
     DiscreteFunctor : {A B : Setoid o ℓ} → (A ⟶ B) → Cats o ℓ e [ D.Discrete A , D.Discrete B ]
     DiscreteFunctor f = record
       { F₀ = f ⟨$⟩_
       ; F₁ = cong f
       ; identity = _
       ; homomorphism = _
       ; F-resp-≈ = _
       }
     DiscreteId : {A : Setoid o ℓ} → NaturalIsomorphism (DiscreteFunctor {A} id⟶) id
     DiscreteId {A} = record
       { F⇒G = record { η = λ _ → refl ; commute = _ }
       ; F⇐G = record { η = λ _ → refl ; commute = _ }
       } where open Setoid A
     PointwiseHom : {X Y Z : Setoid o ℓ} {g : X ⟶ Y} {h : Y ⟶ Z} →
       NaturalIsomorphism (DiscreteFunctor (h ∘ g)) (DiscreteFunctor h ∘F DiscreteFunctor g)
     PointwiseHom {_} {_} {Z} = record
       { F⇒G = record { η = λ _ → refl }
       ; F⇐G = record { η = λ _ → refl }
       }
       where open Setoid Z
     ExtensionalityNI : {A B : Setoid o ℓ} {f g : A ⟶ B} → let open Setoid A in
      ({x y : Carrier} → x ≈ y → Setoid._≈_ B (f ⟨$⟩ x) (g ⟨$⟩ y)) →
      NaturalIsomorphism (DiscreteFunctor f) (DiscreteFunctor g)
     ExtensionalityNI {A} {B} cong≈ = record
       { F⇒G = record { η = λ X → cong≈ A.refl }
       ; F⇐G = record { η = λ X → B.sym (cong≈ A.refl) }
       }
       where
       module A = Setoid A
       module B = Setoid B

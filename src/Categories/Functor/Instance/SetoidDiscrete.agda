{-# OPTIONS --without-K --safe #-}
module Categories.Functor.Instance.SetoidDiscrete where

-- Discrete Functor
--   from Setoids to Cats.

open import Categories.Category using (Category; _[_,_])
open import Categories.Category.Discrete
open import Categories.Category.Instance.Setoids
open import Categories.Category.Instance.Cats
open import Categories.Functor using (Functor; id; _∘F_)
open import Categories.NaturalTransformation.NaturalIsomorphism
  hiding (refl)
import Categories.Category.Construction.SetoidDiscrete as D

open import Relation.Binary using (Setoid)
open import Function using () renaming (id to idf; _∘_ to _●_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Function.Construct.Identity using () renaming (function to id⟶)
open import Function.Construct.Composition using (function)

Discrete : ∀ {o ℓ e} → Functor (Setoids o ℓ) (Cats o ℓ e)
Discrete {o} {ℓ} {e} = record
   { F₀ = category ● D.Discrete
   ; F₁ = DiscreteFunctor
   ; identity = λ {A} → DiscreteId {A}
   ; homomorphism = λ {X} {Y} {Z} {g} {h} → PointwiseHom {X} {Y} {Z} {g} {h}
   ; F-resp-≈ = λ {A} {B} {f} {g} → ExtensionalityNI {A} {B} {f} {g}
   }
   where
     open DiscreteCategory
     DiscreteFunctor : {A B : Setoid o ℓ} → (Func A B) → Cats o ℓ e [ category (D.Discrete A) , category (D.Discrete B) ]
     DiscreteFunctor f = record
       { F₀ = f ⟨$⟩_
       ; F₁ = Func.cong f
       ; identity = _
       ; homomorphism = _
       ; F-resp-≈ = _
       }
     DiscreteId : {A : Setoid o ℓ} → NaturalIsomorphism (DiscreteFunctor {A} (id⟶ A)) id
     DiscreteId {A} = record
       { F⇒G = record { η = λ _ → refl ; commute = _ }
       ; F⇐G = record { η = λ _ → refl ; commute = _ }
       } where open Setoid A
     PointwiseHom : {X Y Z : Setoid o ℓ} {g : Func X Y} {h : Func Y Z} →
       NaturalIsomorphism (DiscreteFunctor (function g h)) (DiscreteFunctor h ∘F DiscreteFunctor g)
     PointwiseHom {_} {_} {Z} = record
       { F⇒G = record { η = λ _ → refl }
       ; F⇐G = record { η = λ _ → refl }
       }
       where open Setoid Z
     ExtensionalityNI : {A B : Setoid o ℓ} {f g : Func A B} → let open Setoid A in
      ({x y : Carrier} → x ≈ y → Setoid._≈_ B (f ⟨$⟩ x) (g ⟨$⟩ y)) →
      NaturalIsomorphism (DiscreteFunctor f) (DiscreteFunctor g)
     ExtensionalityNI {A} {B} cong≈ = record
       { F⇒G = record { η = λ X → cong≈ A.refl }
       ; F⇐G = record { η = λ X → B.sym (cong≈ A.refl) }
       }
       where
       module A = Setoid A
       module B = Setoid B

{-# OPTIONS --without-K --safe #-}
module Categories.Functor.Instance.Discrete where

-- Discrete Functor
--   from Sets to Cats. This works, unlike in the previous version of the library,
--   because the equality in Cats is properly NaturalIsomorphism instead of something stricter,
--   no need for that pesky Heterogeneous anything.

import Relation.Binary.PropositionalEquality as ≡
open import Function using () renaming (id to idf; _∘_ to _●_)

open import Categories.Category using (Category; _[_,_])
import Categories.Category.Construction.StrictDiscrete as D
open import Categories.Functor using (Functor; id; _∘F_)
open import Categories.Category.Instance.Sets
open import Categories.Category.Instance.Cats
open import Categories.NaturalTransformation using (ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism

Discrete : ∀ {o} → Functor (Sets o) (Cats o o o)
Discrete {o} = record
   { F₀ = D.Discrete
   ; F₁ = DiscreteFunctor
   ; identity = DiscreteId
   ; homomorphism = PointwiseHom
   ; F-resp-≈ = λ f≗g → ExtensionalityNI f≗g
   }
   where
     DiscreteFunctor : {A B : Set o} → (A → B) → Cats o o o [ D.Discrete A , D.Discrete B ]
     DiscreteFunctor f = record
       { F₀ = f
       ; F₁ = ≡.cong f
       ; identity = ≡.refl
       ; homomorphism = λ { {_} {_} {_} {≡.refl} {≡.refl} → ≡.refl}
       ; F-resp-≈ = λ g≡h → ≡.cong (≡.cong f) g≡h -- marvel at the weirdness involved
       }
     DiscreteId : {A : Set o} → NaturalIsomorphism (DiscreteFunctor {A} idf) id
     DiscreteId = record
       { F⇒G = record { η = λ X → ≡.refl ; commute = λ { ≡.refl → ≡.refl } ; sym-commute = λ { ≡.refl → ≡.refl} }
       ; F⇐G = record { η = λ _ → ≡.refl ; commute = λ { ≡.refl → ≡.refl } ; sym-commute = λ { ≡.refl → ≡.refl} }
       ; iso = λ X → record { isoˡ = ≡.refl ; isoʳ = ≡.refl }
       }
     PointwiseHom : {X Y Z : Set o} {g : X → Y} {h : Y → Z} →
       NaturalIsomorphism (DiscreteFunctor (h ● g)) (DiscreteFunctor h ∘F DiscreteFunctor g)
     PointwiseHom = record
       { F⇒G = record { η = λ _ → ≡.refl ; commute = λ { ≡.refl → ≡.refl} ; sym-commute = λ { ≡.refl → ≡.refl} }
       ; F⇐G = record { η = λ _ → ≡.refl ; commute = λ { ≡.refl → ≡.refl} ; sym-commute = λ { ≡.refl → ≡.refl} }
       ; iso = λ X → record { isoˡ = ≡.refl ; isoʳ = ≡.refl }
       }
     ExtensionalityNI : {A B : Set o} {g h : A → B} →
      g ≡.≗ h → NaturalIsomorphism (DiscreteFunctor g) (DiscreteFunctor h)
     ExtensionalityNI g≡h = record
       { F⇒G = ntHelper record { η = g≡h ; commute = λ { ≡.refl → ≡.sym (≡.trans-reflʳ (g≡h _))} }
       ; F⇐G = ntHelper record { η = λ X → ≡.sym (g≡h X) ; commute = λ { ≡.refl → ≡.sym (≡.trans-reflʳ _)} }
       ; iso = λ X → record { isoˡ = ≡.trans-symʳ (g≡h _) ; isoʳ = ≡.trans-symˡ (g≡h _) }
       }

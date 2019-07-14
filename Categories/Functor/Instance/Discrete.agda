{-# OPTIONS --without-K --safe #-}
module Categories.Functor.Instance.Discrete where

-- Proof relevant Discrete Functor from Sets to Cats
-- The "proof relevant" really matters here: ≈ for D.Discrete is _≡_
-- and not just ⊤.
open import Function renaming (id to idf)

open import Categories.Category using (Category; _[_,_]; _[_≈_])
open import Categories.Functor using (Functor) renaming (id to idF)
open import Categories.NaturalTransformation.NaturalIsomorphism
open import Categories.Category.Instance.Cats
open import Categories.Category.Instance.Sets

import Relation.Binary.PropositionalEquality as ≡

import Categories.Category.Discrete as D

Discrete : ∀ {s} -> Functor (Sets s) (Cats s s s)
Discrete {s} = record {
             F₀ = D.Discrete;
             F₁ = F₁;
             identity = λ {A} → idN {A};
             homomorphism = hom;
             F-resp-≈ = F-resp-≡}
  where
    -- missing rearrangement lemma
    cong-trans-comm : ∀ {ℓ ℓ′} {B : Set ℓ} {C : Set ℓ′} {X Y Z : B} {h : B → C} {eq₁ : X ≡.≡ Y} {eq₂ : Y ≡.≡ Z}
      → ≡.cong h (≡.trans eq₁ eq₂) ≡.≡ ≡.trans (≡.cong h eq₁) (≡.cong h eq₂)
    cong-trans-comm {eq₁ = ≡.refl} = ≡.refl

    F₁ : {A B : Category.Obj (Sets s)} → Sets s [ A , B ] →
                        Cats s s s [ D.Discrete A , D.Discrete B ]
    F₁ f = record {
             F₀ = f;
             F₁ = ≡.cong f;
             identity = ≡.refl;
             homomorphism =  λ {_} {_} {_} {eq₁} {eq₂} → cong-trans-comm {h = f} {eq₁ = eq₁} {eq₂ = eq₂} ;
             F-resp-≈ = λ f≡g → ≡.cong (≡.cong f) f≡g }

    idN : {A : Set s} → NaturalIsomorphism (F₁ idf) idF
    idN {A} = record
      { F⇒G = record { η = λ X → ≡.refl ; commute = λ { ≡.refl → ≡.refl} }
      ; F⇐G = record { η = λ _ → ≡.refl ; commute = λ { ≡.refl → ≡.refl } }
      ; iso = λ X → record { isoˡ = ≡.refl ; isoʳ = ≡.refl }
      }

    F-resp-≡ : {A B : Set s} {F G : Sets s [ A , B ]} →
                  Sets s [ F ≈ G ] → Cats s s s [ F₁ F ≈ F₁ G ]
    F-resp-≡ F≡G = record
      { F⇒G = record { η = λ X → F≡G {X} ; commute = λ { ≡.refl → ≡.sym (≡.trans-reflʳ F≡G) } }
      ; F⇐G = record { η = λ X → ≡.sym (F≡G {X}) ; commute = λ { ≡.refl → ≡.sym (≡.trans-reflʳ _)} }
      ; iso = λ X → record { isoˡ = ≡.trans-symʳ F≡G ; isoʳ = ≡.trans-symˡ F≡G }
      }
    hom : {X Y Z : Set s} {f : X → Y} {g : Y → Z} →
          NaturalIsomorphism (F₁ (λ x → g (f x))) (F₁ g Categories.Functor.∘F F₁ f)
    hom {f = f} {g} = record
      { F⇒G = record { η = λ _ → ≡.refl ; commute = λ { ≡.refl → ≡.refl} }
      ; F⇐G = record { η = λ _ → ≡.refl ; commute = λ { ≡.refl → ≡.refl} }
      ; iso = λ X → record { isoˡ = ≡.refl ; isoʳ = ≡.refl }
      }

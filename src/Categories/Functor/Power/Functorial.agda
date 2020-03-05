{-# OPTIONS --without-K --safe #-}

open import Level
open import Categories.Category

module Categories.Functor.Power.Functorial {o ℓ e : Level} (C : Category o ℓ e) where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import Categories.Functor renaming (id to idF)
open import Categories.Category.Discrete
open import Categories.Category.Equivalence
open import Categories.Category.Construction.Functors
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism as NI
  using (module NaturalIsomorphism; _≃_; refl)
import Categories.Morphism.Reasoning as MR
open MR C

import Categories.Functor.Power as Power
open Power C

open Category using (Obj)
open Category C using (_⇒_; _∘_; module Equiv)
module C = Category C
module CE = Equiv

private
  variable
    i : Level
    I : Set i

exp→functor₀ : Obj (Exp I) → Functor (Discrete I) C
exp→functor₀ X = record
  { F₀ = X
  ; F₁ = λ { refl → C.id }
  ; identity = CE.refl
  ; homomorphism = λ { {_} {_} {_} {refl} {refl} → CE.sym C.identityˡ}
  ; F-resp-≈ = λ { {_} {_} {refl} {refl} refl → CE.refl}
  }

exp→functor₁ : {X Y : I → C.Obj} → Exp I [ X , Y ] → NaturalTransformation (exp→functor₀ X) (exp→functor₀ Y)
exp→functor₁ F = record { η = F ; commute = λ { refl → id-comm } ; sym-commute = λ { refl → id-comm-sym } }

exp→functor : Functor (Exp I) (Functors (Discrete I) C)
exp→functor = record
  { F₀ = exp→functor₀
  ; F₁ = exp→functor₁
  ; identity = CE.refl
  ; homomorphism = CE.refl
  ; F-resp-≈ = λ eqs {x} → eqs x
  }

functor→exp : Functor (Functors (Discrete I) C) (Exp I)
functor→exp = record
  { F₀ = Functor.F₀
  ; F₁ = NaturalTransformation.η
  ; identity = λ _ → CE.refl
  ; homomorphism = λ _ → CE.refl
  ; F-resp-≈ = λ eqs i → eqs {i}
  }

exp≋functor : StrongEquivalence (Exp I) (Functors (Discrete I) C)
exp≋functor = record
  { F = exp→functor
  ; G = functor→exp
  ; weak-inverse = record
    { F∘G≈id = record
      { F⇒G = ntHelper record
        { η       = λ DI → record
          { η           = λ _ → C.id
          ; commute     = λ { refl → C.∘-resp-≈ˡ (CE.sym (Functor.identity DI))}
          ; sym-commute = λ { refl → C.∘-resp-≈ˡ (Functor.identity DI)}
          }
        ; commute = λ _ → id-comm-sym
        }
      ; F⇐G = ntHelper record
        { η = λ DI → ntHelper record { η = λ _ → C.id ; commute = λ { refl → C.∘-resp-≈ʳ (Functor.identity DI)} }
        ; commute = λ _ → id-comm-sym
        }
      ; iso = λ X → record { isoˡ = C.identity²; isoʳ = C.identity² }
      }
    ; G∘F≈id = record
      { F⇒G = record { η = λ _ _ → C.id ; commute = λ _ _ → id-comm-sym ; sym-commute = λ _ _ → id-comm }
      ; F⇐G = record { η = λ _ _ → C.id ; commute = λ _ _ → id-comm-sym ; sym-commute = λ _ _ → id-comm }
      ; iso = λ X → record { isoˡ = λ _ → C.identity² ; isoʳ = λ _ → C.identity² }
      }
    }
  }
  where
    open C.HomReasoning

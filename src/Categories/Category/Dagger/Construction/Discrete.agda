{-# OPTIONS --without-K --safe #-}
module Categories.Category.Dagger.Construction.Discrete where

open import Relation.Binary.PropositionalEquality

open import Categories.Category.Dagger
open import Categories.Category.Construction.StrictDiscrete

Discrete-HasDagger : ∀ {a} (A : Set a) → HasDagger (Discrete A)
Discrete-HasDagger A = record
  { _† = sym
  ; †-identity = refl
  ; †-homomorphism = λ { {f = refl} {g = refl} → refl }
  ; †-resp-≈ = cong sym
  ; †-involutive = λ { refl → refl}
  }

Discrete-DaggerCategory : ∀ {a} (A : Set a) → DaggerCategory a a a
Discrete-DaggerCategory A = record { hasDagger = Discrete-HasDagger A }

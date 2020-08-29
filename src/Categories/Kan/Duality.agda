{-# OPTIONS --without-K --safe #-}

module Categories.Kan.Duality where

open import Level
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation
open import Categories.Kan

private
  variable
    o ℓ e : Level
    C D E : Category o ℓ e
    F G : Functor C D

module _ {F : Functor C D} {G : Functor C E} where
  private
    module F = Functor F
    module G = Functor G

  coLan⇒Ran : Lan F.op G.op → Ran F G
  coLan⇒Ran lan = record
    { R        = L.op
    ; ε        = η.op
    ; δ        = λ M α → NaturalTransformation.op (σ (Functor.op M) (NaturalTransformation.op α))
    ; δ-unique = λ δ′ eq → σ-unique (NaturalTransformation.op δ′) eq
    ; commutes = λ M α → commutes (Functor.op M) (NaturalTransformation.op α)
    }
    where open Lan lan

  coRan⇒Lan : Ran F.op G.op → Lan F G
  coRan⇒Lan ran = record
    { L        = R.op
    ; η        = ε.op
    ; σ        = λ M α → NaturalTransformation.op (δ (Functor.op M) (NaturalTransformation.op α))
    ; σ-unique = λ σ′ eq → δ-unique (NaturalTransformation.op σ′) eq
    ; commutes = λ M α → commutes (Functor.op M) (NaturalTransformation.op α)
    }
    where open Ran ran

private
  module _ {F : Functor C D} {G : Functor C E} where
    module F = Functor F
    module G = Functor G

    coLan⟺Ran : (R : Ran F.op G.op) → coLan⇒Ran (coRan⇒Lan R) ≡ R
    coLan⟺Ran _ = ≡.refl

    coRan⟺Lan : (L : Lan F.op G.op) → coRan⇒Lan (coLan⇒Ran L) ≡ L
    coRan⟺Lan _ = ≡.refl

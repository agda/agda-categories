{-# OPTIONS --without-K --safe #-}
module Categories.Category.Restriction.Instance.PartialFunctions where

-- The Category of partial functions is a restriction category

-- The proof is straightforward in the sense that it's all unwinding definitions,
-- but also no-trivial in that they need to be unwound with care (a lot of
-- case analyses with 'with' and inspect is used a lot).

open import Data.Maybe using (Maybe; map; just; nothing; _>>=_)
open import Data.Maybe.Properties
open import Function using (const)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; inspect; [_])

open import Categories.Category.Core using (Category)
open import Categories.Category.Instance.PartialFunctions using (PartialFunctions)
open import Categories.Category.Restriction using (Restriction)

private
  variable
    o : Level
    A B C : Set o

Restriction-PF : ∀ {o} → Restriction (PartialFunctions o)
Restriction-PF {o} = record
  { _↓ = λ f x → map (const x) (f x)
  ; pidʳ = pidʳ
  ; ↓-comm = λ {_} {_} {_} {g} {f} → ↓-comm {g = g} {f}
  ; ↓-denestʳ = λ {_} {_} {_} {f} {g} → ↓-denestʳ {f = f} {g}
  ; ↓-skew-comm = λ {_} {_} {_} {g} {f} → ↓-skew-comm {g = g} {f}
  ; ↓-cong = ↓-cong
  }
  where
    open Category (PartialFunctions o)
    _↓ : (A → Maybe B) → (A → Maybe A)
    _↓ = λ f x → map (const x) (f x)

    pidʳ : {f : A → Maybe B} → f ∘ f ↓ ≈ f
    pidʳ {f = f} x with f x | inspect f x
    ... | just z | [ eq ] = eq
    ... | nothing | _ = refl

    ↓-comm : {g : A → Maybe C} {f : A → Maybe B} → g ↓ ∘ f ↓ ≈ f ↓ ∘ g ↓
    ↓-comm {g = g} {f} x with f x | g x | inspect f x | inspect g x
    ... | just b | just b′  | [ fx=jb ] | [ gx=jb′ ] rewrite fx=jb | gx=jb′ = refl
    ... | just b | nothing  | _         | [ eq ]     rewrite eq = refl
    ... | nothing | just b′ | [ eq ]    | _          rewrite eq = refl
    ... | nothing | nothing | _         | _                     = refl

    ↓-denestʳ : {A B C : Obj} {f : A ⇒ B} {g : A ⇒ C} → (g ∘ f ↓) ↓ ≈ g ↓ ∘ f ↓
    ↓-denestʳ {f = f} a with f a
    ... | just b  = refl
    ... | nothing = refl

    ↓-skew-comm : {A B C : Obj} {g : A ⇒ B} {f : C ⇒ A} → g ↓ ∘ f ≈ f ∘ (g ∘ f) ↓
    ↓-skew-comm {g = g} {f = f} a with f a | inspect f a
    ... | just b | [ eq ] with g b
    ... | just c = sym eq
    ... | nothing = refl
    ↓-skew-comm _ | nothing | _ = refl

    ↓-cong : {A B : Obj} {f g : A ⇒ B} → f ≈ g → f ↓ ≈ g ↓
    ↓-cong eq a rewrite eq a = refl

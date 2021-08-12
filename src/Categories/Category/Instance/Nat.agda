{-# OPTIONS --without-K --safe #-}
module Categories.Category.Instance.Nat where

-- Skeleton of FinSetoid as a Category

open import Level

open import Data.Fin.Base using (Fin; inject+; raise; splitAt; join)
open import Data.Fin.Properties
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Sum.Properties
open import Relation.Binary.PropositionalEquality
  using (_≗_; _≡_; refl; sym; trans; cong; module ≡-Reasoning; inspect; [_])
open import Function using (id; _∘′_)

open import Categories.Category.Cartesian.Bundle using (CartesianCategory)
open import Categories.Category.Cocartesian using (Cocartesian)
open import Categories.Category.Cocartesian.Bundle using (CocartesianCategory)
open import Categories.Category.Core using (Category)
open import Categories.Category.Duality using (Cocartesian⇒coCartesian)
open import Categories.Object.Coproduct

Nat : Category 0ℓ 0ℓ 0ℓ
Nat = record
  { Obj = ℕ
  ; _⇒_ = λ m n → (Fin m → Fin n)
  ; _≈_ = _≗_
  ; id = id
  ; _∘_ = _∘′_
  ; assoc = λ _ → refl
  ; sym-assoc = λ _ → refl
  ; identityˡ = λ _ → refl
  ; identityʳ = λ _ → refl
  ; identity² = λ _ → refl
  ; equiv = record
    { refl = λ _ → refl
    ; sym = λ x≡y z → sym (x≡y z)
    ; trans = λ x≡y y≡z w → trans (x≡y w) (y≡z w)
    }
  ; ∘-resp-≈ = λ {_ _ _ f h g i} f≗h g≗i x → trans (f≗h (g x)) (cong h (g≗i x))
  }

-- For other uses, it is important to choose coproducts
-- in theory, it should be strictly associative... but it's not, and won't be for any choice.
Coprod : (m n : ℕ) → Coproduct Nat m n
Coprod m n = record
  { A+B = m + n
  ; i₁ = inject+ n
  ; i₂ = raise m
  ; [_,_] = λ l r z → [ l , r ]′ (splitAt m z)
  ; inject₁ = λ {_ f g} x → cong [ f , g ]′ (splitAt-inject+ m n x)
  ; inject₂ = λ {_ f g} x → cong [ f , g ]′ (splitAt-raise m n x)
  ; unique = uniq
  }
  where
    open ≡-Reasoning
    uniq : {o : ℕ} {h : Fin (m + n) → Fin o} {f : Fin m → Fin o} {g : Fin n → Fin o} →
      h ∘′ inject+ n ≗ f → h ∘′ raise m ≗ g → (λ z → [ f , g ]′ (splitAt m z)) ≗ h
    uniq {_} {h} {f} {g} h≗f h≗g w = begin
      [ f , g ]′ (splitAt m w)                         ≡⟨ [,]-cong (λ x → sym (h≗f x)) (λ x → sym (h≗g x)) (splitAt m w) ⟩
      [ h ∘′ inject+ n , h ∘′ raise m ]′ (splitAt m w) ≡˘⟨ [,]-∘-distr h (splitAt m w) ⟩
      h ([ inject+ n , raise m ]′ (splitAt m w))       ≡⟨ cong h (join-splitAt m n w) ⟩
      h w                                              ∎

Nat-Cocartesian : Cocartesian Nat
Nat-Cocartesian = record
  { initial = record
    { ⊥ = 0
    ; ⊥-is-initial = record
      { ! = λ ()
      ; !-unique = λ _ ()
      }
    }
  ; coproducts = record { coproduct = λ {m} {n} → Coprod m n }
  }

Natop-Cartesian : CartesianCategory 0ℓ 0ℓ 0ℓ
Natop-Cartesian = record
  { U = Category.op Nat
  ; cartesian = Cocartesian⇒coCartesian Nat Nat-Cocartesian
  }

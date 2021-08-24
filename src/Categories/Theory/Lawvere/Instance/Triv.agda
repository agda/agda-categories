{-# OPTIONS --without-K --safe #-}

-- The 'Trivial' instance, with a single arrow between objects

module Categories.Theory.Lawvere.Instance.Triv where

open import Data.Nat using (_*_)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; isEquivalence)

open import Categories.Theory.Lawvere using (LawvereTheory)

Triv : ∀ {ℓ} → LawvereTheory ℓ ℓ
Triv = record
  { L = record
          { _⇒_ = λ _ _ → ⊤
          ; _≈_ = _≡_
          ; assoc = refl
          ; sym-assoc = refl
          ; identityˡ = refl
          ; identityʳ = refl
          ; identity² = refl
          ; equiv = isEquivalence
          ; ∘-resp-≈ = λ _ _ → refl
          }
  ; T = record
    { terminal = record { ⊤ = 0 ; ⊤-is-terminal = record { ! = tt ; !-unique = λ _ → refl } }
    ; products = record
      { product = λ {m} {n} → record
        { A×B = m * n
        ; project₁ = refl
        ; project₂ = refl
        ; unique = λ _ _ → refl
        }
      }
    }
  ; I = record
    { F₁ = λ _ → tt
    ; identity = refl
    ; homomorphism = refl
    ; F-resp-≈ = λ _ → refl
    }
  ; CartF = record
    { F-resp-⊤ = record { ! = tt ; !-unique = λ _ → refl }
    ; F-resp-× = record { ⟨_,_⟩ = λ _ _ → tt ; project₁ = refl ; project₂ = refl ; unique = λ _ _ → refl }
    }
  }

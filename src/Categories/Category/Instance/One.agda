{-# OPTIONS --without-K --safe #-}

open import Level

module Categories.Category.Instance.One where

open import Data.Unit using (⊤; tt)

open import Categories.Category
open import Categories.Functor
open import Categories.Category.Instance.Cats
import Categories.Object.Terminal as Term

module _ {o ℓ e : Level} where
  open Term (Cats o ℓ e)

  One : Category o ℓ e
  One = record
    { Obj       = Lift o ⊤
    ; _⇒_       = λ _ _ → Lift ℓ ⊤
    ; _≈_       = λ _ _ → Lift e ⊤
    }

  One-⊤ : Terminal
  One-⊤ = record { ⊤ = One ; ⊤-is-terminal = record { ! = record { F₀ = λ _ → lift tt } } }

-- not only is One terminal, it can be shifted anywhere else. Stronger version of !
shift : {o ℓ e : Level} (o′ ℓ′ e′ : Level) → Functor (One {o} {ℓ} {e}) (One {o′} {ℓ′} {e′})
shift o′ ℓ′ e′ = _ -- so obvious, Agda can fill it all in automatically!

One0 : Category 0ℓ 0ℓ 0ℓ
One0 = One {0ℓ} {0ℓ} {0ℓ}

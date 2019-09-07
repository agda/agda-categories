{-# OPTIONS --without-K --safe #-}

module Categories.Utils.Level where

open import Level using (Level)

levelOfType : ∀ {a} → Set a → Level
levelOfType {a} _ = a

levelOfTerm : ∀ {a} {A : Set a} → A → Level
levelOfTerm {a} _ = a


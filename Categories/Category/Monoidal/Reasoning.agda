{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)

module Categories.Category.Monoidal.Reasoning {o ℓ e} {C : Category o ℓ e} (M : Monoidal C) where

open import Data.Product using (_,_)

open import Categories.Functor renaming (id to idF)

private
  module C = Category C

open C hiding (id; identityˡ; identityʳ; assoc)

private
  variable
    X Y : Obj
    f g h i : X ⇒ Y

open Monoidal M using (_⊗₁_; ⊗)
open Functor ⊗ using (F-resp-≈; homomorphism)
open HomReasoning public

infixr 6 _⟩⊗⟨_ refl⟩⊗⟨_
infixl 7 _⟩⊗⟨refl

⊗-resp-≈ : f ≈ h → g ≈ i → (f ⊗₁ g) ≈ (h ⊗₁ i)
⊗-resp-≈ p q = F-resp-≈ (p , q)

⊗-resp-≈ˡ : f ≈ h → (f ⊗₁ g) ≈ (h ⊗₁ g)
⊗-resp-≈ˡ p = ⊗-resp-≈ p Equiv.refl

⊗-resp-≈ʳ : g ≈ i → (f ⊗₁ g) ≈ (f ⊗₁ i)
⊗-resp-≈ʳ p = ⊗-resp-≈ Equiv.refl p

_⟩⊗⟨_ : f ≈ h → g ≈ i → (f ⊗₁ g) ≈ (h ⊗₁ i)
_⟩⊗⟨_ = ⊗-resp-≈

refl⟩⊗⟨_ : g ≈ i → (f ⊗₁ g) ≈ (f ⊗₁ i)
refl⟩⊗⟨_ = ⊗-resp-≈ʳ

_⟩⊗⟨refl : f ≈ h → (f ⊗₁ g) ≈ (h ⊗₁ g)
_⟩⊗⟨refl = ⊗-resp-≈ˡ

-- removing the {_} makes the whole thing not type check anymore for some reason
-- an issue was raised on the main agda GitHub repository about this
-- (https://github.com/agda/agda/issues/4140)
-- if this is fixed feel free to remove the {_}
⊗-distrib-over-∘ : ((f ∘ h) ⊗₁ (g ∘ i)) ≈ ((f ⊗₁ g) ∘ (h ⊗₁ i))
⊗-distrib-over-∘ {_} = homomorphism
  -- This also corresponds with the graphical coherence property of diagrams modelling monoidal categories:
--   |        |         |   |
--  [h]      [i]       [h] [i]
--   |        |    ≈    |   |
--  [f]      [g]        |   |
--   |        |         |   |
--                     [f] [g]
--                      |   |

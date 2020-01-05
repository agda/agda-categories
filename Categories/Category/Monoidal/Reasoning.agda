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

-- Parallel-to-serial conversions
--
--   |   |        |   |       |   |
--   |   |        |  [g]     [f]  |
--  [f] [g]   =   |   |   =   |   |
--   |   |       [f]  |       |  [g]
--   |   |        |   |       |   |

serialize₁₂ : ∀ {X₁ Y₁ X₂ Y₂} {f : X₁ ⇒ Y₁} {g : X₂ ⇒ Y₂} →
              f ⊗₁ g ≈ f ⊗₁ C.id ∘ C.id ⊗₁ g
serialize₁₂ {f = f} {g} = begin
  f ⊗₁ g                     ≈˘⟨ C.identityʳ ⟩⊗⟨ C.identityˡ ⟩
  (f ∘ C.id) ⊗₁ (C.id ∘ g)   ≈⟨ ⊗-distrib-over-∘ ⟩
  f ⊗₁ C.id ∘ C.id ⊗₁ g      ∎

serialize₂₁ : ∀ {X₁ Y₁ X₂ Y₂} {f : X₁ ⇒ Y₁} {g : X₂ ⇒ Y₂} →
              f ⊗₁ g ≈ C.id ⊗₁ g ∘ f ⊗₁ C.id
serialize₂₁ {f = f} {g} = begin
  f ⊗₁ g                     ≈˘⟨ C.identityˡ ⟩⊗⟨ C.identityʳ ⟩
  (C.id ∘ f) ⊗₁ (g ∘ C.id)   ≈⟨ ⊗-distrib-over-∘ ⟩
  C.id ⊗₁ g ∘ f ⊗₁ C.id      ∎

-- Split a composite in the first component
--
--   |   |        |   |       |   |
--  [g]  |       [g]  |      [g] [h]
--   |  [h]   =   |   |   =   |   |
--  [f]  |       [f] [h]     [f]  |
--   |   |        |   |       |   |

split₁ʳ : ∀ {X₁ Y₁ Z₁ X₂ Y₂} {f : Y₁ ⇒ Z₁} {g : X₁ ⇒ Y₁} {h : X₂ ⇒ Y₂} →
          (f ∘ g) ⊗₁ h ≈ f ⊗₁ h ∘ g ⊗₁ C.id
split₁ʳ {f = f} {g} {h} = begin
  (f ∘ g) ⊗₁ h            ≈˘⟨ refl⟩⊗⟨ C.identityʳ ⟩
  (f ∘ g) ⊗₁ (h ∘ C.id)   ≈⟨ ⊗-distrib-over-∘ ⟩
  f ⊗₁ h ∘ g ⊗₁ C.id      ∎

split₁ˡ : ∀ {X₁ Y₁ Z₁ X₂ Y₂} {f : Y₁ ⇒ Z₁} {g : X₁ ⇒ Y₁} {h : X₂ ⇒ Y₂} →
          (f ∘ g) ⊗₁ h ≈ f ⊗₁ C.id ∘ g ⊗₁ h
split₁ˡ {f = f} {g} {h} = begin
  (f ∘ g) ⊗₁ h            ≈˘⟨ refl⟩⊗⟨ C.identityˡ ⟩
  (f ∘ g) ⊗₁ (C.id ∘ h)   ≈⟨ ⊗-distrib-over-∘ ⟩
  f ⊗₁ C.id ∘ g ⊗₁ h      ∎

-- Split a composite in the second component
--
--   |   |        |   |       |   |
--   |  [h]       |  [h]     [f] [h]
--  [f]  |    =   |   |   =   |   |
--   |  [g]      [f] [g]      |  [g]
--   |   |        |   |       |   |

split₂ʳ : ∀ {X₁ Y₁ X₂ Y₂ Z₂} {f : X₁ ⇒ Y₁} {g : Y₂ ⇒ Z₂} {h : X₂ ⇒ Y₂} →
          f ⊗₁ (g ∘ h) ≈ f ⊗₁ g ∘ C.id ⊗₁ h
split₂ʳ {f = f} {g} {h} = begin
  f ⊗₁ (g ∘ h)            ≈˘⟨ C.identityʳ ⟩⊗⟨refl ⟩
  (f ∘ C.id) ⊗₁ (g ∘ h)   ≈⟨ ⊗-distrib-over-∘ ⟩
  f ⊗₁ g ∘ C.id ⊗₁ h      ∎

split₂ˡ : ∀ {X₁ Y₁ X₂ Y₂ Z₂} {f : X₁ ⇒ Y₁} {g : Y₂ ⇒ Z₂} {h : X₂ ⇒ Y₂} →
          f ⊗₁ (g ∘ h) ≈ C.id ⊗₁ g ∘ f ⊗₁ h
split₂ˡ {f = f} {g} {h} = begin
  f ⊗₁ (g ∘ h)            ≈˘⟨ C.identityˡ ⟩⊗⟨refl ⟩
  (C.id ∘ f) ⊗₁ (g ∘ h)   ≈⟨ ⊗-distrib-over-∘ ⟩
  C.id ⊗₁ g ∘ f ⊗₁ h      ∎

{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)

module Categories.Category.Monoidal.Reasoning {o ℓ e} {C : Category o ℓ e} (M : Monoidal C) where

open import Data.Product using (_,_)

open import Categories.Functor using (Functor)

open Category C

private
  variable
    X Y : Obj
    f g h i : X ⇒ Y

open Monoidal M using (_⊗₀_; _⊗₁_; ⊗)
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

-- This corresponds to the graphical coherence property of diagrams
-- modelling monoidal categories:
--
--   |        |         |   |
--  [h]      [i]       [h] [i]
--   |        |    ≈    |   |
--  [f]      [g]        |   |
--   |        |         |   |
--                     [f] [g]
--                      |   |

⊗-distrib-over-∘ : ((f ∘ h) ⊗₁ (g ∘ i)) ≈ ((f ⊗₁ g) ∘ (h ⊗₁ i))
⊗-distrib-over-∘ = homomorphism

-- Parallel commutation

parallel : ∀ {X₁ X₂ Y₁ Y₂ Z₁ Z₂ W₁ W₂}
           {f₁ : Y₁ ⇒ W₁} {f₂ : Z₁ ⇒ W₁} {g₁ : Y₂ ⇒ W₂} {g₂ : Z₂ ⇒ W₂}
           {h₁ : X₁ ⇒ Y₁} {h₂ : X₁ ⇒ Z₁} {i₁ : X₂ ⇒ Y₂} {i₂ : X₂ ⇒ Z₂} →
           f₁ ∘ h₁ ≈ f₂ ∘ h₂ → g₁ ∘ i₁ ≈ g₂ ∘ i₂ →
           f₁ ⊗₁ g₁ ∘ h₁ ⊗₁ i₁ ≈ f₂ ⊗₁ g₂ ∘ h₂ ⊗₁ i₂
parallel {f₁ = f₁} {f₂} {g₁} {g₂} {h₁} {h₂} {i₁} {i₂} hyp₁ hyp₂ = begin
  f₁ ⊗₁ g₁ ∘ h₁ ⊗₁ i₁      ≈˘⟨ ⊗-distrib-over-∘ ⟩
  (f₁ ∘ h₁) ⊗₁ (g₁ ∘ i₁)   ≈⟨ hyp₁ ⟩⊗⟨ hyp₂ ⟩
  (f₂ ∘ h₂) ⊗₁ (g₂ ∘ i₂)   ≈⟨ ⊗-distrib-over-∘ ⟩
  f₂ ⊗₁ g₂ ∘ h₂ ⊗₁ i₂      ∎

-- Parallel-to-serial conversions
--
--   |   |        |   |       |   |
--   |   |        |  [g]     [f]  |
--  [f] [g]   =   |   |   =   |   |
--   |   |       [f]  |       |  [g]
--   |   |        |   |       |   |

serialize₁₂ : ∀ {X₁ Y₁ X₂ Y₂} {f : X₁ ⇒ Y₁} {g : X₂ ⇒ Y₂} →
              f ⊗₁ g ≈ f ⊗₁ id ∘ id ⊗₁ g
serialize₁₂ {f = f} {g} = begin
  f ⊗₁ g                 ≈˘⟨ identityʳ ⟩⊗⟨ identityˡ ⟩
  (f ∘ id) ⊗₁ (id ∘ g)   ≈⟨ ⊗-distrib-over-∘ ⟩
  f ⊗₁ id ∘ id ⊗₁ g      ∎

serialize₂₁ : ∀ {X₁ Y₁ X₂ Y₂} {f : X₁ ⇒ Y₁} {g : X₂ ⇒ Y₂} →
              f ⊗₁ g ≈ id ⊗₁ g ∘ f ⊗₁ id
serialize₂₁ {f = f} {g} = begin
  f ⊗₁ g                 ≈˘⟨ identityˡ ⟩⊗⟨ identityʳ ⟩
  (id ∘ f) ⊗₁ (g ∘ id)   ≈⟨ ⊗-distrib-over-∘ ⟩
  id ⊗₁ g ∘ f ⊗₁ id      ∎

-- Split a composite in the first component
--
--   |   |        |   |       |   |
--  [g]  |       [g]  |      [g] [h]
--   |  [h]   =   |   |   =   |   |
--  [f]  |       [f] [h]     [f]  |
--   |   |        |   |       |   |

split₁ʳ : ∀ {X₁ Y₁ Z₁ X₂ Y₂} {f : Y₁ ⇒ Z₁} {g : X₁ ⇒ Y₁} {h : X₂ ⇒ Y₂} →
          (f ∘ g) ⊗₁ h ≈ f ⊗₁ h ∘ g ⊗₁ id
split₁ʳ {f = f} {g} {h} = begin
  (f ∘ g) ⊗₁ h          ≈˘⟨ refl⟩⊗⟨ identityʳ ⟩
  (f ∘ g) ⊗₁ (h ∘ id)   ≈⟨ ⊗-distrib-over-∘ ⟩
  f ⊗₁ h ∘ g ⊗₁ id      ∎

split₁ˡ : ∀ {X₁ Y₁ Z₁ X₂ Y₂} {f : Y₁ ⇒ Z₁} {g : X₁ ⇒ Y₁} {h : X₂ ⇒ Y₂} →
          (f ∘ g) ⊗₁ h ≈ f ⊗₁ id ∘ g ⊗₁ h
split₁ˡ {f = f} {g} {h} = begin
  (f ∘ g) ⊗₁ h          ≈˘⟨ refl⟩⊗⟨ identityˡ ⟩
  (f ∘ g) ⊗₁ (id ∘ h)   ≈⟨ ⊗-distrib-over-∘ ⟩
  f ⊗₁ id ∘ g ⊗₁ h      ∎

-- Split a composite in the second component
--
--   |   |        |   |       |   |
--   |  [h]       |  [h]     [f] [h]
--  [f]  |    =   |   |   =   |   |
--   |  [g]      [f] [g]      |  [g]
--   |   |        |   |       |   |

split₂ʳ : ∀ {X₁ Y₁ X₂ Y₂ Z₂} {f : X₁ ⇒ Y₁} {g : Y₂ ⇒ Z₂} {h : X₂ ⇒ Y₂} →
          f ⊗₁ (g ∘ h) ≈ f ⊗₁ g ∘ id ⊗₁ h
split₂ʳ {f = f} {g} {h} = begin
  f ⊗₁ (g ∘ h)          ≈˘⟨ identityʳ ⟩⊗⟨refl ⟩
  (f ∘ id) ⊗₁ (g ∘ h)   ≈⟨ ⊗-distrib-over-∘ ⟩
  f ⊗₁ g ∘ id ⊗₁ h      ∎

split₂ˡ : ∀ {X₁ Y₁ X₂ Y₂ Z₂} {f : X₁ ⇒ Y₁} {g : Y₂ ⇒ Z₂} {h : X₂ ⇒ Y₂} →
          f ⊗₁ (g ∘ h) ≈ id ⊗₁ g ∘ f ⊗₁ h
split₂ˡ {f = f} {g} {h} = begin
  f ⊗₁ (g ∘ h)          ≈˘⟨ identityˡ ⟩⊗⟨refl ⟩
  (id ∘ f) ⊗₁ (g ∘ h)   ≈⟨ ⊗-distrib-over-∘ ⟩
  id ⊗₁ g ∘ f ⊗₁ h      ∎

-- The opposite, i.e. merge
merge₁ʳ : ∀ {X₁ Y₁ Z₁ X₂ Y₂} {f : Y₁ ⇒ Z₁} {g : X₁ ⇒ Y₁} {h : X₂ ⇒ Y₂} →
          f ⊗₁ h ∘ g ⊗₁ id ≈ (f ∘ g) ⊗₁ h
merge₁ʳ = Equiv.sym split₁ʳ

merge₁ˡ : ∀ {X₁ Y₁ Z₁ X₂ Y₂} {f : Y₁ ⇒ Z₁} {g : X₁ ⇒ Y₁} {h : X₂ ⇒ Y₂} →
          f ⊗₁ id ∘ g ⊗₁ h ≈ (f ∘ g) ⊗₁ h
merge₁ˡ = Equiv.sym split₁ˡ

merge₂ʳ : ∀ {X₁ Y₁ X₂ Y₂ Z₂} {f : X₁ ⇒ Y₁} {g : Y₂ ⇒ Z₂} {h : X₂ ⇒ Y₂} →
          f ⊗₁ g ∘ id ⊗₁ h ≈ f ⊗₁ (g ∘ h)
merge₂ʳ = Equiv.sym split₂ʳ

merge₂ˡ : ∀ {X₁ Y₁ X₂ Y₂ Z₂} {f : X₁ ⇒ Y₁} {g : Y₂ ⇒ Z₂} {h : X₂ ⇒ Y₂} →
          id ⊗₁ g ∘ f ⊗₁ h ≈ f ⊗₁ (g ∘ h)
merge₂ˡ = Equiv.sym split₂ˡ

-- Combined splitting and re-association.

module _ {X Y Z} {f : X ⇒ Z} {g : Y ⇒ Z} {h : X ⇒ Y} (f≈gh : f ≈ g ∘ h) where

  infixr 4 split₁_⟩∘⟨_ split₂_⟩∘⟨_
  infixl 5 _⟩∘⟨split₁_ _⟩∘⟨split₂_

  split₁_⟩∘⟨_ : ∀ {V W} {i j : V ⇒ X ⊗₀ W} → i ≈ j →
                f ⊗₁ id ∘ i ≈ g ⊗₁ id ∘ h ⊗₁ id ∘ j
  split₁_⟩∘⟨_ {_} {_} {i} {j} i≈j = begin
    f ⊗₁ id ∘ i                ≈⟨ f≈gh ⟩⊗⟨refl ⟩∘⟨ i≈j ⟩
    (g ∘ h) ⊗₁ id ∘ j          ≈⟨ split₁ˡ ⟩∘⟨refl ⟩
    (g ⊗₁ id ∘ h ⊗₁ id) ∘ j    ≈⟨ assoc ⟩
    g ⊗₁ id ∘ (h ⊗₁ id ∘ j)    ∎

  split₂_⟩∘⟨_ : ∀ {V W} {i j : V ⇒ W ⊗₀ X} → i ≈ j →
                id ⊗₁ f ∘ i ≈ id ⊗₁ g ∘ id ⊗₁ h ∘ j
  split₂_⟩∘⟨_ {_} {_} {i} {j} i≈j = begin
    id ⊗₁ f ∘ i                ≈⟨ refl⟩⊗⟨ f≈gh ⟩∘⟨ i≈j ⟩
    id ⊗₁ (g ∘ h) ∘ j          ≈⟨ split₂ˡ ⟩∘⟨refl ⟩
    (id ⊗₁ g ∘ id ⊗₁ h) ∘ j    ≈⟨ assoc ⟩
    id ⊗₁ g ∘ (id ⊗₁ h ∘ j)    ∎

  _⟩∘⟨split₁_ : ∀ {V W} {i j : Z ⊗₀ W ⇒ V} → i ≈ j →
                i ∘ f ⊗₁ id ≈ (j ∘ g ⊗₁ id) ∘ h ⊗₁ id
  _⟩∘⟨split₁_ {_} {_} {i} {j} i≈j = begin
    i ∘ f ⊗₁ id                ≈⟨ i≈j ⟩∘⟨ f≈gh ⟩⊗⟨refl ⟩
    j ∘ (g ∘ h) ⊗₁ id          ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
    j ∘ (g ⊗₁ id ∘ h ⊗₁ id)    ≈⟨ sym-assoc ⟩
    (j ∘ g ⊗₁ id) ∘ h ⊗₁ id    ∎

  _⟩∘⟨split₂_ : ∀ {V W} {i j : W ⊗₀ Z ⇒ V} → i ≈ j →
                i ∘ id ⊗₁ f ≈ (j ∘ id ⊗₁ g) ∘ id ⊗₁ h
  _⟩∘⟨split₂_ {_} {_} {i} {j} i≈j = begin
    i ∘ id ⊗₁ f                ≈⟨ i≈j ⟩∘⟨ refl⟩⊗⟨ f≈gh ⟩
    j ∘ id ⊗₁ (g ∘ h)          ≈⟨ refl⟩∘⟨ split₂ˡ ⟩
    j ∘ (id ⊗₁ g ∘ id ⊗₁ h)    ≈⟨ sym-assoc ⟩
    (j ∘ id ⊗₁ g) ∘ id ⊗₁ h    ∎

-- Combined merging and re-association.

module _ {X Y Z} {f : Y ⇒ Z} {g : X ⇒ Y} {h : X ⇒ Z} (fg≈h : f ∘ g ≈ h) where

  infixr 4 merge₁_⟩∘⟨_ merge₂_⟩∘⟨_
  infixl 5 _⟩∘⟨merge₁_ _⟩∘⟨merge₂_

  merge₁_⟩∘⟨_ : ∀ {V W} {i j : V ⇒ X ⊗₀ W} → i ≈ j →
                f ⊗₁ id ∘ g ⊗₁ id ∘ i ≈ h ⊗₁ id ∘ j
  merge₁_⟩∘⟨_ i≈j = ⟺ (split₁ ⟺ fg≈h ⟩∘⟨ ⟺ i≈j)

  merge₂_⟩∘⟨_ : ∀ {V W} {i j : V ⇒ W ⊗₀ X} → i ≈ j →
                id ⊗₁ f ∘ id ⊗₁ g ∘ i ≈ id ⊗₁ h ∘ j
  merge₂_⟩∘⟨_ i≈j = ⟺ (split₂ ⟺ fg≈h ⟩∘⟨ ⟺ i≈j)

  _⟩∘⟨merge₁_ : ∀ {V W} {i j : Z ⊗₀ W ⇒ V} → i ≈ j →
                (i ∘ f ⊗₁ id) ∘ g ⊗₁ id ≈ j ∘ h ⊗₁ id
  _⟩∘⟨merge₁_ i≈j = ⟺ (⟺ fg≈h ⟩∘⟨split₁ ⟺ i≈j)

  _⟩∘⟨merge₂_ : ∀ {V W} {i j : W ⊗₀ Z ⇒ V} → i ≈ j →
                (i ∘ id ⊗₁ f) ∘ id ⊗₁ g ≈ j ∘ id ⊗₁ h
  _⟩∘⟨merge₂_ i≈j = ⟺ (⟺ fg≈h ⟩∘⟨split₂ ⟺ i≈j)

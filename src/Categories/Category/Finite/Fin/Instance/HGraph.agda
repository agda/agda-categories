{-# OPTIONS --without-K --safe #-}

module Categories.Category.Finite.Fin.Instance.HGraph where

open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Patterns
open import Relation.Binary.PropositionalEquality.Core using (_≡_ ; refl)

open import Categories.Category.Finite.Fin
open import Categories.Category
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Presheaf

open import Categories.NaturalTransformation using (ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_)
open import Categories.Adjoint.Equivalence using (⊣Equivalence)
open import Categories.Adjoint.TwoSided using (_⊣⊢_; withZig)
import Categories.Morphism as Mor


private
  variable
    a b c d : Fin 2

x : Fin 3
x = {!   !}

-- The diagram is the following:
-- 0 ---n--> 1
-- with n arrows between 0 and 1

HyperGraphShape : ℕ → FinCatShape
HyperGraphShape n = shapeHelper record
  { size      = 2
  ; ∣_⇒_∣     = morph
  ; id        = id
  ; _∘_       = _∘_
  ; assoc     = assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  }
  where morph : Fin 2 → Fin 2 → ℕ
        morph 0F 0F = 1
        morph 0F 1F = n
        morph 1F 0F = 0
        morph 1F 1F = 1
        
        id : Fin (morph a a)
        id {0F} = 0F -- 0F is the only inhabitant of Fin 1
        id {1F} = 0F 

        _∘_ : ∀ {a b c} → Fin (morph b c) → Fin (morph a b) → Fin (morph a c)
        _∘_ {0F} {0F} {0F} 1₀ 1₀' = 1₀
        _∘_ {0F} {0F} {1F} g 1₀   = g
        _∘_ {1F} {1F} {1F} 1₁ 1₁' = 1₁
        _∘_ {0F} {1F} {1F} 1₁ f   = f
   
        assoc : ∀ {f : Fin (morph a b)} {g : Fin (morph b c)} {h : Fin (morph c d)} →
                  ((h ∘ g) ∘ f) ≡ (h ∘ (g ∘ f))
        assoc {0F} {0F} {0F} {0F} {e} {f} {h} = refl
        assoc {0F} {0F} {0F} {1F} {e} {f} {h} = refl
        assoc {0F} {0F} {1F} {1F} {e} {f} {h} = refl
        assoc {0F} {1F} {1F} {1F} {e} {f} {h} = refl
        assoc {1F} {1F} {1F} {1F} {e} {f} {h} = refl

        identityˡ : ∀ {f : Fin (morph a b)} → (id ∘ f) ≡ f
        identityˡ {0F} {0F} {0F} = refl
        identityˡ {0F} {1F} {f} = refl
        identityˡ {1F} {1F} {0F} = refl

        identityʳ : ∀ {f : Fin (morph a b)} → (f ∘ id) ≡ f
        identityʳ {0F} {0F} {f} = refl
        identityʳ {0F} {1F} {f} = refl
        identityʳ {1F} {1F} {0F} = refl

open import Level

Δₙ : ℕ → Category 0ℓ 0ℓ 0ℓ
Δₙ n = FinCategory (HyperGraphShape n)

----- Some Categories
----- convential names should be found 

open import Categories.Category.Instance.Sets

2GraphSet : (o : Level) → Set (suc o)
2GraphSet o = Presheaf (Δₙ 2) (Sets o)

3GraphSet : (o : Level) → Set (suc o)
3GraphSet o = Presheaf (Δₙ 3) (Sets o)

4GraphSet : (o : Level) → Set (suc o)
4GraphSet o = Presheaf (Δₙ 4) (Sets o)

nGraphSet : ℕ → (o : Level) → Set (suc o)
nGraphSet n o = Presheaf (Δₙ n) (Sets o)

----- Mapping to other constructions

----- Map Δₙ 2 to Parallel 

open import Categories.Category.Finite.Fin.Instance.Parallel as P

Δ₂ : Category 0ℓ 0ℓ 0ℓ
Δ₂ = Δₙ 2

-- module Category Δ₂

module Δ₂ = Category Δ₂ 
open FinCatShape (HyperGraphShape 2)

Δ₂⇒∥ : Functor Δ₂ P.Parallel
Δ₂⇒∥ = record
   { F₀ = F₀
   ; F₁ = F₁
   ; identity = idn
   ; homomorphism = hom
   ; F-resp-≈ = F-resp-≈
   } where 

   F₀ : Fin 2 → Fin 2
   F₀ x = x
 
   F₁ : ∀ {a} {b} → Fin ∣ a ⇒ b ∣ →  Parallel [ F₀ a , F₀ b ] -- P.card (F₀ a) (F₀ b) -- P.Parallel [ F₀ A , F₀ B ]
   F₁ {0F} {0F} x = x
   F₁ {0F} {1F} x = x
   F₁ {1F} {1F} x = x

   idn : ∀ {a} → F₁ ( Δ₂.id {a} ) ≡ Parallel.id 
   idn {0F} = refl
   idn {1F} = refl

   hom : ∀ {X} {Y} {Z} {f : Δ₂ [ X , Y ]} {g : Δ₂ [ Y , Z ]} →
      Parallel [ F₁ (Δ₂ [ g ∘ f ]) ≈ Parallel [ F₁ g ∘ F₁ f ] ]
   hom {0F} {0F} {0F} {0F} {0F} = refl
   hom {0F} {0F} {1F} {0F} {0F} = refl
   hom {0F} {0F} {1F} {0F} {1F} = refl
   hom {0F} {1F} {1F} {0F} {0F} = refl
   hom {0F} {1F} {1F} {1F} {0F} = refl
   hom {1F} {1F} {1F} {0F} {0F} = refl

   F-resp-≈ : ∀ {A} {B} {f g : Δ₂ [ A , B ]} →
         Δ₂ [ f ≈ g ] → Parallel [ F₁ f ≈ F₁ g ]
   F-resp-≈ {0F} {0F} {f} {.f} refl = refl
   F-resp-≈ {0F} {1F} {f} {.f} refl = refl
   F-resp-≈ {1F} {1F} {f} {.f} refl = refl



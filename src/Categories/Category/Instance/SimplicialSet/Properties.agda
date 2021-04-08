{-# OPTIONS --without-K --safe #-}

open import Level
open import Function using (_$_)

module Categories.Category.Instance.SimplicialSet.Properties (o ℓ : Level) where

open import Data.Empty.Polymorphic
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; _<_; fromℕ)
open import Data.Fin.Patterns
open import Data.Product using (proj₁)

import Relation.Binary.PropositionalEquality as Eq

open import Categories.Category
open import Categories.Category.Instance.SimplicialSet
open import Categories.Category.Instance.Simplex

open import Categories.Functor
open import Categories.Functor.Construction.Constant
open import Categories.Functor.Construction.LiftSetoids

open import Categories.NaturalTransformation

open import Categories.Yoneda

private
  module Y = Functor (Yoneda.embed Δ)

-- Some useful notation for a simplicial set
ΔSet : Set (suc o ⊔ suc ℓ)
ΔSet = Category.Obj (SimplicialSet o ℓ )

-- The standard n-simplex.
Δ[_] : ℕ → ΔSet
Δ[_] n = LiftSetoids o ℓ ∘F Y.F₀ n

--------------------------------------------------------------------------------
-- Boundaries of the Standard Simplicies
--
-- The basic idea here is that we will build up boundary of 'Δ[ n ]' by considering
-- all of the morphisms 'Δ[ m , n ]' that factor through some face map 'face i : Δ[ n - 1 , n ]'

-- The indexing here is a bit tricky, but this is the price we pay to avoid 'pred'
-- A 'Boundary m n' represents some set of maps into 'Δ[ ℕ.suc n ]' that factor through
-- a face map. To make this indexing more obvious, we use the suggestively named variable 'n-1'.
record Boundary (m n-1 : ℕ) : Set where
  field
    hom : Δ [ m , (ℕ.suc n-1) ]
    factor : Δ [ m , n-1 ]
    factor-dim : Fin (ℕ.suc n-1)
    factor-face : Δ [ hom ≈ Δ [ face factor-dim ∘ factor ] ]

-- Lift morphisms in Δ to maps between boundary sets on 'Δ[ n ]'
boundary-map : ∀ {x y n} → Δ [ x , y ] → Boundary y n → Boundary x n
boundary-map {n = n} f b = record
  { hom = hom b ∘ f
  ; factor = factor b ∘ f
  ; factor-dim = factor-dim b
  ; factor-face = λ x → factor-face b (proj₁ f x)
  }
  where
    open Category Δ
    open Boundary

-- The boundary of an n-simplex
∂Δ[_] : ℕ → ΔSet 
∂Δ[_] ℕ.zero = const record
  { Carrier = ⊥
  ; _≈_ = λ ()
  ; isEquivalence = record
    { refl  = λ { {()} }
    ; sym   = λ { {()} }
    ; trans = λ { {()} }
    }
  }
∂Δ[_] (ℕ.suc n) = record
  { F₀ = λ m → record
    { Carrier = Lift o (Boundary m n)
    -- Unwinding the equality by hand here leads to less unsolved metavariables down the line
    ; _≈_ = λ (lift b) (lift b′) → ∀ x → Lift ℓ (proj₁ (hom b) x ≡ proj₁ (hom b′) x)
    ; isEquivalence = record
      { refl = λ x → lift refl
      ; sym = λ eq x → lift (sym (lower (eq x)))
      ; trans = λ eq₁ eq₂ x → lift (trans (lower (eq₁ x)) (lower (eq₂ x)))
      }
    }
  ; F₁ = λ f → record
    { _⟨$⟩_ = λ (lift b) → lift (boundary-map f b)
    ; cong = λ eq x → eq (proj₁ f x)
    }
  ; identity = λ eq → eq
  ; homomorphism = λ {_} {_} {_} {f} {g} eq x → eq (proj₁ f (proj₁ g x))
  ; F-resp-≈ = λ {_} {_} {f} {g} f≈g {b} {b′} eq x → lift $ begin
    proj₁ (hom (lower b)) (proj₁ f x)  ≡⟨ lower (eq (proj₁ f x)) ⟩
    proj₁ (hom (lower b′)) (proj₁ f x) ≡⟨ cong (proj₁ (hom (lower b′))) (f≈g x) ⟩
    proj₁ (hom (lower b′)) (proj₁ g x) ∎
  } 
  where
    open Boundary
    open Eq
    open ≡-Reasoning

--------------------------------------------------------------------------------
-- Horns
-- 
-- The idea here is essentially the same as the boundaries, but we exclude the kth
-- face map as a possible factor.

record Horn (m n-1 : ℕ) (k : Fin (ℕ.suc n-1)) : Set where
  field
    horn : Boundary m n-1

  open Boundary horn public

  field
    is-horn : factor-dim Eq.≢ k

Λ[_,_] : (n : ℕ) → Fin n → ΔSet
Λ[ ℕ.suc n , k ] = record
  { F₀ = λ m → record
    { Carrier = Lift o (Horn m n k)
    ; _≈_ = λ (lift b) (lift b′) → ∀ x → Lift ℓ (proj₁ (hom b) x ≡ proj₁ (hom b′) x)
    ; isEquivalence = record
      { refl = λ x → lift refl
      ; sym = λ eq x → lift (sym (lower (eq x)))
      ; trans = λ eq₁ eq₂ x → lift (trans (lower (eq₁ x)) (lower (eq₂ x)))
      }
    }
  ; F₁ = λ f → record
    { _⟨$⟩_ = λ (lift h) → lift $ record
      { horn = boundary-map f (horn h)
      ; is-horn = is-horn h
      }
    ; cong = λ eq x → eq (proj₁ f x)
    }
  ; identity = λ eq → eq
  ; homomorphism = λ {_} {_} {_} {f} {g} eq x → eq (proj₁ f (proj₁ g x))
  ; F-resp-≈ = λ {_} {_} {f} {g} f≈g {b} {b′} eq x → lift $ begin
    proj₁ (hom (lower b)) (proj₁ f x)  ≡⟨ lower (eq (proj₁ f x)) ⟩
    proj₁ (hom (lower b′)) (proj₁ f x) ≡⟨ cong (proj₁ (hom (lower b′))) (f≈g x) ⟩
    proj₁ (hom (lower b′)) (proj₁ g x) ∎
  }
  where
    open Horn
    open Eq
    open ≡-Reasoning


--------------------------------------------------------------------------------
-- Kan Complexes
--
-- These are technically "Algebraic" Kan Complexes, as they come with a choice of fillers
-- However, this notion is far easier than the more geometric flavor,
-- as we can sidestep questions about choice.

module _ where
  open Category (SimplicialSet o ℓ)

  -- Inclusion of boundaries
  ∂Δ-inj : ∀ {n} → ∂Δ[ n ] ⇒ Δ[ n ]
  ∂Δ-inj {ℕ.zero} = ntHelper record
    { η = λ X → record
      { _⟨$⟩_ = ⊥-elim
      ; cong = λ { {()} }
      }
    ; commute = λ { _ {()} _ }
    }
  ∂Δ-inj {ℕ.suc n} = ntHelper record
    { η = λ X → record
      { _⟨$⟩_ = λ (lift b) → lift (hom b)
      ; cong = λ eq → lift (λ x → lower (eq x))
      }
    ; commute = λ f eq → lift (λ x → lower (eq (proj₁ f x)))
    }
    where
      open Boundary

  -- Inclusion of n-horns into n-simplicies
  Λ-inj : ∀ {n} → (k : Fin n) → Λ[ n , k ] ⇒ Δ[ n ]
  Λ-inj {n = ℕ.suc n} k = ntHelper record
    { η = λ X → record
      { _⟨$⟩_ = λ (lift h) → lift (hom h)
      ; cong = λ eq → lift (λ x → lower (eq x))
      }
    ; commute = λ f eq → lift (λ x → lower (eq (proj₁ f x)))
    }
    where
      open Horn
  
  record IsKanComplex (X : ΔSet) : Set (o ⊔ ℓ) where
    field
      filler : ∀ {n} {k} → Λ[ n , k ] ⇒ X → Δ[ n ] ⇒ X
      filler-cong : ∀ {n} {k} → {f g : Λ[ n , k ] ⇒ X} → f ≈ g → filler {n} f ≈ filler g
      is-filler : ∀ {n} {k} → (f : Λ[ n , k ] ⇒ X) → filler f ∘ Λ-inj k ≈ f

  record IsWeakKanComplex (X : ΔSet) : Set (o ⊔ ℓ) where
    field
      filler : ∀ {n} {k : Fin (ℕ.suc n)} → 0F < k → k < fromℕ n → Λ[ ℕ.suc n , k ] ⇒ X → Δ[ ℕ.suc n ] ⇒ X
      filler-cong : ∀ {n} {k} → (0<k : 0F < k) → (k<n : k < fromℕ n) → {f g : Λ[ ℕ.suc n , k ] ⇒ X} → f ≈ g → filler 0<k k<n f ≈ filler 0<k k<n g
      is-filler : ∀ {n} {k : Fin (ℕ.suc n)} → (0<k : 0F < k) → (k<n : k < fromℕ n) → (f : Λ[ ℕ.suc n , k ] ⇒ X) → filler 0<k k<n f ∘ Λ-inj k ≈ f

  KanComplex⇒WeakKanComplex : ∀ {X} → IsKanComplex X → IsWeakKanComplex X
  KanComplex⇒WeakKanComplex complex = record
    { filler = λ _ _ f → filler f
    ; filler-cong = λ _ _ eq x → filler-cong eq x
    ; is-filler = λ { {n} {k} 0<k k<n f {m} {h} {h′} x → is-filler f {m} {h} x }
    }
    where
      open IsKanComplex complex
  

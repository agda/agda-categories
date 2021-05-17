{-# OPTIONS --without-K --safe #-}

open import Level

module Categories.Category.Instance.SimplicialSet.Properties (o ℓ : Level) where

open import Function using (_$_)

open import Data.Empty.Polymorphic using (⊥; ⊥-elim)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Product using (proj₁)

import Relation.Binary.PropositionalEquality as Eq

open import Categories.Category using (Category; _[_,_]; _[_∘_]; _[_≈_])
open import Categories.Category.Instance.SimplicialSet using (SimplicialSet)
open import Categories.Category.Instance.Simplex using (Δ; δ; σ; ⟦_⟧; Δ-eq; Δ-pointwise)

open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Construction.Constant using (const)
open import Categories.Functor.Construction.LiftSetoids using (LiftSetoids)

open import Categories.NaturalTransformation using (ntHelper)

open import Categories.Yoneda

private
  module Y = Functor (Yoneda.embed Δ)
  module Δ = Category Δ

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
  -- To avoid the (somewhat confusion) pattern of 'ℕ.suc n-1', let's define
  -- a bit of helpful local notation.
  private
    n : ℕ
    n = ℕ.suc n-1

  field
    hom : Δ [ m , n ]
    factor : Δ [ m , n-1 ]
    factor-dim : Fin n
    factor-face : Δ [ hom ≈ Δ [ δ factor-dim ∘ factor ] ]

-- Lift morphisms in Δ to maps between boundary sets on 'Δ[ n ]'
boundary-map : ∀ {x y n} → Δ [ x , y ] → Boundary y n → Boundary x n
boundary-map {n = n} f b = record
  { hom = hom b ∘ f
  ; factor = factor b ∘ f
  ; factor-dim = factor-dim b
  ; factor-face = Δ-eq (Δ-pointwise (factor-face b))
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
    ; _≈_ = λ (lift b) (lift b′) → Lift ℓ (Δ [ hom b ≈ hom b′ ])
    ; isEquivalence = record
      { refl = lift Δ.Equiv.refl
      ; sym = λ (lift eq) → lift (Δ.Equiv.sym eq)
      ; trans = λ (lift eq₁) (lift eq₂) → lift (Δ.Equiv.trans eq₁ eq₂)
      }
    }
  ; F₁ = λ f → record
    { _⟨$⟩_ = λ (lift b) → lift (boundary-map f b)
    ; cong = λ (lift eq) → lift (Δ-eq (Δ-pointwise eq))
    }
  ; identity = λ (lift eq) → lift (Δ-eq (Δ-pointwise eq))
  ; homomorphism = λ (lift eq) → lift (Δ-eq (Δ-pointwise eq))
  ; F-resp-≈ = λ {_} {_} {f} {g} f≈g {b} {b′} eq → lift $ Δ-eq $ λ {x} → begin
    ⟦ hom (lower b) ⟧  (⟦ f ⟧ x) ≡⟨ Δ-pointwise (lower eq) ⟩
    ⟦ hom (lower b′) ⟧ (⟦ f ⟧ x) ≡⟨ cong ⟦ hom (lower b′) ⟧ (Δ-pointwise f≈g) ⟩
    ⟦ hom (lower b′) ⟧ (⟦ g ⟧ x) ∎
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
    ; _≈_ = λ (lift h) (lift h′) → Lift ℓ (Δ [ hom h ≈ hom h′ ])
    ; isEquivalence = record
      { refl = lift Δ.Equiv.refl
      ; sym = λ (lift eq) → lift (Δ.Equiv.sym eq)
      ; trans = λ (lift eq₁) (lift eq₂) → lift (Δ.Equiv.trans eq₁ eq₂)
      }
    }
  ; F₁ = λ f → record
    { _⟨$⟩_ = λ (lift h) → lift record
      { horn = boundary-map f (horn h)
      ; is-horn = is-horn h
      }
    ; cong = λ (lift eq) → lift (Δ-eq (Δ-pointwise eq))
    }
  ; identity = λ (lift eq) → lift (Δ-eq (Δ-pointwise eq))
  ; homomorphism = λ (lift eq) → lift (Δ-eq (Δ-pointwise eq))
  ; F-resp-≈ = λ {_} {_} {f} {g} f≈g {h} {h′} eq → lift $ Δ-eq $ λ {x} → begin
    ⟦ hom (lower h) ⟧  (⟦ f ⟧ x) ≡⟨ Δ-pointwise (lower eq) ⟩
    ⟦ hom (lower h′) ⟧ (⟦ f ⟧ x) ≡⟨ cong ⟦ hom (lower h′) ⟧ (Δ-pointwise f≈g) ⟩
    ⟦ hom (lower h′) ⟧ (⟦ g ⟧ x) ∎
  }
  where
    open Horn
    open Eq
    open ≡-Reasoning


--------------------------------------------------------------------------------
-- Morphims between simplicial sets

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
      ; cong = λ (lift eq) → lift (Δ-eq (Δ-pointwise eq))
      }
    ; commute = λ f (lift eq) → lift (Δ-eq (Δ-pointwise eq))
    }
    where
      open Boundary

  -- Inclusion of n-horns into n-simplicies
  Λ-inj : ∀ {n} → (k : Fin n) → Λ[ n , k ] ⇒ Δ[ n ]
  Λ-inj {n = ℕ.suc n} k = ntHelper record
    { η = λ X → record
      { _⟨$⟩_ = λ (lift h) → lift (hom h)
      ; cong = λ (lift eq) → lift (Δ-eq (Δ-pointwise eq))
      }
    ; commute = λ f (lift eq) → lift (Δ-eq (Δ-pointwise eq))
    }
    where
      open Horn

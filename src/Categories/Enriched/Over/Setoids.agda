{-# OPTIONS --without-K --safe #-}

-- A Category enriched over Setoids is... a Category!
module Categories.Enriched.Over.Setoids where

open import Level
open import Data.Product using (uncurry; proj₁; proj₂; Σ; _,_)
open import Data.Unit using (tt)
open import Function.Equality using (_⟨$⟩_; cong)
open import Relation.Binary.Bundles using (Setoid)

open import Categories.Category.Core using () renaming (Category to SCategory)
open import Categories.Category.Equivalence using (StrongEquivalence)
open import Categories.Category.Monoidal.Instance.Setoids
open import Categories.Functor renaming (id to idF)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_)
open import Categories.Enriched.Category
import Categories.Morphism.Reasoning as MR

Category′ : (o ℓ t : Level) → Set (suc (o ⊔ ℓ ⊔ t))
Category′ o ℓ t = Category (Setoids-Monoidal {t} {ℓ}) o

-- Start with the translation functions
Cat→Cat′ : {o ℓ t : Level} → SCategory o ℓ t → Category′ o t ℓ
Cat→Cat′ C = record
  { Obj = Obj
  ; hom = λ a b → record
    { Carrier = a ⇒ b
    ; _≈_ = _≈_
    ; isEquivalence = equiv
    }
  ; id = record
    { _⟨$⟩_ = λ _ → id
    ; cong = λ _ → Equiv.refl
    }
  ; ⊚ = record
    { _⟨$⟩_ = uncurry _∘_
    ; cong = uncurry ∘-resp-≈
    }
  ; ⊚-assoc = λ { {x = (x₁ , x₂) , x₃} {(y₁ , y₂) , y₃} ((x₁≈y₁ , x₂≈y₂) , x₃≈y₃) → begin
    (x₁ ∘ x₂) ∘ x₃ ≈⟨ assoc {h = x₁} ⟩
    x₁ ∘ x₂ ∘ x₃   ≈⟨ (x₁≈y₁ ⟩∘⟨ x₂≈y₂ ⟩∘⟨ x₃≈y₃) ⟩
    y₁ ∘ y₂ ∘ y₃   ∎ }
  ; unitˡ = λ { {_} {_} {_ , x} {_ , y} (_ , x≈y) → Equiv.trans (identityˡ {f = x}) x≈y }
  ; unitʳ = λ z → Equiv.trans identityʳ (proj₁ z)
  }
  where
  open SCategory C
  open HomReasoning

Cat′→Cat : {o ℓ t : Level} → Category′ o ℓ t → SCategory o t ℓ
Cat′→Cat 𝓒 = record
  { Obj = Obj
  ; _⇒_ = λ a b → Carrier (hom a b)
  ; _≈_ = λ {a} {b} f g → _≈_ (hom a b) f g
  ; id = id ⟨$⟩ lift tt
  ; _∘_ = λ f g → ⊚ ⟨$⟩ (f , g)
  ; assoc = λ {A} {B} {C} {D} → ⊚-assoc ((refl (hom C D) , refl (hom B C)) , refl (hom A B))
  ; sym-assoc = λ {A} {B} {C} {D} → sym (hom A D) (⊚-assoc ((refl (hom C D) , refl (hom B C)) , refl (hom A B)))
  ; identityˡ = λ {A} {B} → unitˡ (lift tt , refl (hom A B))
  ; identityʳ = λ {A} {B} → unitʳ (refl (hom A B) , lift tt)
  ; identity² = λ {A} → unitˡ (lift tt , refl (hom A A)) -- Enriched doesn't have a unit²
  ; equiv = λ {A} {B} → record
    { refl = refl (hom A B)
    ; sym = sym (hom A B)
    ; trans = trans (hom A B)
    }
  ; ∘-resp-≈ = λ f≈h g≈i → cong ⊚ (f≈h , g≈i)
  }
  where
  open Category 𝓒
  open Setoid

-- Back-and-forth gives the same thing, SCat version
-- the details are trivial, but have to be spelled out
SCat-Equiv : {o ℓ t : Level} → (C : SCategory o ℓ t) → StrongEquivalence C (Cat′→Cat (Cat→Cat′ C))
SCat-Equiv C = record
  { F = fwd
  ; G = bwd
  ; weak-inverse = record
    { F∘G≈id = f∘b≃id
    ; G∘F≈id = b∘f≃id
    }
  }
  where
  open SCategory C
  open MR C
  fwd : Functor C (Cat′→Cat (Cat→Cat′ C))
  fwd = record
    { F₀ = λ x → x
    ; F₁ = λ f → f
    ; identity = Equiv.refl
    ; homomorphism = Equiv.refl
    ; F-resp-≈ = λ ≈ → ≈
    }
  bwd : Functor (Cat′→Cat (Cat→Cat′ C)) C
  bwd = record
    { F₀ = λ x → x
    ; F₁ = λ f → f
    ; identity = Equiv.refl
    ; homomorphism = Equiv.refl
    ; F-resp-≈ = λ ≈ → ≈
    }
  f∘b≃id : fwd ∘F bwd ≃ idF
  f∘b≃id = record
    { F⇒G = record { η = λ A → id {A} ; commute = λ _ → id-comm-sym ; sym-commute = λ _ → id-comm }
    ; F⇐G = record { η = λ A → id {A} ; commute = λ _ → id-comm-sym ; sym-commute = λ _ → id-comm }
    ; iso = λ X → record { isoˡ = identity² ; isoʳ = identity² }
    }
  b∘f≃id : bwd ∘F fwd ≃ idF
  b∘f≃id = record
    { F⇒G = record { η = λ A → id {A} ; commute = λ _ → id-comm-sym ; sym-commute = λ _ → id-comm }
    ; F⇐G = record { η = λ A → id {A} ; commute = λ _ → id-comm-sym ; sym-commute = λ _ → id-comm }
    ; iso = λ X → record { isoˡ = identity² ; isoʳ = identity² }
    }

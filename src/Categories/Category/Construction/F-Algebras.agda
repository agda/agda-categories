{-# OPTIONS --universe-polymorphism #-}
module Categories.Category.Construction.F-Algebras where

open import Level
open import Data.Product using (proj₁; proj₂)

open import Categories.Category
open import Categories.Functor hiding (id)
open import Categories.Functor.Algebra
open import Categories.Object.Initial
import Categories.Morphism.Reasoning as MR
import Categories.Morphism as Mor using (_≅_)

private
  variable
    o ℓ e : Level
    𝒞 : Category o ℓ e

F-Algebras : {𝒞 : Category o ℓ e} → Endofunctor 𝒞 → Category (ℓ ⊔ o) (e ⊔ ℓ) e
F-Algebras {𝒞 = 𝒞} F = record
  { Obj       = F-Algebra F
  ; _⇒_       = F-Algebra-Morphism
  ; _≈_       = λ α₁ α₂ → f α₁ ≈ f α₂
  ; _∘_       = λ α₁ α₂ → record { f = f α₁ ∘ f α₂ ; commutes = commut α₁ α₂ }
  ; id        = record { f = id ; commutes = id-comm-sym ○ ⟺ (∘-resp-≈ʳ identity) }
  ; assoc     = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv     = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }
  ; ∘-resp-≈  = ∘-resp-≈
  }
  where
    open Category 𝒞
    open MR 𝒞
    open HomReasoning
    open Equiv
    open Functor F
    open F-Algebra-Morphism
    open F-Algebra
    commut : {A B C : F-Algebra F} (α₁ : F-Algebra-Morphism B C) (α₂ : F-Algebra-Morphism A B) →
      (f α₁ ∘ f α₂) ∘ α A ≈ α C ∘ F₁ (f α₁ ∘ f α₂)
    commut {A} {B} {C} α₁ α₂ = begin
      (f α₁ ∘ f α₂) ∘ α A            ≈⟨ pullʳ (commutes α₂) ⟩
      f α₁ ∘ (α B ∘ F₁ (f α₂))       ≈⟨ pullˡ (commutes α₁) ⟩
      (α C ∘ F₁ (f α₁)) ∘ F₁ (f α₂)  ≈⟨ pullʳ (⟺ homomorphism) ⟩
      α C ∘ F₁ (f α₁ ∘ f α₂)   ∎


module Lambek {𝒞 : Category o ℓ e} {F : Endofunctor 𝒞} (I : Initial (F-Algebras F)) where
  open Category 𝒞
  open Definitions 𝒞
  open Functor F
  open F-Algebra using (α)

  open MR 𝒞 using (glue)
  open Mor 𝒞
  open Initial I -- so ⊥ is an F-Algebra, which is initial

  -- While an expert might be able to decipher the proof at the nLab
  --   (https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor)
  -- I (JC) have found that the notes at
  --   http://www.cs.ru.nl/~jrot/coalgebra/ak-algebras.pdf
  -- are easier to follow, and lead to the full proof below.
  private
    module ⊥ = F-Algebra ⊥
    A = ⊥.A
    a : F₀ A ⇒ A
    a = ⊥.α

    -- The F-Algebra structure that will make things work
    F⊥ : F-Algebra F
    F⊥ = iterate ⊥

    -- By initiality, we get the following morphism
    f : F-Algebra-Morphism ⊥ F⊥
    f = !

    module FAM = F-Algebra-Morphism f

    i : A ⇒ F₀ A
    i = FAM.f

    a∘f : F-Algebra-Morphism ⊥ ⊥
    a∘f = record
      { f = a ∘ i
      ; commutes = glue triv FAM.commutes ○ ∘-resp-≈ʳ (⟺ homomorphism)
      }
      where
        open HomReasoning using (_○_; ⟺)
        triv : CommutativeSquare (α F⊥) (α F⊥) a a
        triv = Equiv.refl

  lambek : A ≅ F₀ A
  lambek = record
    { from = i
    ; to = a
    ; iso = record
      { isoˡ = ⊥-id a∘f
      ; isoʳ = begin
        i ∘ a       ≈⟨ F-Algebra-Morphism.commutes f ⟩
        F₁ a ∘ F₁ i ≈˘⟨ homomorphism ⟩
        F₁ (a ∘ i)  ≈⟨ F-resp-≈ (⊥-id a∘f) ⟩
        F₁ id       ≈⟨ identity ⟩
        id ∎
      }
    }
    where
      open HomReasoning

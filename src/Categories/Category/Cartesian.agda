{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category; module Commutation)

-- Defines the following properties of a Category:
-- Cartesian -- a Cartesian category is a category with all products

module Categories.Category.Cartesian {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level hiding (suc)
open import Data.Nat using (ℕ; zero; suc)

open Category 𝒞
open HomReasoning

open import Categories.Category.BinaryProducts 𝒞 using (BinaryProducts; module BinaryProducts)
open import Categories.Object.Terminal 𝒞 using (Terminal)
open import Categories.Object.Product.Core 𝒞 using (module Product)
open import Categories.Morphism 𝒞 using (_≅_; module ≅)
open import Categories.Morphism.Reasoning 𝒞 using (cancelˡ; pullʳ; pullˡ)
open import Categories.Category.Monoidal using (Monoidal)
import Categories.Category.Monoidal.Symmetric as Sym

open import Categories.Functor using (Functor) renaming (id to idF)
open import Categories.NaturalTransformation using (ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)

private
  variable
    A B C D W X Y Z : Obj
    f f′ g g′ h i : A ⇒ B

-- Cartesian monoidal category
record Cartesian : Set (levelOfTerm 𝒞) where
  field
    terminal : Terminal
    products : BinaryProducts

  private
    module products = BinaryProducts products
  open Terminal terminal public
  open products using (_×_; π₁; π₂; ⟨_,_⟩; product) public

  power : Obj → ℕ → Obj
  power A 0 = ⊤
  power A 1 = A
  power A (suc (suc n)) = A × power A (suc n)

-- The cartesian structure induces a monoidal one: 𝒞 is cartesian monoidal.

module CartesianMonoidal (cartesian : Cartesian) where
  open Commutation 𝒞
  open Cartesian cartesian using (⊤; !; !-unique; !-unique₂; products; π₁; π₂; ⟨_,_⟩)
  open BinaryProducts products using (_×_; _⁂_;
    _×-; -×_; ⟨⟩∘; ⟨⟩-cong₂; -×-; ×-assoc; assocˡ∘⁂; assocʳ∘⁂; ⁂∘⟨⟩;
    first∘⟨⟩; second∘⟨⟩; ⟨⟩-congˡ; ⟨⟩-congʳ; π₁∘⁂; π₂∘⁂; assocˡ∘⟨⟩;
    assocˡ; assocʳ;
    η; unique; project₁; project₂)

  ⊤×A≅A : ⊤ × A ≅ A
  ⊤×A≅A = record
    { from = π₂
    ; to   = ⟨ ! , id ⟩
    ; iso  = record
      { isoˡ = begin
        ⟨ ! , id ⟩ ∘ π₂ ≈˘⟨ unique !-unique₂ (cancelˡ project₂) ⟩
        ⟨ π₁ , π₂ ⟩     ≈⟨ η ⟩
        id              ∎
      ; isoʳ = project₂
      }
    }

  A×⊤≅A : A × ⊤ ≅ A
  A×⊤≅A = record
    { from = π₁
    ; to   = ⟨ id , ! ⟩
    ; iso  = record
      { isoˡ = begin
        ⟨ id , ! ⟩ ∘ π₁ ≈˘⟨ unique (cancelˡ project₁) !-unique₂ ⟩
        ⟨ π₁ , π₂ ⟩     ≈⟨ η ⟩
        id              ∎
      ; isoʳ = project₁
      }
    }

  ⊤×--id : NaturalIsomorphism (⊤ ×-) idF
  ⊤×--id = record
    { F⇒G = ntHelper record
      { η       = λ _ → π₂
      ; commute = λ _ → project₂
      }
    ; F⇐G = ntHelper record
      { η       = λ _ → ⟨ ! , id ⟩
      ; commute = λ f → begin
        ⟨ ! , id ⟩ ∘ f                                     ≈⟨ ⟨⟩∘ ⟩
        ⟨ ! ∘ f , id  ∘ f ⟩                                ≈⟨ ⟨⟩-cong₂ (⟺ (!-unique _)) identityˡ ⟩
        ⟨ ! , f ⟩                                          ≈˘⟨ ⟨⟩-cong₂ identityˡ identityʳ ⟩
        ⟨ id ∘ ! , f ∘ id ⟩                                ≈˘⟨ ⟨⟩-cong₂ (pullʳ project₁) (pullʳ project₂) ⟩
        ⟨ (id ∘ π₁) ∘ ⟨ ! , id ⟩ , (f ∘ π₂) ∘ ⟨ ! , id ⟩ ⟩ ≈˘⟨ ⟨⟩∘ ⟩
        ⟨ id ∘ π₁ , f ∘ π₂ ⟩ ∘ ⟨ ! , id ⟩                  ∎
      }
    ; iso = λ _ → _≅_.iso ⊤×A≅A
    }

  -×⊤-id : NaturalIsomorphism (-× ⊤) idF
  -×⊤-id = record
    { F⇒G = ntHelper record
      { η       = λ _ → π₁
      ; commute = λ _ → project₁
      }
    ; F⇐G = ntHelper record
      { η       = λ _ → ⟨ id , ! ⟩
      ; commute = λ f → begin
        ⟨ id , ! ⟩ ∘ f                                     ≈⟨ ⟨⟩∘ ⟩
        ⟨ id ∘ f , ! ∘ f ⟩                                 ≈⟨ ⟨⟩-cong₂ identityˡ (⟺ (!-unique _)) ⟩
        ⟨ f , ! ⟩                                          ≈˘⟨ ⟨⟩-cong₂ identityʳ identityˡ ⟩
        ⟨ f ∘ id , id ∘ ! ⟩                                ≈˘⟨ ⟨⟩-cong₂ (pullʳ project₁) (pullʳ project₂) ⟩
        ⟨ (f ∘ π₁) ∘ ⟨ id , ! ⟩ , (id ∘ π₂) ∘ ⟨ id , ! ⟩ ⟩ ≈˘⟨ ⟨⟩∘ ⟩
        ⟨ f ∘ π₁ , id ∘ π₂ ⟩ ∘ ⟨ id , ! ⟩                  ∎
      }
    ; iso = λ _ → _≅_.iso A×⊤≅A
    }
  private
    infixr 7 _⊗₀_
    infixr 8 _⊗₁_

    _⊗₀_ = _×_
    _⊗₁_ = _⁂_
    α⇒   = assocˡ

  private
   pentagon :  [ ((X ⊗₀ Y) ⊗₀ Z) ⊗₀ W ⇒ X ⊗₀ Y ⊗₀ Z ⊗₀ W ]⟨
                 α⇒ ⊗₁ id         ⇒⟨ (X ⊗₀ Y ⊗₀ Z) ⊗₀ W ⟩
                 α⇒               ⇒⟨ X ⊗₀ (Y ⊗₀ Z) ⊗₀ W ⟩
                 id ⊗₁ α⇒
               ≈ α⇒               ⇒⟨ (X ⊗₀ Y) ⊗₀ Z ⊗₀ W ⟩
                 α⇒
               ⟩
   pentagon             = begin
      (id ⁂ α⇒) ∘ α⇒ ∘ (α⇒ ⁂ id)                                        ≈⟨ pullˡ second∘⟨⟩ ⟩
      ⟨ π₁ ∘ π₁ , α⇒ ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩ ∘ (α⇒ ⁂ id)                     ≈⟨ ⟨⟩∘ ⟩
      ⟨ (π₁ ∘ π₁) ∘ (α⇒ ⁂ id) , (α⇒ ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩) ∘ (α⇒ ⁂ id) ⟩     ≈⟨ ⟨⟩-cong₂ (pullʳ π₁∘⁂) (pullʳ ⟨⟩∘) ⟩
      ⟨ π₁ ∘ α⇒ ∘ π₁ , α⇒ ∘ ⟨ (π₂ ∘ π₁) ∘ (α⇒ ⁂ id) , π₂ ∘ (α⇒ ⁂ id) ⟩ ⟩  ≈⟨ ⟨⟩-cong₂ (pullˡ project₁) ( refl⟩∘⟨ ⟨⟩-cong₂ (pullʳ π₁∘⁂) π₂∘⁂) ⟩
      ⟨ (π₁ ∘ π₁) ∘ π₁ , α⇒ ∘ ⟨ π₂ ∘ α⇒ ∘ π₁ , id ∘ π₂ ⟩ ⟩                ≈⟨ ⟨⟩-cong₂ assoc (refl⟩∘⟨ ⟨⟩-cong₂ (pullˡ project₂) identityˡ) ⟩
      ⟨ π₁₁₁ , α⇒ ∘ ⟨ ⟨ π₂ ∘ π₁ , π₂ ⟩ ∘ π₁ , π₂ ⟩ ⟩                       ≈⟨ ⟨⟩-congˡ (refl⟩∘⟨ ⟨⟩-congʳ ⟨⟩∘) ⟩
      ⟨ π₁₁₁ , α⇒ ∘ ⟨ ⟨ (π₂ ∘ π₁) ∘ π₁ , π₂ ∘ π₁ ⟩ , π₂ ⟩ ⟩                ≈⟨ ⟨⟩-congˡ assocˡ∘⟨⟩ ⟩
      ⟨ π₁₁₁ , ⟨ (π₂ ∘ π₁) ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩ ⟩                      ≈˘⟨ ⟨⟩-congˡ (⟨⟩-cong₂ (Equiv.trans (pullʳ project₁) sym-assoc) project₂) ⟩
      ⟨ π₁₁₁ , ⟨ (π₂ ∘ π₁) ∘ α⇒ , π₂ ∘ α⇒ ⟩ ⟩                             ≈˘⟨ ⟨⟩-cong₂ (pullʳ project₁) ⟨⟩∘ ⟩
      ⟨ (π₁ ∘ π₁) ∘ α⇒ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ∘ α⇒ ⟩                          ≈˘⟨ ⟨⟩∘ ⟩
      α⇒ ∘ α⇒                                                           ∎
      where
        π₁₁₁ = π₁ ∘ π₁ ∘ π₁

  monoidal : Monoidal 𝒞
  monoidal = record
    { ⊗                    = -×-
    ; unit                 = ⊤
    ; unitorˡ              = ⊤×A≅A
    ; unitorʳ              = A×⊤≅A
    ; associator           = ≅.sym ×-assoc
    ; unitorˡ-commute-from = project₂
    ; unitorˡ-commute-to   = let open NaturalIsomorphism ⊤×--id in ⇐.commute _
    ; unitorʳ-commute-from = project₁
    ; unitorʳ-commute-to   = let open NaturalIsomorphism -×⊤-id in ⇐.commute _
    ; assoc-commute-from   = assocˡ∘⁂
    ; assoc-commute-to     = assocʳ∘⁂
    ; triangle             = begin
      (id ⁂ π₂) ∘ assocˡ                       ≈⟨ ⁂∘⟨⟩ ⟩
      ⟨ id ∘ π₁ ∘ π₁ , π₂ ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩ ≈⟨ ⟨⟩-cong₂ (pullˡ identityˡ) (project₂ ○ (⟺ identityˡ)) ⟩
      π₁ ⁂ id                                  ∎
    ; pentagon             = pentagon
    }

module CartesianSymmetricMonoidal (cartesian : Cartesian) where
  open Cartesian cartesian using (products; π₁; π₂; ⟨_,_⟩)
  open CartesianMonoidal cartesian using (monoidal)
  open Sym monoidal using (Symmetric; symmetricHelper)
  open Monoidal monoidal using (_⊗₁_)
  open BinaryProducts products hiding (⟨_,_⟩; π₁; π₂)

  symmetric : Symmetric
  symmetric = symmetricHelper record
    { braiding    = record
      { F⇒G = ntHelper record
        { η       = λ _ → swap
        ; commute = λ _ → swap∘⁂
        }
      ; F⇐G = ntHelper record
        { η       = λ _ → swap
        ; commute = λ _ → swap∘⁂
        }
      ; iso = λ _ → record
        { isoˡ = swap∘swap
        ; isoʳ = swap∘swap
        }
      }
    ; commutative = swap∘swap
    ; hexagon     = begin
        id ⊗₁ swap ∘ assocˡ ∘ swap ⊗₁ id                        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟨⟩-congʳ ⟨⟩∘ ⟩
        id ⊗₁ swap ∘ assocˡ ∘ ⟨ ⟨ π₂ ∘ π₁ , π₁ ∘ π₁ ⟩ , id ∘ π₂ ⟩ ≈⟨ refl⟩∘⟨ assocˡ∘⟨⟩ ⟩
        id ⊗₁ swap ∘ ⟨ π₂ ∘ π₁ , ⟨ π₁ ∘ π₁ , id ∘ π₂ ⟩ ⟩          ≈⟨ ⁂∘⟨⟩ ⟩
        ⟨ id ∘ π₂ ∘ π₁ , swap ∘ ⟨ π₁ ∘ π₁ , id ∘ π₂ ⟩ ⟩           ≈⟨ ⟨⟩-cong₂ identityˡ swap∘⟨⟩ ⟩
        ⟨ π₂ ∘ π₁ , ⟨ id ∘ π₂ , π₁ ∘ π₁ ⟩ ⟩                       ≈⟨ ⟨⟩-congˡ (⟨⟩-congʳ identityˡ) ⟩
        ⟨ π₂ ∘ π₁ , ⟨ π₂ , π₁ ∘ π₁ ⟩ ⟩                            ≈˘⟨ assocˡ∘⟨⟩ ⟩
        assocˡ ∘ ⟨ ⟨ π₂ ∘ π₁ , π₂ ⟩ , π₁ ∘ π₁ ⟩                   ≈˘⟨ refl⟩∘⟨ swap∘⟨⟩ ⟩
        assocˡ ∘ swap ∘ assocˡ                                    ∎
    }

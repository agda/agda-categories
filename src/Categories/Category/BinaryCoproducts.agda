{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)

-- Defines BinaryCoproducts -- for when a Category has all Binary Coproducts

-- Most of the work is dual to Categories.Category.BinaryProducts, so the idea
-- in this module is to make use of duality

module Categories.Category.BinaryCoproducts {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level using (levelOfTerm)

open Category 𝒞

open import Categories.Object.Coproduct 𝒞
open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Morphism 𝒞 using (_≅_)
open import Categories.Morphism.Duality 𝒞
open import Categories.Object.Duality 𝒞

open import Categories.Functor using (Functor) renaming (id to idF)
open import Categories.Functor.Bifunctor using (Bifunctor; appʳ; appˡ)

private
  variable
    A B C : Obj

record BinaryCoproducts : Set (levelOfTerm 𝒞) where
  field
    coproduct : ∀ {A B} → Coproduct A B

  module _ (A B : Obj) where 
    open Coproduct (coproduct {A} {B})
      renaming (A+B to infixr 6 _+_)
      using ()
      public

  module _ {A B : Obj} where
    open Coproduct (coproduct {A} {B})
      using (i₁; i₂; [_,_]; inject₁; inject₂; []-cong₂; ∘-distribˡ-[]) 
      renaming (unique to +-unique; η to +-η; g-η to +-g-η) 
      public 

  module Dual where
    op-binaryProducts : BinaryProducts op
    op-binaryProducts = record { product = Coproduct⇒coProduct coproduct }

    module op-binaryProducts = BinaryProducts op-binaryProducts

  open Dual

  +-comm : A + B ≅ B + A
  +-comm = op-≅⇒≅ (op-binaryProducts.×-comm)

  +-assoc : A + B + C ≅ (A + B) + C
  +-assoc = op-≅⇒≅ (op-binaryProducts.×-assoc)

  -- Don't use Dual.op-binaryProducts here, since it makes Agda solve with
  -- Dual.op-binaryProducts._⁂_ instead of +₁
  open BinaryProducts record { product = Coproduct⇒coProduct coproduct }
    using ()
    renaming ( _⁂_          to infixr 7 _+₁_
             ; ⟨⟩-congʳ     to []-congʳ
             ; ⟨⟩-congˡ     to []-congˡ
             ; assocˡ       to +-assocʳ
             ; assocʳ       to +-assocˡ
             ; assocˡ∘assocʳ to +-assocˡ∘+-assocʳ
             ; assocʳ∘assocˡ to +-assocʳ∘+-assocˡ
             ; swap         to +-swap
             ; first        to +-first
             ; second       to +-second
             ; π₁∘⁂         to +₁∘i₁
             ; π₂∘⁂         to +₁∘i₂
             ; ⁂-cong₂      to +₁-cong₂
             ; ⁂∘⟨⟩         to []∘+₁
             ; first∘⟨⟩     to []∘+-first
             ; second∘⟨⟩    to []∘+-second
             ; ⁂∘⁂          to +₁∘+₁
             ; ⟨⟩∘          to ∘[]
             ; first∘first  to +-first∘+-first
             ; second∘second to +-second∘+-second
             ; first∘second to +-first∘+-second
             ; second∘first to +-second∘+-first
             ; first↔second to +-second↔+-first
             ; firstid      to +-firstid
             ; swap∘⟨⟩      to []∘+-swap
             ; swap∘⁂       to +₁∘+-swap
             ; swap∘swap    to +-swap∘+-swap
             ; swap-epi     to +-swap-epi
             ; swap-mono    to +-swap-mono
             ; assocʳ∘⟨⟩    to []∘+-assocʳ
             ; assocˡ∘⟨⟩    to []∘+-assocˡ
             ; assocʳ∘⁂     to +₁∘+-assocʳ
             ; assocˡ∘⁂     to +₁∘+-assocˡ
             ; Δ            to ∇
             ; Δ∘           to ∘∇
             ; ⁂∘Δ          to ∇∘+₁
             )
    public

  -- since op-×- has type Bifunctor 𝒞.op 𝒞.op 𝒞.op,
  -- need to rewrap in order to type check
  -+- : Bifunctor 𝒞 𝒞 𝒞
  -+- = record
    { F₀           = op-×-.F₀
    ; F₁           = op-×-.F₁
    ; identity     = op-×-.identity
    ; homomorphism = op-×-.homomorphism
    ; F-resp-≈     = op-×-.F-resp-≈
    }
    where op-×- = op-binaryProducts.-×-
          module op-×- = Functor op-×-

  -+_ : Obj → Functor 𝒞 𝒞
  -+_ = appʳ -+-

  _+- : Obj → Functor 𝒞 𝒞
  _+- = appˡ -+-
{-# OPTIONS --without-K --safe #-}
module Categories.Category.Construction.Grothendieck where

-- The simpler construction of a Category from a Functor into Cats, as a (weak) 1-Category
open import Level
open import Data.Product using (Σ; _,_; Σ-syntax; proj₁; proj₂; map; _×_)
open import Function using (_$_) renaming (_∘_ to _●_)

open import Categories.Category
open import Categories.Category.Instance.Cats
open import Categories.Functor renaming (id to idF)
open import Categories.NaturalTransformation hiding (id)
open import Categories.NaturalTransformation.NaturalIsomorphism

private
  variable
    o ℓ e o′ ℓ′ e′ : Level

Grothendieck : {C : Category o ℓ e} → Functor C (Cats o′ ℓ′ e′) → Category (o ⊔ o′) (ℓ ⊔ ℓ′) e
Grothendieck {C = C} F = record
  { Obj = Σ Obj (λ c → Category.Obj $ F₀ c)
  ; _⇒_ = λ { (c , a) (c′ , a′) →
          Σ (c ⇒ c′) (λ f →  let module D = Category (F₀ c′) in
                              Functor.F₀ (F₁ f) a D.⇒ a′)  }
  ; _≈_ = λ x y → proj₁ x ≈ proj₁ y -- because the other half is always provably ≈
  ; id = λ { {c , a} → id , (η $ F⇒G $ identity {c}) a}
  ; _∘_ = λ { {_ , a₁} {_ , a₂} {c₃ , a₃} (u , f) (v , g) → u ∘ v ,
          let module E = Category (F₀ c₃) in f E.∘ Functor.F₁ (F₁ u) g E.∘ (η $ F⇒G homomorphism) a₁ }
  ; assoc = assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; equiv = record { refl = Equiv.refl ; sym = Equiv.sym ; trans = Equiv.trans }
  ; ∘-resp-≈ = ∘-resp-≈
  }
  where
  open Category C
  open Functor F
  open NaturalIsomorphism
  open NaturalTransformation

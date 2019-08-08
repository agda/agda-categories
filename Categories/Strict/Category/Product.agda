{-# OPTIONS --without-K --safe #-}
module Categories.Strict.Category.Product where

open import Level
open import Function using () renaming (_∘_ to _∙_)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂; zip; map; <_,_>; swap)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)

open import Categories.Utils.Product
open import Categories.Strict.Category using (Category)
open import Categories.Strict.Functor renaming (id to idF)

private
  variable
    o ℓ o′ ℓ′ o″ ℓ″ : Level
    o₁ ℓ₁ o′₁ ℓ′₁ o₂ ℓ₂ o′₂ ℓ′₂ : Level

    C C₁ C₂ D D₁ D₂ : Category o ℓ

Product : (C : Category o ℓ) (D : Category o′ ℓ′) → Category (o ⊔ o′) (ℓ ⊔ ℓ′)
Product C D = record
  { Obj       = C.Obj × D.Obj
  ; _⇒_       = C._⇒_ -< _×_ >- D._⇒_
  ; _∘_       = zip C._∘_ D._∘_
  ; id        = C.id , D.id
  ; assoc     = cong₂ _,_ C.assoc D.assoc
  ; identityˡ = cong₂ _,_ C.identityˡ D.identityˡ
  ; identityʳ = cong₂ _,_ C.identityʳ D.identityʳ
  }
  where module C = Category C
        module D = Category D

-- product of functors sharing the same domain
infixr 2 _※_
_※_ : ∀ (F : Functor C D₁) → (G : Functor C D₂) → Functor C (Product D₁ D₂)
F ※ G = record
  { F₀           = < F.F₀ , G.F₀ >
  ; F₁           = < F.F₁ , G.F₁ >
  ; identity     = cong₂ _,_ F.identity G.identity
  ; homomorphism = cong₂ _,_ F.homomorphism G.homomorphism
  }
  where module F = Functor F
        module G = Functor G

-- general product of functors
infixr 2 _⁂_
_⁂_ : ∀ (F₁ : Functor C₁ D₁) (F₂ : Functor C₂ D₂) → Functor (Product C₁ C₂) (Product D₁ D₂)
F ⁂ G = record
  { F₀           = map F.F₀ G.F₀
  ; F₁           = map F.F₁ G.F₁
  ; identity     = cong₂ _,_ F.identity G.identity
  ; homomorphism = cong₂ _,_ F.homomorphism G.homomorphism
  }
  where module F = Functor F
        module G = Functor G
{-
-- Natural Transformations respect the ⁂ product
infixr 5 _⁂ⁿ_
_⁂ⁿ_ : ∀ {C₁ : Category o₁ ℓ₁ e₁} {D₁ : Category o′₁ ℓ′₁ e′₁}
         {C₂ : Category o₂ ℓ₂ e₂} {D₂ : Category o′₂ ℓ′₂ e′₂}
         {F₁ G₁ : Functor C₁ D₁} {F₂ G₂ : Functor C₂ D₂}
         (α : NaturalTransformation F₁ G₁) (β : NaturalTransformation F₂ G₂) →
         NaturalTransformation (F₁ ⁂ F₂) (G₁ ⁂ G₂)
α ⁂ⁿ β = record
  { η       = map⁎′ α.η β.η
  ; commute = map⁎′ α.commute β.commute
  }
  where module α = NaturalTransformation α
        module β = NaturalTransformation β

-- Natural Transformations respect the ※ product as well
infixr 5 _※ⁿ_
_※ⁿ_ : ∀ {D₁ : Category o ℓ e} {D₂ : Category o′ ℓ′ e′}
         {F₁ G₁ : Functor C D₁} {F₂ G₂ : Functor C D₂}
         (α : NaturalTransformation F₁ G₁) →
         (β : NaturalTransformation F₂ G₂) →
         NaturalTransformation (F₁ ※ F₂) (G₁ ※ G₂)
α ※ⁿ β = record
  { η       = < α.η , β.η >
  ; commute = < α.commute , β.commute >
  }
  where module α = NaturalTransformation α
        module β = NaturalTransformation β

-- Natural Isomorphisms too
infixr 5 _⁂ⁿⁱ_
_⁂ⁿⁱ_ : ∀ {C₁ : Category o₁ ℓ₁ e₁} {D₁ : Category o′₁ ℓ′₁ e′₁}
          {C₂ : Category o₂ ℓ₂ e₂} {D₂ : Category o′₂ ℓ′₂ e′₂}
          {F₁ G₁ : Functor C₁ D₁} {F₂ G₂ : Functor C₂ D₂}
          (α : NaturalIsomorphism F₁ G₁) (β : NaturalIsomorphism F₂ G₂) →
          NaturalIsomorphism (F₁ ⁂ F₂) (G₁ ⁂ G₂)
α ⁂ⁿⁱ β = record
  { F⇒G = α.F⇒G ⁂ⁿ β.F⇒G
  ; F⇐G = α.F⇐G ⁂ⁿ β.F⇐G
  ; iso = λ where
    (X , Y) → record
      { isoˡ = isoˡ (α.iso X) , isoˡ (β.iso Y)
      ; isoʳ = isoʳ (α.iso X) , isoʳ (β.iso Y)
      }
  }
  where module α = NaturalIsomorphism α
        module β = NaturalIsomorphism β
        open Morphism.Iso

-- Natural Isomorphisms too
infixr 5 _※ⁿⁱ_
_※ⁿⁱ_ : ∀ {D₁ : Category o ℓ e} {D₂ : Category o′ ℓ′ e′}
          {F₁ G₁ : Functor C D₁} {F₂ G₂ : Functor C D₂}
          (α : NaturalIsomorphism F₁ G₁) →
          (β : NaturalIsomorphism F₂ G₂) →
          NaturalIsomorphism (F₁ ※ F₂) (G₁ ※ G₂)
α ※ⁿⁱ β = record
  { F⇒G = α.F⇒G ※ⁿ β.F⇒G
  ; F⇐G = α.F⇐G ※ⁿ β.F⇐G
  ; iso = λ X → record
    { isoˡ = isoˡ (α.iso X) , isoˡ (β.iso X)
    ; isoʳ = isoʳ (α.iso X) , isoʳ (β.iso X)
    }
  }
  where module α = NaturalIsomorphism α
        module β = NaturalIsomorphism β
        open Morphism.Iso

module _ (C₁ : Category o ℓ e) (C₂ : Category o′ ℓ′ e′) (C₃ : Category o″ ℓ″ e″) where

  module C₁ = Category C₁
  module C₂ = Category C₂
  module C₃ = Category C₃

  assocˡ : Functor (Product (Product C₁ C₂) C₃) (Product C₁ (Product C₂ C₃))
  assocˡ = record
    { F₀           = < proj₁ ∙ proj₁ , < proj₂ ∙ proj₁ , proj₂ > >
    ; F₁           = < proj₁ ∙ proj₁ , < proj₂ ∙ proj₁ , proj₂ > >
    ; identity     = C₁.Equiv.refl , C₂.Equiv.refl , C₃.Equiv.refl
    ; homomorphism = C₁.Equiv.refl , C₂.Equiv.refl , C₃.Equiv.refl
    ; F-resp-≈     = < proj₁ ∙ proj₁ , < proj₂ ∙ proj₁ , proj₂ > >
    }

  assocʳ : Functor (Product C₁ (Product C₂ C₃)) (Product (Product C₁ C₂) C₃)
  assocʳ = record
    { F₀           = < < proj₁ , proj₁ ∙ proj₂ > , proj₂ ∙ proj₂ >
    ; F₁           = < < proj₁ , proj₁ ∙ proj₂ > , proj₂ ∙ proj₂ >
    ; identity     = (C₁.Equiv.refl , C₂.Equiv.refl) , C₃.Equiv.refl
    ; homomorphism = (C₁.Equiv.refl , C₂.Equiv.refl) , C₃.Equiv.refl
    ; F-resp-≈     = < < proj₁ , proj₁ ∙ proj₂ > , proj₂ ∙ proj₂ >
    }
-}

-- Might be able to elide all the refl fields below?
module _ {C : Category o ℓ} {D : Category o′ ℓ′} where

  private
    module C = Category C
    module D = Category D

  πˡ : Functor (Product C D) C
  πˡ = record
    { F₀           = proj₁
    ; F₁           = proj₁
    ; identity     = refl
    ; homomorphism = refl
    }

  πʳ : Functor (Product C D) D
  πʳ = record
    { F₀           = proj₂
    ; F₁           = proj₂
    ; identity     = refl
    ; homomorphism = refl
    }

  Swap : Functor (Product C D) (Product D C)
  Swap = record
    { F₀           = swap
    ; F₁           = swap
    ; identity     = refl
    ; homomorphism = refl
    }

{-# OPTIONS --without-K --safe #-}
module Categories.Category.Product where

open import Level
open import Function using () renaming (_∘_ to _∙_)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂; zip; map; <_,_>; swap)

open import Categories.Utils.Product
open import Categories.Category using (Category)
open import Categories.Category.Groupoid using (IsGroupoid)
open import Categories.Functor renaming (id to idF)
open import Categories.NaturalTransformation.Core
open import Categories.NaturalTransformation.NaturalIsomorphism hiding (refl)
import Categories.Morphism as Morphism

private
  variable
    o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ : Level
    o₁ ℓ₁ e₁ o′₁ ℓ′₁ e′₁ o₂ ℓ₂ e₂ o′₂ ℓ′₂ e′₂ : Level

    C C₁ C₂ D D₁ D₂ : Category o ℓ e

Product : (C : Category o ℓ e) (D : Category o′ ℓ′ e′) → Category (o ⊔ o′) (ℓ ⊔ ℓ′) (e ⊔ e′)
Product C D = record
  { Obj       = C.Obj × D.Obj
  ; _⇒_       = C._⇒_ -< _×_ >- D._⇒_
  ; _≈_       = C._≈_ -< _×_ >- D._≈_
  ; _∘_       = zip C._∘_ D._∘_
  ; id        = C.id , D.id
  ; assoc     = C.assoc , D.assoc
  ; sym-assoc = C.sym-assoc , D.sym-assoc
  ; identityˡ = C.identityˡ , D.identityˡ
  ; identityʳ = C.identityʳ , D.identityʳ
  ; identity² = C.identity² , D.identity²
  ; equiv     = record
    { refl  = C.Equiv.refl , D.Equiv.refl
    ; sym   = map C.Equiv.sym D.Equiv.sym
    ; trans = zip C.Equiv.trans D.Equiv.trans
    }
  ; ∘-resp-≈  = zip C.∘-resp-≈ D.∘-resp-≈
  }
  where module C = Category C
        module D = Category D

-- product of functors sharing the same domain
infixr 2 _※_
_※_ : ∀ (F : Functor C D₁) → (G : Functor C D₂) → Functor C (Product D₁ D₂)
F ※ G = record
  { F₀           = < F.F₀ , G.F₀ >
  ; F₁           = < F.F₁ , G.F₁ >
  ; identity     = F.identity , G.identity
  ; homomorphism = F.homomorphism , G.homomorphism
  ; F-resp-≈     = < F.F-resp-≈ , G.F-resp-≈ >
  }
  where module F = Functor F
        module G = Functor G

-- general product of functors
infixr 2 _⁂_
_⁂_ : ∀ (F₁ : Functor C₁ D₁) (F₂ : Functor C₂ D₂) → Functor (Product C₁ C₂) (Product D₁ D₂)
F ⁂ G = record
  { F₀           = map F.F₀ G.F₀
  ; F₁           = map F.F₁ G.F₁
  ; identity     = F.identity , G.identity
  ; homomorphism = F.homomorphism , G.homomorphism
  ; F-resp-≈     = map F.F-resp-≈ G.F-resp-≈
  }
  where module F = Functor F
        module G = Functor G

-- Natural Transformations respect the ⁂ product
infixr 5 _⁂ⁿ_
_⁂ⁿ_ : ∀ {C₁ : Category o₁ ℓ₁ e₁} {D₁ : Category o′₁ ℓ′₁ e′₁}
         {C₂ : Category o₂ ℓ₂ e₂} {D₂ : Category o′₂ ℓ′₂ e′₂}
         {F₁ G₁ : Functor C₁ D₁} {F₂ G₂ : Functor C₂ D₂}
         (α : NaturalTransformation F₁ G₁) (β : NaturalTransformation F₂ G₂) →
         NaturalTransformation (F₁ ⁂ F₂) (G₁ ⁂ G₂)
α ⁂ⁿ β = ntHelper record
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
α ※ⁿ β = ntHelper record
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

  private
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

module _ {C : Category o ℓ e} {D : Category o′ ℓ′ e′} where

  private
    module C = Category C
    module D = Category D

  πˡ : Functor (Product C D) C
  πˡ = record
    { F₀           = proj₁
    ; F₁           = proj₁
    ; identity     = refl
    ; homomorphism = refl
    ; F-resp-≈     = proj₁
    }
    where open C.Equiv using (refl)

  πʳ : Functor (Product C D) D
  πʳ = record
    { F₀           = proj₂
    ; F₁           = proj₂
    ; identity     = refl
    ; homomorphism = refl
    ; F-resp-≈     = proj₂
    }
    where open D.Equiv using (refl)

  Swap : Functor (Product C D) (Product D C)
  Swap = record
    { F₀           = swap
    ; F₁           = swap
    ; identity     = D.Equiv.refl , C.Equiv.refl
    ; homomorphism = D.Equiv.refl , C.Equiv.refl
    ; F-resp-≈     = swap
    }

-- Groupoid Product
Groupoid-× : {C : Category o₁ ℓ₁ e₁} {D : Category o₂ ℓ₂ e₂}
        → IsGroupoid C → IsGroupoid D → IsGroupoid (Product C D)
Groupoid-× c₁ c₂ = record
    { _⁻¹ = map (IsGroupoid._⁻¹ c₁) (IsGroupoid._⁻¹ c₂)
    ; iso = record { isoˡ = Iso.isoˡ i₁ , Iso.isoˡ i₂
                   ; isoʳ = Iso.isoʳ i₁ , Iso.isoʳ i₂
                   }
    }
  where
  open Morphism
  i₁ = IsGroupoid.iso c₁
  i₂ = IsGroupoid.iso c₂

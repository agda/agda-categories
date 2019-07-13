{-# OPTIONS --without-K --safe #-}
module Categories.Adjoint where

-- Adjoints

open import Level using (Level; _⊔_; levelOfTerm)

open import Data.Product using (_,_; _×_)
open import Function using () renaming (_∘_ to _∙_)
open import Function.Inverse using (Inverse)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)

-- be explicit in imports to 'see' where the information comes from
open import Categories.Category using (Category)
open import Categories.Category.Product using (Product; _⁂_)
open import Categories.Category.Instance.Setoids
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.Functor.Hom using (Hom[_][-,-])
open import Categories.NaturalTransformation using (NaturalTransformation; _≃_) renaming (id to idN)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (NaturalIsomorphism; unitorˡ; unitorʳ)
import Categories.Square as Square

private
  variable
    o ℓ e : Level
    C D : Category o ℓ e

record Adjoint (L : Functor C D) (R : Functor D C) : Set (levelOfTerm C ⊔ levelOfTerm D) where
  private
    module C = Category C
    module D = Category D
    module L = Functor L
    module R = Functor R

  field
    unit   : NaturalTransformation idF (R ∘F L)
    counit : NaturalTransformation (L ∘F R) idF

  module unit = NaturalTransformation unit
  module counit = NaturalTransformation counit

  field
    zig : ∀ {A : C.Obj} → counit.η (L.F₀ A) D.∘ L.F₁ (unit.η A) D.≈ D.id
    zag : ∀ {B : D.Obj} → R.F₁ (counit.η B) C.∘ unit.η (R.F₀ B) C.≈ C.id

  private
    variable
      A : C.Obj
      B : D.Obj

  Ladjunct : L.F₀ A D.⇒ B → A C.⇒ R.F₀ B
  Ladjunct f = R.F₁ f C.∘ unit.η _

  Radjunct : A C.⇒ R.F₀ B → L.F₀ A D.⇒ B
  Radjunct f = counit.η _ D.∘ L.F₁ f

  RLadjunct≈id : ∀ {f : L.F₀ A D.⇒ B} → Radjunct (Ladjunct f) D.≈ f
  RLadjunct≈id {f = f} = begin
    Radjunct (Ladjunct f)                            ≈⟨ refl⟩∘⟨ L.homomorphism ⟩
    counit.η _ D.∘ L.F₁ (R.F₁ f) D.∘ L.F₁ (unit.η _) ≈⟨ pullˡ (counit.commute f) ⟩
    (f D.∘ counit.η _) D.∘ L.F₁ (unit.η _)           ≈⟨ pullʳ zig ⟩
    f D.∘ D.id                                       ≈⟨ D.identityʳ ⟩
    f                                                ∎
    where open D.HomReasoning
          open Square D

  LRadjunct≈id : ∀ {f : A C.⇒ R.F₀ B} → Ladjunct (Radjunct f) C.≈ f
  LRadjunct≈id {f = f} = begin
    Ladjunct (Radjunct f)                              ≈⟨ R.homomorphism ⟩∘⟨refl ⟩
    (R.F₁ (counit.η _) C.∘ R.F₁ (L.F₁ f)) C.∘ unit.η _ ≈˘⟨ pushʳ (unit.commute f) ⟩
    R.F₁ (counit.η _) C.∘ unit.η _ C.∘ f               ≈⟨ pullˡ zag ⟩
    C.id C.∘ f                                         ≈⟨ C.identityˡ ⟩
    f                                                  ∎
    where open C.HomReasoning
          open Square C

  Hom[L-,-] : Bifunctor C.op D (Setoids _ _)
  Hom[L-,-] = Hom[ D ][-,-] ∘F (L.op ⁂ idF)

  Hom[-,R-] : Bifunctor C.op D (Setoids _ _)
  Hom[-,R-] = Hom[ C ][-,-] ∘F (idF ⁂ R)

  module Hom[L-,-] = Functor Hom[L-,-]
  module Hom[-,R-] = Functor Hom[-,R-]

  -- Inverse is more 'categorical' than bijection defined via injection/surjection
  Hom-inverse : ∀ A B → Inverse (Hom[L-,-].F₀ (A , B)) (Hom[-,R-].F₀ (A , B))
  Hom-inverse A B = record
    { to = record
      { _⟨$⟩_ = Ladjunct {A} {B}
      ; cong = C.∘-resp-≈ˡ ∙ R.F-resp-≈
      }
    ; from = record
      { _⟨$⟩_ = Radjunct {A} {B}
      ; cong = D.∘-resp-≈ʳ ∙ L.F-resp-≈
      }
    ; inverse-of = record
      { left-inverse-of = λ _ → RLadjunct≈id
      ; right-inverse-of = λ _ → LRadjunct≈id
      }
    }

  module Hom-inverse {A} {B} = Inverse (Hom-inverse A B)

  op : Adjoint R.op L.op
  op = record
    { unit   = counit.op
    ; counit = unit.op
    ; zig    = zag
    ; zag    = zig
    }

infix 5 _⊣_
_⊣_ = Adjoint

⊣-id : idF {C = C} ⊣ idF {C = C}
⊣-id {C = C} = record
  { unit   = F⇐G unitorˡ
  ; counit = F⇒G unitorʳ
  ; zig    = identityˡ
  ; zag    = identityʳ
  }
  where open Category C
        open NaturalIsomorphism

-- Do we really need a specific equivalence relation on Adjoints?
infix 4 _≊_
_≊_ : ∀ {L : Functor C D} {R : Functor D C} → Rel (L ⊣ R) _
_≊_ A B = A.unit ≃ B.unit × A.counit ≃ B.counit
  where module A = Adjoint A
        module B = Adjoint B

module _ {L : Functor C D} {R : Functor D C} where

  private
    module C = Category C
    module D = Category D

  ≊-isEquivalence : IsEquivalence (_≊_ {L = L} {R})
  ≊-isEquivalence = record
    { refl  = C.Equiv.refl , D.Equiv.refl
    ; sym   = λ where
      (eq₁ , eq₂) → C.Equiv.sym eq₁ , D.Equiv.sym eq₂
    ; trans = λ where
      (eql₁ , eqr₁) (eql₂ , eqr₂) →
        C.Equiv.trans eql₁ eql₂ , D.Equiv.trans eqr₁ eqr₂
    }

  ≊-setoid : Setoid _ _
  ≊-setoid = record
    { Carrier       = L ⊣ R
    ; _≈_           = _
    ; isEquivalence = ≊-isEquivalence
    }

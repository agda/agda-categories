{-# OPTIONS --without-K --safe #-}
module Categories.Adjoint where

-- Adjoints

open import Level

open import Data.Product using (_,_; _×_)
open import Function using (_$_) renaming (_∘_ to _∙_)
import Function.Inverse as FI
open import Relation.Binary using (Rel; IsEquivalence; Setoid)

-- be explicit in imports to 'see' where the information comes from
open import Categories.Category using (Category)
open import Categories.Category.Product using (Product; _⁂_)
open import Categories.Category.Instance.Setoids
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.Functor.Hom using (Hom[_][-,-])
open import Categories.Functor.Construction.LiftSetoids
open import Categories.NaturalTransformation using (NaturalTransformation; _≃_) renaming (id to idN)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (NaturalIsomorphism; unitorˡ; unitorʳ)
import Categories.Morphism.Reasoning as MR

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
          open MR D

  LRadjunct≈id : ∀ {f : A C.⇒ R.F₀ B} → Ladjunct (Radjunct f) C.≈ f
  LRadjunct≈id {f = f} = begin
    Ladjunct (Radjunct f)                              ≈⟨ R.homomorphism ⟩∘⟨refl ⟩
    (R.F₁ (counit.η _) C.∘ R.F₁ (L.F₁ f)) C.∘ unit.η _ ≈˘⟨ pushʳ (unit.commute f) ⟩
    R.F₁ (counit.η _) C.∘ unit.η _ C.∘ f               ≈⟨ pullˡ zag ⟩
    C.id C.∘ f                                         ≈⟨ C.identityˡ ⟩
    f                                                  ∎
    where open C.HomReasoning
          open MR C

  Hom[L-,-] : Bifunctor C.op D (Setoids _ _)
  Hom[L-,-] = Hom[ D ][-,-] ∘F (L.op ⁂ idF)

  Hom[-,R-] : Bifunctor C.op D (Setoids _ _)
  Hom[-,R-] = Hom[ C ][-,-] ∘F (idF ⁂ R)

  module Hom[L-,-] = Functor Hom[L-,-]
  module Hom[-,R-] = Functor Hom[-,R-]

  -- Inverse is more 'categorical' than bijection defined via injection/surjection
  Hom-inverse : ∀ A B → FI.Inverse (Hom[L-,-].F₀ (A , B)) (Hom[-,R-].F₀ (A , B))
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

  module Hom-inverse {A} {B} = FI.Inverse (Hom-inverse A B)
  
  op : Adjoint R.op L.op
  op = record
    { unit   = counit.op
    ; counit = unit.op
    ; zig    = zag
    ; zag    = zig
    }

  -- a complication: the two hom functors do not live in the same Setoids,
  -- so they need to be maped to the same Setoids first before establishing
  -- natural isomorphism!
  module _ where
    private
      levelℓ : Category o ℓ e → Level
      levelℓ {ℓ = ℓ} _ = ℓ
  
      levele : Category o ℓ e → Level
      levele {e = e} _ = e
  
  
    Hom[L-,-]′ : Bifunctor C.op D (Setoids _ _)
    Hom[L-,-]′ = LiftSetoids (levelℓ C) (levele C) ∘F Hom[ D ][-,-] ∘F (L.op ⁂ idF)
  
    Hom[-,R-]′ : Bifunctor C.op D (Setoids _ _)
    Hom[-,R-]′ = LiftSetoids (levelℓ D) (levele D) ∘F Hom[ C ][-,-] ∘F (idF ⁂ R)

    Hom-NI : NaturalIsomorphism Hom[L-,-]′ Hom[-,R-]′
    Hom-NI = record
      { F⇒G = record
        { η       = λ _ → record
          { _⟨$⟩_ = λ f → lift (Ladjunct (lower f))
          ; cong  = λ eq → lift (C.∘-resp-≈ˡ (R.F-resp-≈ (lower eq)))
          }
        ; commute = λ where
          {X , Y} {A , B} (f , g) {lift h} {lift i} (lift eq) →
            let open C
                open HomReasoning
                open MR C
            in lift $ begin
              R.F₁ (g D.∘ h D.∘ L.F₁ f) ∘ unit.η A         ≈⟨ R.homomorphism ⟩∘⟨refl ⟩
              (R.F₁ g ∘ R.F₁ (h D.∘ L.F₁ f)) ∘ unit.η A    ≈⟨ (refl⟩∘⟨ R.homomorphism) ⟩∘⟨refl ⟩
              (R.F₁ g ∘ R.F₁ h ∘ R.F₁ (L.F₁ f)) ∘ unit.η A ≈⟨ pullʳ assoc ⟩
              R.F₁ g ∘ R.F₁ h ∘ R.F₁ (L.F₁ f) ∘ unit.η A   ≈˘⟨ refl⟩∘⟨ ⟺ (R.F-resp-≈ eq) ⟩∘⟨ unit.commute f ⟩
              R.F₁ g ∘ R.F₁ i ∘ unit.η X ∘ f               ≈˘⟨ refl⟩∘⟨ assoc ⟩
              R.F₁ g ∘ (R.F₁ i ∘ unit.η X) ∘ f             ∎
        }
      ; F⇐G = record
        { η       = λ _ → record
          { _⟨$⟩_ = λ f → lift (Radjunct (lower f))
          ; cong  = λ eq → lift (D.∘-resp-≈ʳ (L.F-resp-≈ (lower eq)))
          }
        ; commute = λ where
          {X , Y} {A , B} (f , g) {lift h} {lift i} (lift eq) →
            let open D
                open HomReasoning
                open MR D
            in lift $ begin
              counit.η B ∘ L.F₁ (R.F₁ g C.∘ h C.∘ f)       ≈⟨ refl⟩∘⟨ L.homomorphism ⟩
              counit.η B ∘ L.F₁ (R.F₁ g) ∘ L.F₁ (h C.∘ f)  ≈⟨ pullˡ (counit.commute g) ⟩
              (g ∘ counit.η Y) ∘ L.F₁ (h C.∘ f)            ≈⟨ refl⟩∘⟨ L.homomorphism ⟩
              (g ∘ counit.η Y) ∘ L.F₁ h ∘ L.F₁ f           ≈⟨ refl ⟩∘⟨ L.F-resp-≈ eq ⟩∘⟨ refl ⟩
              (g ∘ counit.η Y) ∘ L.F₁ i ∘ L.F₁ f           ≈⟨ pullʳ (⟺ assoc) ⟩
              g ∘ (counit.η Y ∘ L.F₁ i) ∘ L.F₁ f           ∎
        }
      ; iso = λ X → record
        { isoˡ = λ eq → let open D.HomReasoning in lift (RLadjunct≈id ○ lower eq)
        ; isoʳ = λ eq → let open C.HomReasoning in lift (LRadjunct≈id ○ lower eq)
        }
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

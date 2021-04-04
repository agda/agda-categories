{-# OPTIONS --without-K --safe #-}
module Categories.Adjoint where

-- Adjoints

open import Level

open import Data.Product using (_,_; _×_)
open import Function using (_$_) renaming (_∘_ to _∙_)
open import Function.Equality using (Π; _⟶_)
import Function.Inverse as FI
open import Relation.Binary using (Rel; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

-- be explicit in imports to 'see' where the information comes from
open import Categories.Category.Core using (Category)
open import Categories.Category.Product using (Product; _⁂_)
open import Categories.Category.Instance.Setoids
open import Categories.Morphism
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.Functor.Hom using (Hom[_][-,-])
open import Categories.Functor.Construction.LiftSetoids
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper; _∘ₕ_; _∘ᵥ_; _∘ˡ_; _∘ʳ_)
  renaming (id to idN)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (NaturalIsomorphism; unitorˡ; unitorʳ; associator; _≃_)
import Categories.Morphism.Reasoning as MR

private
  variable
    o o′ o″ ℓ ℓ′ ℓ″ e e′ e″ : Level
    C D E : Category o ℓ e

record Adjoint (L : Functor C D) (R : Functor D C) : Set (levelOfTerm L ⊔ levelOfTerm R) where
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

  -- naturality condition on the two hom functors.
  -- these conditions are separated out because a complication due to the
  -- universe level in Agda.
  module _ where
    open C
    open HomReasoning
    open MR C

    Ladjunct-comm : ∀ {X Y A B} {h i : L.F₀ X D.⇒ Y} {f : A ⇒ X} {g : Y D.⇒ B} →
                      h D.≈ i →
                      R.F₁ (g D.∘ h D.∘ L.F₁ f) ∘ unit.η A ≈ R.F₁ g ∘ (R.F₁ i ∘ unit.η X) ∘ f
    Ladjunct-comm {X} {Y} {A} {B} {h} {i} {f} {g} eq = begin
      R.F₁ (g D.∘ h D.∘ L.F₁ f) ∘ unit.η A         ≈⟨ R.homomorphism ⟩∘⟨refl ⟩
      (R.F₁ g ∘ R.F₁ (h D.∘ L.F₁ f)) ∘ unit.η A    ≈⟨ (refl⟩∘⟨ R.homomorphism) ⟩∘⟨refl ⟩
      (R.F₁ g ∘ R.F₁ h ∘ R.F₁ (L.F₁ f)) ∘ unit.η A ≈⟨ pullʳ assoc ⟩
      R.F₁ g ∘ R.F₁ h ∘ R.F₁ (L.F₁ f) ∘ unit.η A   ≈˘⟨ refl⟩∘⟨ ⟺ (R.F-resp-≈ eq) ⟩∘⟨ unit.commute f ⟩
      R.F₁ g ∘ R.F₁ i ∘ unit.η X ∘ f               ≈⟨ refl⟩∘⟨ sym-assoc ⟩
      R.F₁ g ∘ (R.F₁ i ∘ unit.η X) ∘ f             ∎

    Ladjunct-comm′ : ∀ {X A B} {f : A ⇒ X} {g : L.F₀ X D.⇒ B} →
                      Ladjunct (g D.∘ L.F₁ f) ≈ Ladjunct g ∘ f
    Ladjunct-comm′ = ∘-resp-≈ˡ R.homomorphism ○ (pullʳ (⟺ (unit.commute _))) ○ sym-assoc

    Ladjunct-resp-≈ : ∀ {A B} {f g : L.F₀ A D.⇒ B} → f D.≈ g → Ladjunct f ≈ Ladjunct g
    Ladjunct-resp-≈ eq = ∘-resp-≈ˡ (R.F-resp-≈ eq)

  module _ where
    open D
    open HomReasoning
    open MR D

    Radjunct-comm : ∀ {X Y A B} {h i : X C.⇒ R.F₀ Y} {f : A C.⇒ X} {g : Y ⇒ B} →
                      h C.≈ i →
                      counit.η B ∘ L.F₁ (R.F₁ g C.∘ h C.∘ f) ≈ g ∘ (counit.η Y ∘ L.F₁ i) ∘ L.F₁ f
    Radjunct-comm {X} {Y} {A} {B} {h} {i} {f} {g} eq = begin
      counit.η B ∘ L.F₁ (R.F₁ g C.∘ h C.∘ f)       ≈⟨ refl⟩∘⟨ L.homomorphism ⟩
      counit.η B ∘ L.F₁ (R.F₁ g) ∘ L.F₁ (h C.∘ f)  ≈⟨ pullˡ (counit.commute g) ⟩
      (g ∘ counit.η Y) ∘ L.F₁ (h C.∘ f)            ≈⟨ refl⟩∘⟨ L.homomorphism ⟩
      (g ∘ counit.η Y) ∘ L.F₁ h ∘ L.F₁ f           ≈⟨ refl⟩∘⟨ L.F-resp-≈ eq ⟩∘⟨refl ⟩
      (g ∘ counit.η Y) ∘ L.F₁ i ∘ L.F₁ f           ≈⟨ pullʳ sym-assoc ⟩
      g ∘ (counit.η Y ∘ L.F₁ i) ∘ L.F₁ f           ∎

    Radjunct-comm′ : ∀ {Y A B} {f : A C.⇒ R.F₀ Y} {g : Y ⇒ B} →
                      Radjunct (R.F₁ g C.∘ f) ≈ g ∘ Radjunct f
    Radjunct-comm′ = ∘-resp-≈ʳ L.homomorphism ○ pullˡ (counit.commute _) ○ assoc

    Radjunct-resp-≈ : ∀ {A B} {f g : A C.⇒ R.F₀ B} → f C.≈ g → Radjunct f ≈ Radjunct g
    Radjunct-resp-≈ eq = ∘-resp-≈ʳ (L.F-resp-≈ eq)

  -- a complication: the two hom functors do not live in the same Setoids,
  -- so they need to be mapped to the same Setoids first before establishing
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
      { F⇒G = ntHelper record
        { η       = λ _ → record
          { _⟨$⟩_ = λ f → lift (Ladjunct (lower f))
          ; cong  = λ eq → lift (Ladjunct-resp-≈ (lower eq))
          }
        ; commute = λ _ eq → lift $ Ladjunct-comm (lower eq)
        }
      ; F⇐G = ntHelper record
        { η       = λ _ → record
          { _⟨$⟩_ = λ f → lift (Radjunct (lower f))
          ; cong  = λ eq → lift (Radjunct-resp-≈ (lower eq))
          }
        ; commute = λ _ eq → lift $ Radjunct-comm (lower eq)
        }
      ; iso = λ X → record
        { isoˡ = λ eq → let open D.HomReasoning in lift (RLadjunct≈id ○ lower eq)
        ; isoʳ = λ eq → let open C.HomReasoning in lift (LRadjunct≈id ○ lower eq)
        }
      }

  module Hom-NI = NaturalIsomorphism Hom-NI

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

private
  op-involutive : ∀ {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {L : Functor C D} {R : Functor D C} (L⊣R : L ⊣ R) →
                  Adjoint.op (Adjoint.op L⊣R) ≡ L⊣R
  op-involutive _ = ≡.refl

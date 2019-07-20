{-# OPTIONS --without-K --safe #-}
module Categories.Adjoint where

-- Adjoints

open import Level

open import Data.Product using (_,_; _×_)
open import Function using (_$_) renaming (_∘_ to _∙_)
open import Function.Equality using (Π; _⟶_)
import Function.Inverse as FI
open import Relation.Binary using (Rel; IsEquivalence; Setoid)

-- be explicit in imports to 'see' where the information comes from
open import Categories.Category using (Category)
open import Categories.Category.Product using (Product; _⁂_)
open import Categories.Category.Instance.Setoids
open import Categories.Morphism
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
    o o′ ℓ e : Level
    C D : Category o ℓ e

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
      R.F₁ g ∘ R.F₁ i ∘ unit.η X ∘ f               ≈˘⟨ refl⟩∘⟨ assoc ⟩
      R.F₁ g ∘ (R.F₁ i ∘ unit.η X) ∘ f             ∎

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
      (g ∘ counit.η Y) ∘ L.F₁ h ∘ L.F₁ f           ≈⟨ refl ⟩∘⟨ L.F-resp-≈ eq ⟩∘⟨ refl ⟩
      (g ∘ counit.η Y) ∘ L.F₁ i ∘ L.F₁ f           ≈⟨ pullʳ (⟺ assoc) ⟩
      g ∘ (counit.η Y ∘ L.F₁ i) ∘ L.F₁ f           ∎

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
      { F⇒G = record
        { η       = λ _ → record
          { _⟨$⟩_ = λ f → lift (Ladjunct (lower f))
          ; cong  = λ eq → lift (C.∘-resp-≈ˡ (R.F-resp-≈ (lower eq)))
          }
        ; commute = λ _ eq → lift $ Ladjunct-comm (lower eq)
        }
      ; F⇐G = record
        { η       = λ _ → record
          { _⟨$⟩_ = λ f → lift (Radjunct (lower f))
          ; cong  = λ eq → lift (D.∘-resp-≈ʳ (L.F-resp-≈ (lower eq)))
          }
        ; commute = λ _ eq → lift $ Radjunct-comm (lower eq)
        }
      ; iso = λ X → record
        { isoˡ = λ eq → let open D.HomReasoning in lift (RLadjunct≈id ○ lower eq)
        ; isoʳ = λ eq → let open C.HomReasoning in lift (LRadjunct≈id ○ lower eq)
        }
      }
  
infix 5 _⊣_
_⊣_ = Adjoint

-- a special case of the natural isomorphism in which homsets in C and D have the same
-- universe level. therefore there is no need to lift Setoids to the saem level.
-- this is helpful when combining with Yoneda lemma.
module _ {C : Category o ℓ e} {D : Category o′ ℓ e} {L : Functor C D} {R : Functor D C} where
  private
    module C = Category C
    module D = Category D
    module L = Functor L
    module R = Functor R

  module _ (adjoint : L ⊣ R) where       
    open Adjoint adjoint

    -- in this case, the hom functors are naturally isomorphism directly
    Hom-NI′ : NaturalIsomorphism Hom[L-,-] Hom[-,R-]
    Hom-NI′ = record
      { F⇒G = record
        { η       = λ _ → Hom-inverse.to
        ; commute = λ _ eq → Ladjunct-comm eq
        }
      ; F⇐G = record
        { η       = λ _ → Hom-inverse.from
        ; commute = λ _ eq → Radjunct-comm eq
        }
      ; iso = λ _ → record
        { isoˡ = λ eq → let open D.HomReasoning in RLadjunct≈id ○ eq
        ; isoʳ = λ eq → let open C.HomReasoning in LRadjunct≈id ○ eq
        }
      }

  -- now goes from natural isomorphism back to adjoint.
  -- for simplicity, just construct the case in which homsetoids of C and D
  -- are compatible.

  private
    Hom[L-,-] : Bifunctor C.op D (Setoids _ _)
    Hom[L-,-] = Hom[ D ][-,-] ∘F (L.op ⁂ idF)

    Hom[-,R-] : Bifunctor C.op D (Setoids _ _)
    Hom[-,R-] = Hom[ C ][-,-] ∘F (idF ⁂ R)

  module _ (Hni : NaturalIsomorphism Hom[L-,-] Hom[-,R-]) where
    open NaturalIsomorphism Hni
    open NaturalTransformation
    open Functor
    open Π

    private
      unitη : ∀ X → F₀ Hom[L-,-] (X , L.F₀ X) ⟶ F₀ Hom[-,R-] (X , L.F₀ X)
      unitη X = ⇒.η (X , L.F₀ X)

      unit : NaturalTransformation idF (R ∘F L)
      unit = record
        { η       = λ X → unitη X ⟨$⟩ D.id
        ; commute = λ {X} {Y} f → begin
          (unitη Y ⟨$⟩ D.id) ∘ f                             ≈⟨ introˡ R.identity ⟩
          R.F₁ D.id ∘ (unitη Y  ⟨$⟩ D.id) ∘ f                ≈˘⟨ ⇒.commute (f , D.id) D.Equiv.refl ⟩
          ⇒.η (X , L.F₀ Y) ⟨$⟩ (D.id D.∘ D.id D.∘ L.F₁ f)    ≈⟨ cong (⇒.η (X , L.F₀ Y)) (D.Equiv.trans D.identityˡ D.identityˡ) ⟩
          ⇒.η (X , L.F₀ Y) ⟨$⟩ L.F₁ f                        ≈⟨ cong (⇒.η (X , L.F₀ Y)) (MR.introʳ D (MR.elimʳ D L.identity)) ⟩
          ⇒.η (X , L.F₀ Y) ⟨$⟩ (L.F₁ f D.∘ D.id D.∘ L.F₁ id) ≈⟨ ⇒.commute (C.id , L.F₁ f) D.Equiv.refl ⟩
          R.F₁ (L.F₁ f) ∘ (unitη X ⟨$⟩ D.id) ∘ id            ≈⟨ refl⟩∘⟨ identityʳ ⟩
          R.F₁ (L.F₁ f) ∘ (unitη X ⟨$⟩ D.id)                 ∎
        }
        where open C
              open HomReasoning
              open MR C

      counitη : ∀ X → F₀ Hom[-,R-] (R.F₀ X , X) ⟶ F₀ Hom[L-,-] (R.F₀ X , X)
      counitη X = ⇐.η (R.F₀ X , X)

      counit : NaturalTransformation (L ∘F R) idF
      counit = record
        { η       = λ X → counitη X ⟨$⟩ C.id
        ; commute = λ {X} {Y} f → begin
          (counitη Y ⟨$⟩ C.id) ∘ L.F₁ (R.F₁ f)               ≈˘⟨ identityˡ ⟩
          id ∘ (counitη Y ⟨$⟩ C.id) ∘ L.F₁ (R.F₁ f)          ≈˘⟨ ⇐.commute (R.F₁ f , D.id) C.Equiv.refl ⟩
          ⇐.η (R.F₀ X , Y) ⟨$⟩ (R.F₁ id C.∘ C.id C.∘ R.F₁ f) ≈⟨ cong (⇐.η (R.F₀ X , Y)) (C.Equiv.trans (MR.elimˡ C R.identity) C.identityˡ) ⟩
          ⇐.η (R.F₀ X , Y) ⟨$⟩ R.F₁ f                        ≈⟨ cong (⇐.η (R.F₀ X , Y)) (MR.introʳ C C.identityˡ) ⟩
          ⇐.η (R.F₀ X , Y) ⟨$⟩ (R.F₁ f C.∘ C.id C.∘ C.id)    ≈⟨ ⇐.commute (C.id , f) C.Equiv.refl ⟩
          f ∘ (counitη X ⟨$⟩ C.id) ∘ L.F₁ C.id               ≈⟨ refl⟩∘⟨ elimʳ L.identity ⟩
          f ∘ (counitη X ⟨$⟩ C.id)                           ∎
        }
        where open D
              open HomReasoning
              open MR D
  
    Hom-NI⇒Adjoint : L ⊣ R
    Hom-NI⇒Adjoint = record
      { unit   = unit
      ; counit = counit
      ; zig    = λ {A} →
        let open D
            open HomReasoning
            open MR D
        in begin
          η counit (L.F₀ A) ∘ L.F₁ (η unit A)      ≈˘⟨ identityˡ ⟩
          id ∘ η counit (L.F₀ A) ∘ L.F₁ (η unit A) ≈˘⟨ ⇐.commute (η unit A , id) C.Equiv.refl ⟩
          ⇐.η (A , L.F₀ A) ⟨$⟩ (R.F₁ id C.∘ C.id C.∘ η unit A)
                                                   ≈⟨ cong (⇐.η (A , L.F₀ A)) (C.Equiv.trans (MR.elimˡ C R.identity) C.identityˡ) ⟩
          ⇐.η (A , L.F₀ A) ⟨$⟩ η unit A            ≈⟨ isoˡ refl ⟩
          id
                                                   ∎
      ; zag    = λ {B} →
        let open C
            open HomReasoning
            open MR C
        in begin
          R.F₁ (η counit B) ∘ η unit (R.F₀ B)      ≈˘⟨ refl⟩∘⟨ identityʳ ⟩
          R.F₁ (η counit B) ∘ η unit (R.F₀ B) ∘ id ≈˘⟨ ⇒.commute (id , η counit B) D.Equiv.refl ⟩
          ⇒.η (R.F₀ B , B) ⟨$⟩ (η counit B D.∘ D.id D.∘ L.F₁ id)
                                                   ≈⟨ cong (⇒.η (R.F₀ B , B)) (MR.elimʳ D (MR.elimʳ D L.identity)) ⟩
          ⇒.η (R.F₀ B , B) ⟨$⟩ η counit B          ≈⟨ isoʳ refl ⟩
          id                                       ∎
      }
      where module i {X} = Iso (iso X)
            open i
  
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

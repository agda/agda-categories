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
      (g ∘ counit.η Y) ∘ L.F₁ h ∘ L.F₁ f           ≈⟨ refl ⟩∘⟨ L.F-resp-≈ eq ⟩∘⟨ refl ⟩
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

-- a special case of the natural isomorphism in which homsets in C and D have the same
-- universe level. therefore there is no need to lift Setoids to the same level.
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
      { F⇒G = ntHelper record
        { η       = λ _ → Hom-inverse.to
        ; commute = λ _ eq → Ladjunct-comm eq
        }
      ; F⇐G = ntHelper record
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
      unit = ntHelper record
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
      counit = ntHelper record
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

-- the general case from isomorphic Hom setoids to adjoint functors
module _ {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {L : Functor C D} {R : Functor D C} where
  private
    module C = Category C
    module D = Category D
    module L = Functor L
    module R = Functor R
    open Functor
    open Π
    
    Hom[L-,-] : Bifunctor C.op D (Setoids _ _)
    Hom[L-,-] = LiftSetoids ℓ e ∘F Hom[ D ][-,-] ∘F (L.op ⁂ idF)

    Hom[-,R-] : Bifunctor C.op D (Setoids _ _)
    Hom[-,R-] = LiftSetoids ℓ′ e′ ∘F Hom[ C ][-,-] ∘F (idF ⁂ R)

  module _ (Hni : Hom[L-,-] ≃ Hom[-,R-]) where
    open NaturalIsomorphism Hni
    private
      unitη : ∀ X → F₀ Hom[L-,-] (X , L.F₀ X) ⟶ F₀ Hom[-,R-] (X , L.F₀ X)
      unitη X = ⇒.η (X , L.F₀ X)
  
      unit : NaturalTransformation idF (R ∘F L)
      unit = ntHelper record
        { η       = λ X → lower (unitη X ⟨$⟩ lift D.id)
        ; commute = λ {X Y} f → begin
          lower (unitη Y ⟨$⟩ lift D.id) ∘ f
            ≈⟨ introˡ R.identity ⟩
          R.F₁ D.id ∘ lower (unitη Y ⟨$⟩ lift D.id) ∘ f
            ≈˘⟨ lower (⇒.commute (f , D.id) (lift D.Equiv.refl)) ⟩
          lower (⇒.η (X , L.F₀ Y) ⟨$⟩ lift (D.id D.∘ D.id D.∘ L.F₁ f))
            ≈⟨ lower (cong (⇒.η (X , L.F₀ Y)) (lift (D.Equiv.trans D.identityˡ D.identityˡ))) ⟩
          lower (⇒.η (X , L.F₀ Y) ⟨$⟩ lift (L.F₁ f))
            ≈⟨ lower (cong (⇒.η (X , L.F₀ Y)) (lift (MR.introʳ D (MR.elimʳ D L.identity)))) ⟩
          lower (⇒.η (X , L.F₀ Y) ⟨$⟩ lift (L.F₁ f D.∘ D.id D.∘ L.F₁ id))
            ≈⟨ lower (⇒.commute (C.id , L.F₁ f) (lift D.Equiv.refl)) ⟩
          R.F₁ (L.F₁ f) ∘ lower (⇒.η (X , L.F₀ X) ⟨$⟩ lift D.id) ∘ id
            ≈⟨ refl⟩∘⟨ identityʳ ⟩
          F₁ (R ∘F L) f ∘ lower (unitη X ⟨$⟩ lift D.id)                ∎
        }
        where open C
              open HomReasoning
              open MR C
  

      counitη : ∀ X → F₀ Hom[-,R-] (R.F₀ X , X) ⟶ F₀ Hom[L-,-] (R.F₀ X , X)
      counitη X = ⇐.η (R.F₀ X , X)

      counit : NaturalTransformation (L ∘F R) idF
      counit = ntHelper record
        { η       = λ X → lower (counitη X ⟨$⟩ lift C.id)
        ; commute = λ {X} {Y} f → begin
          lower (⇐.η (R.F₀ Y , Y) ⟨$⟩ lift C.id) ∘ L.F₁ (R.F₁ f)
            ≈˘⟨ identityˡ ⟩
          id ∘ lower (⇐.η (R.F₀ Y , Y) ⟨$⟩ lift C.id) ∘ L.F₁ (R.F₁ f)
            ≈˘⟨ lower (⇐.commute (R.F₁ f , D.id) (lift C.Equiv.refl)) ⟩
          lower (⇐.η (R.F₀ X , Y) ⟨$⟩ lift (R.F₁ id C.∘ C.id C.∘ R.F₁ f))
            ≈⟨ lower (cong (⇐.η (R.F₀ X , Y)) (lift (C.Equiv.trans (MR.elimˡ C R.identity) C.identityˡ))) ⟩
          lower (⇐.η (R.F₀ X , Y) ⟨$⟩ lift (R.F₁ f))
            ≈⟨ lower (cong (⇐.η (R.F₀ X , Y)) (lift (MR.introʳ C C.identityˡ))) ⟩
          lower (⇐.η (R.F₀ X , Y) ⟨$⟩ lift (R.F₁ f C.∘ C.id C.∘ C.id))
            ≈⟨ lower (⇐.commute (C.id , f) (lift C.Equiv.refl)) ⟩
          f ∘ lower (⇐.η (R.F₀ X , X) ⟨$⟩ lift C.id) ∘ L.F₁ C.id
            ≈⟨ refl⟩∘⟨ elimʳ L.identity ⟩
          f ∘ lower (⇐.η (R.F₀ X , X) ⟨$⟩ lift C.id)
            ∎
        }
        where open D
              open HomReasoning
              open MR D

    Hom-NI′⇒Adjoint : L ⊣ R
    Hom-NI′⇒Adjoint = record
      { unit   = unit
      ; counit = counit
      ; zig    = λ {A} →
        let open D
            open HomReasoning
            open MR D
        in begin
          lower (counitη (L.F₀ A) ⟨$⟩ lift C.id) ∘ L.F₁ (η unit A)
            ≈˘⟨ identityˡ ⟩
          id ∘ lower (counitη (L.F₀ A) ⟨$⟩ lift C.id) ∘ L.F₁ (η unit A)
            ≈˘⟨ lower (⇐.commute (η unit A , id) (lift C.Equiv.refl)) ⟩
          lower (⇐.η (A , L.F₀ A) ⟨$⟩ lift (R.F₁ id C.∘ C.id C.∘ lower (⇒.η (A , L.F₀ A) ⟨$⟩ lift id)))
            ≈⟨ lower (cong (⇐.η (A , L.F₀ A)) (lift (C.Equiv.trans (MR.elimˡ C R.identity) C.identityˡ))) ⟩
          lower (⇐.η (A , L.F₀ A) ⟨$⟩ (⇒.η (A , L.F₀ A) ⟨$⟩ lift id))
            ≈⟨ lower (isoˡ (lift refl)) ⟩
          id ∎
      ; zag    = λ {B} →
        let open C
            open HomReasoning
            open MR C
        in begin
          R.F₁ (lower (⇐.η (R.F₀ B , B) ⟨$⟩ lift id)) ∘ lower (⇒.η (R.F₀ B , L.F₀ (R.F₀ B)) ⟨$⟩ lift D.id)
            ≈˘⟨ refl⟩∘⟨ identityʳ ⟩
          R.F₁ (lower (⇐.η (R.F₀ B , B) ⟨$⟩ lift id)) ∘ lower (⇒.η (R.F₀ B , L.F₀ (R.F₀ B)) ⟨$⟩ lift D.id) ∘ id
            ≈˘⟨ lower (⇒.commute (id , η counit B) (lift D.Equiv.refl)) ⟩
          lower (⇒.η (R.F₀ B , B) ⟨$⟩ lift (lower (⇐.η (R.F₀ B , B) ⟨$⟩ lift id) D.∘ D.id D.∘ L.F₁ id))
            ≈⟨ lower (cong (⇒.η (R.F₀ B , B)) (lift (MR.elimʳ D (MR.elimʳ D L.identity)))) ⟩
          lower (⇒.η (R.F₀ B , B) ⟨$⟩ lift (lower (⇐.η (R.F₀ B , B) ⟨$⟩ lift id)))
            ≈⟨ lower (isoʳ (lift refl)) ⟩
          id ∎
      }
      where open NaturalTransformation
            module _ {X} where
              open Iso (iso X) public

⊣-id : idF {C = C} ⊣ idF {C = C}
⊣-id {C = C} = record
  { unit   = F⇐G unitorˡ
  ; counit = F⇒G unitorʳ
  ; zig    = identityˡ
  ; zag    = identityʳ
  }
  where open Category C
        open NaturalIsomorphism

-- Adjoints compose; we can't be sloppy, so associators and unitors must be inserted.
-- Use single letters in pairs, so L & M on the left, and R & S on the right
_∘⊣_ : {L : Functor C D} {R : Functor D C} {M : Functor D E} {S : Functor E D} →
  L ⊣ R → M ⊣ S → (M ∘F L) ⊣ (R ∘F S)
_∘⊣_ {C = C} {D = D} {E = E} {L = L} {R} {M} {S} LR MS = record
  { unit =  ((F⇐G (associator _ S R) ∘ᵥ R ∘ˡ (F⇒G (associator L M S))) ∘ᵥ
            (R ∘ˡ (MSη′ ∘ʳ L)) ∘ᵥ (R ∘ˡ (F⇐G unitorˡ))) ∘ᵥ LRη′
  ; counit = MSε′ ∘ᵥ (((F⇒G (unitorʳ {F = M}) ∘ʳ S) ∘ᵥ ((M ∘ˡ LRε′) ∘ʳ S)) ∘ᵥ
             (F⇒G (associator R L M) ∘ʳ S) ) ∘ᵥ F⇐G (associator S R (M ∘F L) )
  ; zig = λ {A} → zig′ {A}
  ; zag = λ {B} → zag′ {B}
  }
  where
    open Functor
    open NaturalTransformation
    open NaturalIsomorphism
    module LR = Adjoint LR renaming (unit to LRη′; counit to LRε′)
    module MS = Adjoint MS renaming (unit to MSη′; counit to MSε′)
    module LRη = NaturalTransformation (Adjoint.unit LR) renaming (η to ηLR)
    module MSη = NaturalTransformation (Adjoint.unit MS) renaming (η to ηMS)
    module LRε = NaturalTransformation (Adjoint.counit LR) renaming (η to εLR)
    module MSε = NaturalTransformation (Adjoint.counit MS) renaming (η to εMS)
    module C = Category C
    module D = Category D
    module E = Category E
    module L = Functor L renaming (F₀ to L₀; F₁ to L₁)
    module M = Functor M renaming (F₀ to M₀; F₁ to M₁)
    module R = Functor R renaming (F₀ to R₀; F₁ to R₁)
    module S = Functor S renaming (F₀ to S₀; F₁ to S₁)
    open LR; open MS; open LRη; open LRε; open MSε; open MSη; open L; open M; open R; open S

    zig′ : {A : C.Obj} → (εMS (M₀ (L₀ A)) E.∘
       ((E.id E.∘ M₁ (εLR (S₀ (M₀ (L₀ A))))) E.∘ E.id) E.∘ E.id)
      E.∘ M₁ (L₁ (((C.id C.∘ R₁ D.id) C.∘ R₁ (ηMS (L₀ A)) C.∘ R₁ D.id) C.∘ ηLR A))
      E.≈ E.id
    -- use "inverted" format here, where rules are out-dented
    zig′ {A} = begin
        (εMS (M₀ (L₀ A)) E.∘ ((E.id E.∘ M₁ (εLR (S₀ (M₀ (L₀ A))))) E.∘ E.id) E.∘ E.id)
        E.∘ M₁ (L₁ (((C.id C.∘ R₁ D.id) C.∘ R₁ (ηMS (L₀ A)) C.∘ R₁ D.id) C.∘ ηLR A))
      ≈⟨  ( refl⟩∘⟨ (E.identityʳ ○ E.identityʳ ○ E.identityˡ)) ⟩∘⟨refl ⟩  -- get rid of those pesky E.id
        (εMS (M₀ (L₀ A)) E.∘ M₁ (εLR (S₀ (M₀ (L₀ A)))))
        E.∘ M₁ (L₁ (((C.id C.∘ R₁ D.id) C.∘ R₁ (ηMS (L₀ A)) C.∘ R₁ D.id) C.∘ ηLR A))
      ≈⟨ E.assoc ○ E.∘-resp-≈ʳ (⟺ M.homomorphism) ⟩
        εMS (M₀ (L₀ A)) E.∘
        M₁ (εLR (S₀ (M₀ (L₀ A))) D.∘ L₁ (((C.id C.∘ R₁ D.id) C.∘ R₁ (ηMS (L₀ A)) C.∘ R₁ D.id) C.∘ ηLR A))
         -- below: get rid of lots of pesky id. Nasty bit of nested equational reasoning, but nothing deep
      ≈⟨  refl⟩∘⟨ M.F-resp-≈ (D.∘-resp-≈ʳ (L.F-resp-≈
             (C.∘-resp-≈ˡ (C.∘-resp-≈ C.identityˡ (C.∘-resp-≈ʳ R.identity) C.HomReasoning.○
                let _⊚_ = C.HomReasoning._○_ in C.∘-resp-≈ R.identity C.identityʳ ⊚ C.identityˡ)))) ⟩
        εMS (M₀ (L₀ A)) E.∘ M₁ (εLR (S₀ (M₀ (L₀ A))) D.∘ L₁ ((R₁ (ηMS (L₀ A))) C.∘ ηLR A))
      ≈⟨  refl⟩∘⟨ M.F-resp-≈ (D.∘-resp-≈ʳ L.homomorphism) ⟩
        εMS (M₀ (L₀ A)) E.∘ M₁ (εLR (S₀ (M₀ (L₀ A))) D.∘ L₁ (R₁ (ηMS (L₀ A))) D.∘ L₁ (ηLR A))
      ≈⟨ refl⟩∘⟨ M.F-resp-≈ D.sym-assoc ⟩
        εMS (M₀ (L₀ A)) E.∘ M₁ ((εLR (S₀ (M₀ (L₀ A))) D.∘ L₁ (R₁ (ηMS (L₀ A)))) D.∘ L₁ (ηLR A))
      ≈⟨  refl⟩∘⟨ M.F-resp-≈ (D.∘-resp-≈ˡ (LRε.commute _)) ⟩
        εMS (M₀ (L₀ A)) E.∘ M₁ ( (_ D.∘ εLR _) D.∘ L₁ (ηLR A))
      ≈⟨  refl⟩∘⟨ M.homomorphism ⟩
        εMS (M₀ (L₀ A)) E.∘ M₁ (_ D.∘ εLR _) E.∘ M₁ (L₁ (ηLR A))
      ≈⟨  refl⟩∘⟨ ( M.homomorphism ⟩∘⟨refl ) ⟩
        εMS (M₀ (L₀ A)) E.∘ (M₁ (ηMS (L₀ A)) E.∘ M₁ (εLR _)) E.∘ M₁ (L₁ (ηLR A))
      ≈⟨ E.∘-resp-≈ʳ E.assoc ○ E.sym-assoc ⟩
        (εMS (M₀ (L₀ A)) E.∘ M₁ (ηMS (L₀ A))) E.∘ (M₁ (εLR _) E.∘ M₁ (L₁ (ηLR A)))
      ≈⟨ MS.zig ⟩∘⟨refl ⟩
        E.id E.∘ (M₁ (εLR _) E.∘ M₁ (L₁ (ηLR A)))
      ≈⟨ E.identityˡ ⟩
        M₁ (εLR _) E.∘ M₁ (L₁ (ηLR A))
      ≈˘⟨ M.homomorphism ⟩
        M₁ (εLR _ D.∘ L₁ (ηLR A))
      ≈⟨ M.F-resp-≈ LR.zig ○ M.identity ⟩
        E.id ∎
      where open E.HomReasoning

    zag′ : {B : E.Obj} → R₁ (S₁ (εMS B E.∘ ((E.id E.∘ M₁ (εLR (S₀ B))) E.∘ E.id) E.∘ E.id))
      C.∘ ((C.id C.∘ R₁ D.id) C.∘ R₁ (ηMS (L₀ (R₀ (S₀ B)))) C.∘ R₁ D.id) C.∘
      ηLR (R₀ (S₀ B)) C.≈ C.id
    zag′ {B} =
      let _⊚_ = E.HomReasoning._○_ in
      begin
         R₁ (S₁ (εMS B E.∘ ((E.id E.∘ M₁ (εLR (S₀ B))) E.∘ E.id) E.∘ E.id))
          C.∘ ((C.id C.∘ R₁ D.id) C.∘ R₁ (ηMS (L₀ (R₀ (S₀ B)))) C.∘ R₁ D.id) C.∘
          ηLR (R₀ (S₀ B)) -- get rid of all those id
      ≈⟨ R.F-resp-≈ (S.F-resp-≈ (E.∘-resp-≈ʳ (E.identityʳ ⊚ (E.identityʳ ⊚ E.identityˡ)))) ⟩∘⟨
         C.∘-resp-≈ˡ (C.∘-resp-≈ C.identityˡ (C.∘-resp-≈ʳ R.identity) ○
          C.∘-resp-≈ R.identity C.identityʳ ○ C.identityˡ) ⟩
         R₁ (S₁ (εMS B E.∘ M₁ (εLR (S₀ B)))) C.∘ R₁ (ηMS (L₀ (R₀ (S₀ B)))) C.∘ ηLR (R₀ (S₀ B))
      ≈⟨ C.sym-assoc ⟩
         (R₁ (S₁ (εMS B E.∘ M₁ (εLR (S₀ B)))) C.∘ R₁ (ηMS (L₀ (R₀ (S₀ B))))) C.∘ ηLR (R₀ (S₀ B))
      ≈˘⟨  R.homomorphism ⟩∘⟨refl ⟩
         R₁ (S₁ (εMS B E.∘ M₁ (εLR (S₀ B))) D.∘ ηMS (L₀ (R₀ (S₀ B)))) C.∘ ηLR (R₀ (S₀ B))
      ≈⟨ R.F-resp-≈ (D.∘-resp-≈ˡ S.homomorphism) ⟩∘⟨refl ⟩
        R₁ ((S₁ (εMS B) D.∘ (S₁ (M₁ (εLR (S₀ B))))) D.∘ ηMS (L₀ (R₀ (S₀ B)))) C.∘ ηLR (R₀ (S₀ B))
      ≈⟨ R.F-resp-≈ D.assoc ⟩∘⟨refl ⟩
        R₁ (S₁ (εMS B) D.∘ S₁ (M₁ (εLR (S₀ B))) D.∘ ηMS (L₀ (R₀ (S₀ B)))) C.∘ ηLR (R₀ (S₀ B))
      ≈⟨ R.F-resp-≈ (D.∘-resp-≈ʳ (D.HomReasoning.⟺ (MSη.commute (εLR (S₀ B))))) ⟩∘⟨refl ⟩
         R₁ (S₁ (εMS B) D.∘ ηMS (S₀ B) D.∘ εLR (S₀ B)) C.∘ ηLR (R₀ (S₀ B))
      ≈⟨ R.F-resp-≈ D.sym-assoc ⟩∘⟨refl ⟩
         R₁ ((S₁ (εMS B) D.∘ ηMS (S₀ B)) D.∘ εLR (S₀ B)) C.∘ ηLR (R₀ (S₀ B))
      ≈⟨ R.F-resp-≈ (D.∘-resp-≈ˡ MS.zag) ⟩∘⟨refl ⟩
         R₁ (D.id D.∘ εLR (S₀ B)) C.∘ ηLR (R₀ (S₀ B))
      ≈⟨ C.∘-resp-≈ˡ (R.F-resp-≈ D.identityˡ) ⟩
         R₁ (εLR (S₀ B)) C.∘ ηLR (R₀ (S₀ B))
      ≈⟨ LR.zag ⟩
         C.id ∎
      where open C.HomReasoning

{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Monoidal

module Categories.Category.Monoidal.Closed {o ℓ e} {C : Category o ℓ e} (M : Monoidal C) where

private
  module C = Category C
  open Category C

  variable
    X : Obj

open import Level
open import Function using (_$_) renaming (id to idFun)
open import Data.Product using (Σ; _,_)
open import Function.Equality as Π using (Π)

open import Categories.Adjoint
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Construction.Constant
open import Categories.Functor.Bifunctor
open import Categories.Functor.Hom
open import Categories.Category.Instance.Setoids
open import Categories.Morphism C
open import Categories.Morphism.Reasoning C
open import Categories.Morphism.Properties C
open import Categories.NaturalTransformation hiding (id)
open import Categories.NaturalTransformation.NaturalIsomorphism as NI hiding (_≅_)
open import Categories.NaturalTransformation.Dinatural using (extranaturalʳ)
open import Categories.NaturalTransformation.Properties
open import Categories.Yoneda
import Categories.Category.Closed as Cl

record Closed : Set (levelOfTerm M) where
  open Monoidal M public
  
  field
    [-,-]   : Bifunctor C.op C C 
    adjoint : (-⊗ X) ⊣ appˡ [-,-] X
    
  module adjoint {X} = Adjoint (adjoint {X})
  module [-,-] = Functor [-,-]

  Hom[-⊗_,-] : ∀ X → Bifunctor C.op C (Setoids ℓ e)
  Hom[-⊗ X ,-] = adjoint.Hom[L-,-] {X}

  Hom[-,[_,-]] : ∀ X → Bifunctor C.op C (Setoids ℓ e)
  Hom[-,[ X ,-]] = adjoint.Hom[-,R-] {X}

  Hom-NI : ∀ {X : Obj} → NaturalIsomorphism Hom[-⊗ X ,-] Hom[-,[ X ,-]]
  Hom-NI = Hom-NI′ adjoint

  -- TODO: show that closed monoidal category is closed.
  module _ where
    open HomReasoning
    open Hom C
    open Π.Π

    private
      [_,-] : Obj → Endofunctor C
      [_,-] = appˡ [-,-]

      nat′ : ∀ {X} → NaturalIsomorphism (Hom[-,[ unit ,-]] ∘F constʳ X) Hom[ C ][-, [-,-].F₀ (unit , X) ]
      nat′ = record
        { F⇒G = record
          { η       = λ _ → Π.id
          ; commute = λ f eq → ∘-resp-≈ˡ [-,-].identity ○ ∘-resp-≈ʳ (∘-resp-≈ˡ eq)
          }
        ; F⇐G = record
          { η       = λ _ → Π.id
          ; commute = λ f eq → ⟺ (∘-resp-≈ˡ [-,-].identity ○ ∘-resp-≈ʳ (∘-resp-≈ˡ (⟺ eq)))
          }
        ; iso = λ _ → record
          { isoˡ = idFun
          ; isoʳ = idFun
          }
        }

      nat : ∀ {X} → NaturalIsomorphism Hom[ C ][-, X ] (appʳ Hom[-⊗ unit ,-] X)
      nat = record
        { F⇒G = record
          { η       = λ _ → record
            { _⟨$⟩_ = λ f → f ∘ unitorʳ.from
            ; cong  = ∘-resp-≈ˡ
            }
          ; commute = λ {_ _} f {g h} eq → begin
            (id ∘ g ∘ f) ∘ unitorʳ.from       ≈⟨ identityˡ ⟩∘⟨refl ⟩
            (g ∘ f) ∘ unitorʳ.from            ≈˘⟨ pushʳ unitorʳ-commute-from ⟩
            g ∘ unitorʳ.from ∘ f ⊗₁ id        ≈⟨ pullˡ (∘-resp-≈ˡ eq) ⟩
            (h ∘ unitorʳ.from) ∘ f ⊗₁ id      ≈˘⟨ identityˡ ⟩
            id ∘ (h ∘ unitorʳ.from) ∘ f ⊗₁ id ∎
          }
        ; F⇐G = record
          { η       = λ _ → record
            { _⟨$⟩_ = λ f → f ∘ unitorʳ.to
            ; cong  = ∘-resp-≈ˡ
            }
          ; commute = λ {_ _} f {g h} eq → begin
            (id ∘ g ∘ f ⊗₁ id) ∘ unitorʳ.to   ≈⟨ identityˡ ⟩∘⟨refl ⟩
            (g ∘ f ⊗₁ id) ∘ unitorʳ.to        ≈˘⟨ pushʳ unitorʳ-commute-to ⟩
            g ∘ unitorʳ.to ∘ f                ≈⟨ pullˡ (∘-resp-≈ˡ eq) ⟩
            (h ∘ unitorʳ.to) ∘ f              ≈˘⟨ identityˡ ⟩
            id ∘ (h ∘ unitorʳ.to) ∘ f         ∎
          }
        ; iso = λ _ → record
          { isoˡ = cancelʳ unitorʳ.isoʳ ○_
          ; isoʳ = cancelʳ unitorʳ.isoˡ ○_
          }
        }

      identity-NI : NaturalIsomorphism idF [ unit ,-]
      identity-NI = record
        { F⇒G = F∘id⇒F ∘ᵥ ([ unit ,-] ∘ˡ unitorʳ-natural.F⇒G) ∘ᵥ adjoint.unit
        ; F⇐G = adjoint.counit ∘ᵥ (unitorʳ-natural.F⇐G ∘ʳ [ unit ,-]) ∘ᵥ F⇒id∘F
        ; iso = λ X → Iso-resp-≈ iso′.iso
                                 ((∘-resp-≈ˡ (F-resp-≈ [ unit ,-] identityˡ)) ○ ⟺ identityˡ)
                                 (∘-resp-≈ˡ (elimʳ (identity ⊗)) ○ ∘-resp-≈ʳ (⟺ identityʳ))
        }
        where iso′ : ∀ X → X ≅ [-,-].F₀ (unit , X)
              iso′ X = yoneda-iso C (nat′ ⓘᵥ (Hom-NI {X = unit} ⓘʳ constʳ X) ⓘᵥ nat)
              module iso′ {X} = _≅_ (iso′ X)
              open Functor

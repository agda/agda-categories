{-# OPTIONS --without-K --safe #-}
module Categories.Functor.Hom where

-- The Hom Functor from C.op × C to Setoids,
-- the two 1-argument version fixing one object
-- and some notation for the version where the category must be made explicit

open import Data.Product
open import Function using () renaming (_∘_ to _∙_)

open import Categories.Category
open import Categories.Functor hiding (id)
open import Categories.Functor.Properties
open import Categories.Functor.Bifunctor
open import Categories.Category.Instance.Setoids
import Categories.Morphism.Reasoning as MR

open import Relation.Binary using (Setoid)

module Hom {o ℓ e} (C : Category o ℓ e) where
  open Category C
  open MR C

  Hom[-,-] : Bifunctor (Category.op C) C (Setoids ℓ e)
  Hom[-,-] = record
    { F₀           = F₀′
    ; F₁           = λ where
      (f , g) → record
        { to = λ h → g ∘ h ∘ f
        ; cong = ∘-resp-≈ʳ ∙ ∘-resp-≈ˡ
        }
    ; identity     = identityˡ ○ identityʳ
    ; homomorphism = refl⟩∘⟨ sym-assoc ○ ⟺ assoc²''
    ; F-resp-≈     = λ { (f₁≈g₁ , f₂≈g₂) → f₂≈g₂ ⟩∘⟨ refl⟩∘⟨ f₁≈g₁}
    }
    where F₀′ : Obj × Obj → Setoid ℓ e
          F₀′ (A , B) = hom-setoid {A} {B}
          open HomReasoning

  Hom[_,-] : Obj → Functor C (Setoids ℓ e)
  Hom[_,-] = appˡ Hom[-,-]

  Hom[-,_] : Obj → Contravariant C (Setoids ℓ e)
  Hom[-,_] = appʳ Hom[-,-]

  Hom[_,_] : Obj → Obj → Setoid ℓ e
  Hom[ A , B ] = hom-setoid {A} {B}

-- Notation for when the ambient Category must be specified explicitly.
module _ {o ℓ e} (C : Category o ℓ e) where
  open Category C
  open Hom C

  Hom[_][-,-] : Bifunctor (Category.op C) C (Setoids ℓ e)
  Hom[_][-,-] = Hom[-,-]

  Hom[_][_,-] : Obj → Functor C (Setoids ℓ e)
  Hom[_][_,-] B = Hom[ B ,-]

  Hom[_][-,_] : Obj → Contravariant C (Setoids ℓ e)
  Hom[_][-,_] B = Hom[-, B ]

  Hom[_][_,_] : Obj → Obj → Setoid ℓ e
  Hom[_][_,_] A B = hom-setoid {A} {B}

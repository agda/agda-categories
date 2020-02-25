{-# OPTIONS --without-K --safe #-}
module Categories.Category.Construction.Coproduct where

-- Coproduct of categories.  Need to pull out some of the combinators.
-- Coproduct of Groupoid as well.

open import Level
open import Data.Sum
open import Data.Empty
open import Relation.Binary using (Rel)
open import Function using (_$_)

open import Categories.Category
open import Categories.Category.Groupoid using (IsGroupoid)
import Categories.Morphism as Morphism

private
  variable
    o ℓ e o′ ℓ′ e′ : Level

private
  _⊞_ : {a b c d r s : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
         (R : A → B → Set r) (S : C → D → Set s) →
         (A ⊎ C) → (B ⊎ D) → Set (r ⊔ s)
  _⊞_ {r = r} {s = s} R S =
           λ { (inj₁ x) (inj₁ x₁) → Lift (r ⊔ s) (R x x₁)
             ; (inj₁ x) (inj₂ y) → Lift (r ⊔ s) ⊥
             ; (inj₂ y₁) (inj₁ x) → Lift (r ⊔ s) ⊥
             ; (inj₂ y₁) (inj₂ y) → Lift (r ⊔ s) (S y₁ y)
             }

  _⊞Rel_ : {a b c d r s u v : Level} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
         {R : A → B → Set r} {S : C → D → Set s}  →
         ({a₁ : A} {b₁ : B} → Rel (R a₁ b₁) u) → ({c₁ : C} {d₁ : D} → Rel (S c₁ d₁) v) →
         ({x : A ⊎ C} {y : B ⊎ D} → Rel (_⊞_ R S x y) (u ⊔ v))
  _⊞Rel_ {u = u} {v = v} R₁ R₂ {inj₁ x} {inj₁ x₁} p q = Lift (u ⊔ v) (R₁ (lower p) (lower q))
  (R₁ ⊞Rel R₂) {inj₁ x} {inj₂ y} () ()
  (R₁ ⊞Rel R₂) {inj₂ y₁} {inj₁ x} () ()
  _⊞Rel_ {u = u} {v = v} R₁ R₂ {inj₂ y₁} {inj₂ y} p q = Lift (u ⊔ v) (R₂ (lower p) (lower q))

Coproduct : (C : Category o ℓ e) (D : Category o′ ℓ′ e′) → Category (o ⊔ o′) (ℓ ⊔ ℓ′) (e ⊔ e′)
Coproduct C D = record
  { Obj = C.Obj ⊎ D.Obj
  ; _⇒_ = C._⇒_ ⊞ D._⇒_
  ; _≈_ = C._≈_ ⊞Rel D._≈_
  ; id = λ { {inj₁ _} → lift C.id ; {inj₂ _} → lift D.id }
  ; _∘_ = λ { {inj₁ x} {inj₁ x₁} {inj₁ x₂} → λ { (lift p) (lift q) → lift (p C.∘ q) }
            ; {inj₁ x} {inj₁ x₁} {inj₂ y} → λ ()
            ; {inj₁ x} {inj₂ y} {inj₁ x₁} → λ ()
            ; {inj₁ x} {inj₂ y} {inj₂ y₁} → λ _ ()
            ; {inj₂ y} {inj₁ x} {inj₁ x₁} → λ _ ()
            ; {inj₂ y} {inj₁ x} {inj₂ y₁} → λ ()
            ; {inj₂ y} {inj₂ y₁} {inj₁ x} → λ ()
            ; {inj₂ y} {inj₂ y₁} {inj₂ y₂} → λ { (lift p) (lift q) → lift (p D.∘ q) }
            }
  ; assoc = λ { {inj₁ x} {inj₁ x₁} {inj₁ x₂} {inj₁ x₃} → lift C.assoc
              ; {inj₂ y} {inj₂ y₁} {inj₂ y₂} {inj₂ y₃} → lift D.assoc}
  ; sym-assoc = λ { {inj₁ x} {inj₁ x₁} {inj₁ x₂} {inj₁ x₃} → lift C.sym-assoc
                  ; {inj₂ y} {inj₂ y₁} {inj₂ y₂} {inj₂ y₃} → lift D.sym-assoc}
  ; identityˡ = λ { {inj₁ x} {inj₁ x₁} → lift C.identityˡ
                  ; {inj₂ y} {inj₂ y₁} → lift D.identityˡ }
  ; identityʳ = λ { {inj₁ x} {inj₁ x₁} → lift C.identityʳ
                  ; {inj₂ y} {inj₂ y₁} → lift D.identityʳ}
  ; identity² = λ { {inj₁ x} → lift C.identity²
                  ; {inj₂ y} → lift D.identity² }
  ; equiv = λ { {inj₁ x} {inj₁ x₁} → record
                { refl = lift C.Equiv.refl
                ; sym = λ { (lift p) → lift $ C.Equiv.sym p }
                ; trans = λ { (lift p) (lift q) → lift $ C.Equiv.trans p q } }
              ; {inj₁ x} {inj₂ y} → record { refl = λ { {()} } ; sym = λ { {()} } ; trans = λ { {()} } }
              ; {inj₂ y} {inj₁ x} → record { refl = λ { {()} } ; sym = λ { {()} } ; trans = λ { {()} } }
              ; {inj₂ y} {inj₂ y₁} → record
                { refl = lift D.Equiv.refl
                ; sym = λ { (lift p) → lift $ D.Equiv.sym p }
                ; trans = λ { (lift p) (lift q) → lift $ D.Equiv.trans p q } }
              }
  ; ∘-resp-≈ = λ { {inj₁ x} {inj₁ x₁} {inj₁ x₂} → λ { (lift f≈h) (lift g≈i) → lift $ C.∘-resp-≈ f≈h g≈i }
                 ; {inj₂ y} {inj₂ y₁} {inj₂ y₂} → λ { (lift f≈h) (lift g≈i) → lift $ D.∘-resp-≈ f≈h g≈i } }
  }
  where
  module C = Category C
  module D = Category D

IsGroupoid-⊎ : {C : Category o ℓ e} {D : Category o′ ℓ′ e′} → IsGroupoid C → IsGroupoid D → IsGroupoid (Coproduct C D)
IsGroupoid-⊎ G₁ G₂ = record
  { _⁻¹ = λ { {inj₁ x} {inj₁ x₁} (lift f) → lift $ IsGroupoid._⁻¹ G₁ f
            ; {inj₂ y} {inj₂ y₁} (lift f) → lift $ IsGroupoid._⁻¹ G₂ f
            }
  ; iso = λ { {inj₁ x} {inj₁ x₁} {lift f} → record
              { isoˡ = lift $ Iso.isoˡ i₁
              ; isoʳ = lift $ Iso.isoʳ i₁
              }
            ; {inj₂ y} {inj₂ y₁} {lift f} → record
              { isoˡ = lift $ Iso.isoˡ i₂
              ; isoʳ = lift $ Iso.isoʳ i₂
              }
            }
  }
  where
  open Morphism
  i₁ = IsGroupoid.iso G₁
  i₂ = IsGroupoid.iso G₂

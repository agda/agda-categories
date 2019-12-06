{-# OPTIONS --without-K --safe #-}

module Categories.Diagram.Limit.Ran where

open import Level
open import Data.Product using (Σ)

open import Categories.Category
open import Categories.Category.Complete
open import Categories.Category.Construction.Cones
open import Categories.Category.Construction.Comma
open import Categories.Category.Construction.Properties.Comma
open import Categories.Diagram.Cone.Properties
open import Categories.Diagram.Limit.Properties
open import Categories.Functor
open import Categories.Functor.Properties
open import Categories.Functor.Construction.Constant
open import Categories.NaturalTransformation
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism; _≃_; module ≃; _ⓘˡ_)
open import Categories.Kan
open import Categories.Diagram.Limit

import Categories.Morphism as M
import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e : Level
    C D E : Category o ℓ e

-- construct a Ran from a limit
module _ {o ℓ e o′ ℓ′ e′} {C : Category o′ ℓ′ e′} {D : Category o ℓ e}
         (F : Functor C D) (X : Functor C E) (Com : Complete (o′ ⊔ ℓ) (ℓ′ ⊔ e) e′ E) where
  private
    module C = Category C
    module D = Category D
    module E = Category E
    module F = Functor F
    module X = Functor X
    open Limit
    open Cone
    open Cone⇒ renaming (commute to ⇒-commute)
    open M E

    G   : (d : D.Obj) → Functor (d ↙ F) E
    G d   = X ∘F Cod (const! d) F
    ⊤Gd : ∀ d → Limit (G d)
    ⊤Gd d = Com (G d)
    module ⊤Gd d = Limit (⊤Gd d)
    f↙F : ∀ {Y Z} (f : Y D.⇒ Z) → Functor (Z ↙ F) (Y ↙ F)
    f↙F   = along-natˡ′ F

    Gf≃ : ∀ {Y Z} (f : Y D.⇒ Z) → G Z ≃ G Y ∘F f↙F f
    Gf≃ f = record
      { F⇒G = ntHelper record
        { η       = λ _ → X.F₁ C.id
        ; commute = λ _ → [ X ]-resp-square id-comm-sym
        }
      ; F⇐G = ntHelper record
        { η       = λ _ → X.F₁ C.id
        ; commute = λ _ → [ X ]-resp-square id-comm-sym
        }
      ; iso = λ _ → record
        { isoˡ = [ X ]-resp-∘ C.identity² ○ X.identity
        ; isoʳ = [ X ]-resp-∘ C.identity² ○ X.identity
        }
      }
      where open MR C
            open E.HomReasoning

    limY⇒limZ∘ : ∀ {Y Z} (f : Y D.⇒ Z) → Cones (G Y ∘F f↙F f) [ F-map-Coneʳ (f↙F f) (limit (Com (G Y))) , limit (Com (G Y ∘F f↙F f)) ]
    limY⇒limZ∘ {Y} f     = F⇒arr Com (f↙F f) (G Y)
    limZ∘≅limZ : ∀ {Y Z} (f : Y D.⇒ Z) → apex (⊤Gd Z) ≅ apex (Com (G Y ∘F f↙F f))
    limZ∘≅limZ {Y} {Z} f = ≃⇒lim≅ (Gf≃ f) (⊤Gd Z) (Com _)

  -- limit-is-ran : Ran F X
  -- limit-is-ran = record
  --   { R        = R
  --   ; ε        = {!!}
  --   ; δ        = {!!}
  --   ; δ-unique = {!!}
  --   ; commutes = {!!}
  --   }
  --   where open MR E
  --         open E.HomReasoning

  --         R₀ : D.Obj → E.Obj
  --         R₀ d = apex (⊤Gd d)
  --         R₁ : ∀ {A B} → D [ A , B ] → E [ R₀ A , R₀ B ]
  --         R₁ {A} f = _≅_.to (limZ∘≅limZ f) E.∘ arr (limY⇒limZ∘ f)

  --         R : Functor D E
  --         R = record
  --           { F₀           = R₀
  --           ; F₁           = R₁
  --           ; identity     = λ {d} → terminal.⊤-id (⊤Gd d) record
  --             { commute = λ {Z} → begin
  --               ⊤Gd.proj d Z ∘ R₁ D.id                                               ≈⟨ pullˡ (⇒-commute (≃⇒Cone⇒ (≃.sym (Gf≃ D.id)) (Com _) (⊤Gd d))) ⟩
  --               (X.F₁ C.id ∘ proj (Com _) Z) ∘ arr (limY⇒limZ∘ D.id)                 ≈⟨ pullʳ (⇒-commute (limY⇒limZ∘ D.id)) ⟩
  --               X.F₁ C.id ∘ ⊤Gd.proj d record { f = D.id D.∘ CommaObj.f Z D.∘ D.id } ≈⟨ refl⟩∘⟨ {!⊤Gd.proj d!} ⟩
  --               X.F₁ C.id ∘ ⊤Gd.proj d Z                                             ≈⟨ elimˡ X.identity ⟩
  --               ⊤Gd.proj d Z                                                         ∎
  --             }
  --           ; homomorphism = {!!}
  --           ; F-resp-≈     = {!!}
  --           }
  --           where open E

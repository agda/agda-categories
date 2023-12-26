{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Functor.Hom.Properties.Covariant {o ℓ e} (C : Category o ℓ e) where

open import Level using (Level)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary using (Setoid)

open import Categories.Category.Construction.Cones using (Cone; Cone⇒; Cones)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Diagram.Cone.Properties using (F-map-Coneˡ)
open import Categories.Diagram.Limit using (Limit; ψ-≈⇒rep-≈)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Limits using (Continuous)
open import Categories.Functor.Hom using (module Hom)

import Categories.Morphism.Reasoning as MR
open Func

private
  variable
    o′ ℓ′ e′ : Level
    J : Category o′ ℓ′ e′
  module C = Category C

open Category C
open Hom C

-- Hom functor preserves limits in C
module _ (W : Obj) {F : Functor J C} (lim : Limit F) where
  private
    module F   = Functor F
    module lim = Limit lim
    open lim
    HomF : Functor J (Setoids ℓ e)
    HomF = Hom[ W ,-] ∘F F
    open HomReasoning
    open MR C

    ⊤ : Cone HomF
    ⊤ = F-map-Coneˡ Hom[ W ,-] limit

    module _ (K : Cone HomF) where
      private
        module K = Cone _ K

      KW : Setoid.Carrier (Cone.N K) → Cone F
      KW x = record
        { N    = W
        ; apex = record
          { ψ       = λ X → K.ψ X ⟨$⟩ x
          ; commute = λ f → ⟺ (∘-resp-≈ʳ identityʳ) ○ K.commute f (Setoid.refl K.N)
          }
        }

      ! : Cones HomF [ K , ⊤ ]
      ! = record
        { arr     = record
          { to = λ x → rep (KW x)
          ; cong  = λ {x y} eq → ψ-≈⇒rep-≈ F W (Cone.apex (KW x)) (Cone.apex (KW y)) lim
                                              (λ A → Func.cong (K.ψ A) eq)
          }
        ; commute = λ {X} {x y} eq → begin
          proj X ∘ rep (KW x) ∘ C.id ≈⟨ refl⟩∘⟨ C.identityʳ ⟩
          proj X ∘ rep (KW x)        ≈⟨ lim.commute ⟩
          K.ψ X ⟨$⟩ x                ≈⟨ Func.cong (K.ψ X) eq ⟩
          K.ψ X ⟨$⟩ y                ∎
        }

    !-unique : ∀ {K : Cone HomF} (f : Cones HomF [ K , ⊤ ]) → Cones HomF [ ! K ≈ f ]
    !-unique {K} f {x} {y} x≈y = begin
      rep (KW K x) ≈⟨ terminal.!-unique f′ ⟩
      f.arr ⟨$⟩ x  ≈⟨ Func.cong f.arr x≈y ⟩
      f.arr ⟨$⟩ y  ∎
      where module K = Cone _ K
            module f = Cone⇒ _ f

            f′ : Cones F [ KW K x , limit ]
            f′ = record
              { arr     = f.arr ⟨$⟩ x
              ; commute = ⟺ (∘-resp-≈ʳ C.identityʳ) ○ f.commute (Setoid.refl K.N)
              }

  hom-resp-limit : Limit HomF
  hom-resp-limit = record
    { terminal = record
      { ⊤             = ⊤
      ; ⊤-is-terminal = record
        { !        = ! _
        ; !-unique = !-unique
        }
      }
    }

Hom-Continuous : ∀ X o′ ℓ′ e′ → Continuous o′ ℓ′ e′ Hom[ X ,-]
Hom-Continuous X _ _ _ L = terminal.⊤-is-terminal
  where open Limit (hom-resp-limit X L)

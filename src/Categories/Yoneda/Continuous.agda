{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Yoneda.Continuous {o ℓ e} (C : Category o ℓ e) where

open import Function.Equality using (Π)
open import Relation.Binary using (Setoid)

open import Categories.Category.Construction.Cones
open import Categories.Category.Construction.Presheaves
open import Categories.Diagram.Cone.Properties
open import Categories.Diagram.Limit
open import Categories.Functor
open import Categories.Functor.Limits
open import Categories.Functor.Hom
open import Categories.Functor.Hom.Properties C
open import Categories.NaturalTransformation
open import Categories.Yoneda

import Categories.Morphism.Reasoning as MR

open Hom C
open Yoneda C
open Π using (_⟨$⟩_)

private
  module C = Category C

module _ {o′ ℓ′ e′} {J : Category o′ ℓ′ e′} {F : Functor J C} (L : Limit F) where
  private
    module J = Category J
    module F = Functor F
    module L = Limit L
    open C.HomReasoning
    open MR C

    yF = embed ∘F F

    ⊤ : Cone yF
    ⊤ = F-map-Coneˡ embed L.limit

    HomL : ∀ X → Limit (Hom[ X ,-] ∘F F)
    HomL X = hom-resp-limit X L
    module HomL X = Limit (HomL X)

    module _ {K : Cone yF} where
      private
        module K where
          open Cone _ K public
          module N   = Functor N
          module ψ j = NaturalTransformation (ψ j)

      KHF : ∀ X → Cone (Hom[ X ,-] ∘F F)
      KHF X = record
        { N    = K.N.₀ X
        ; apex = record
          { ψ       = λ j → K.ψ.η j X
          ; commute = λ f eq → C.∘-resp-≈ʳ C.identityʳ ○ K.commute f eq
          }
        }

      ! : Cones yF [ K , ⊤ ]
      ! = record
        { arr     = ntHelper record
          { η       = λ X → Cone⇒.arr (HomL.terminal.! X {KHF X})
          ; commute = λ {X Y} f {x y} eq → L.terminal.!-unique record
            { arr     = C.id C.∘ L.rep _ C.∘ f
            ; commute = λ {j} → begin
              L.proj j C.∘ C.id C.∘ L.rep _ C.∘ f ≈⟨ refl⟩∘⟨ C.identityˡ ⟩
              L.proj j C.∘ L.rep _ C.∘ f          ≈⟨ pullˡ L.commute ⟩
              (K.ψ.η j X ⟨$⟩ y) C.∘ f             ≈˘⟨ C.identityˡ ⟩
              C.id C.∘ (K.ψ.η j X ⟨$⟩ y) C.∘ f    ≈˘⟨ K.ψ.commute j f eq ⟩
              K.ψ.η j Y ⟨$⟩ (K.N.₁ f ⟨$⟩ x)       ∎
            }
          }
        ; commute = λ eq → L.commute ○ Π.cong (K.ψ.η _ _) eq
        }

      module _ (f : Cones yF [ K , ⊤ ]) where
        private
          module f where
            open Cone⇒ _ f public
            module arr = NaturalTransformation arr

        !-unique : Cones yF [ ! ≈ f ]
        !-unique {X} {x} {y} eq = L.terminal.!-unique record
          { arr     = f.arr.η X ⟨$⟩ y
          ; commute = f.commute (Setoid.sym (K.N.₀ X) eq)
          }

  embed-resp-limit : Limit yF
  embed-resp-limit = record
    { terminal = record
      { ⊤             = ⊤
      ; ⊤-is-terminal = record
        { !        = !
        ; !-unique = !-unique
        }
      }
    }

embed-Continous : ∀ o′ ℓ′ e′ → Continuous o′ ℓ′ e′ embed
embed-Continous _ _ _ L = terminal.⊤-is-terminal
  where open Limit (embed-resp-limit L)

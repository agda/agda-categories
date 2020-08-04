{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Yoneda.Continuous {o ℓ e} (C : Category o ℓ e) where

open import Function.Equality using (Π)

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
          ; commute = λ f → {!Cone⇒.commute (HomL.terminal.! X {KHF X})!}
          }
        ; commute = λ eq → L.commute ○ Π.cong (K.ψ.η _ _) eq
        }

  embed-resp-limit : Limit yF
  embed-resp-limit = record
    { terminal = record
      { ⊤             = ⊤
      ; ⊤-is-terminal = record
        { !        = !
        ; !-unique = {!!}
        }
      }
    }

embed-Continous : ∀ o′ ℓ′ e′ → Continuous o′ ℓ′ e′ embed
embed-Continous _ _ _ L = terminal.⊤-is-terminal
  where open Limit (embed-resp-limit L)

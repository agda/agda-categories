{-# OPTIONS --without-K --safe #-}

open import Level
open import Categories.Category using () renaming (Category to Setoid-Category)
open import Categories.Category.Monoidal using (Monoidal)

module Categories.Bicategory.Instance.EnrichedCats
  {o ℓ e} {V : Setoid-Category o ℓ e} (M : Monoidal V) (v : Level) where

-- The 2-category of V-enriched categories

open import Data.Product as Prod using (_,_)

open import Categories.Bicategory using (Bicategory)
open import Categories.Category.Construction.EnrichedFunctors M
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Enriched.Category M
open import Categories.Enriched.Functor M renaming (id to idF)
open import Categories.Enriched.NaturalTransformation M hiding (id)
import Categories.Enriched.NaturalTransformation.NaturalIsomorphism M as NI
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.Functor.Construction.Constant using (const)
open import Categories.NaturalTransformation using (ntHelper)

open module V = Setoid-Category V using (_∘_)
open Monoidal M
open NaturalTransformation
open NI.NaturalIsomorphism

EnrichedCats : Bicategory (ℓ ⊔ e ⊔ v) (ℓ ⊔ e ⊔ v) (e ⊔ v) (o ⊔ ℓ ⊔ e ⊔ suc v)
EnrichedCats = record
  { enriched = record
    { Obj = Category v
    ; hom = EnrichedFunctors
    ; id  = const idF
    ; ⊚   = ⊚
    ; ⊚-assoc = λ {_ _ C D} →
      let module C  = Category C
          module D  = Category D
          module UC = Underlying C
          module UD = Underlying D
          open UD using () renaming (_∘_ to _∙_)
      in record
        { F⇒G = ntHelper record
          { η       = λ { ((F , G) , H) → from (NI.associator {F = F} {G} {H}) }
          ; commute = λ { {(_ , G₁) , H₁} {(F₂ , G₂) , _} ((α , β) , γ) {X} →
            let module G₁ = Functor G₁
                module H₁ = Functor H₁
                module F₂ = Functor F₂
                module G₂ = Functor G₂
                module UF₂ = UnderlyingFunctor F₂
            in begin
              D.id ∙ ((F₂.₁ ∘ G₂.₁) ∘ γ [ X ]) ∙ (F₂.₁ ∘ β [ H₁.₀ X ]) ∙
              α [ G₁.₀ (H₁.₀ X) ]
            ≈⟨ UD.identityˡ ○ ⟺ UD.assoc ⟩
              (((F₂.₁ ∘ G₂.₁) ∘ γ [ X ]) ∙ (F₂.₁ ∘ β [ H₁.₀ X ])) ∙
              α [ G₁.₀ (H₁.₀ X) ]
            ≈⟨ UD.∘-resp-≈ˡ (UD.∘-resp-≈ˡ V.assoc ○ ⟺ UF₂.homomorphism) ⟩
              (F₂.₁ ∘ ((G₂.₁ ∘ γ [ X ]) UC.∘ β [ H₁.₀ X ])) ∙ α [ G₁.₀ (H₁.₀ X) ]
            ≈˘⟨ UD.identityʳ ⟩
              ((F₂.₁ ∘ ((G₂.₁ ∘ γ [ X ]) UC.∘ β [ H₁.₀ X ])) ∙
                α [ G₁.₀ (H₁.₀ X) ]) ∙ D.id
            ∎ }
          }
        ; F⇐G = ntHelper record
          { η       = λ { ((F , G) , H) → to (NI.associator {F = F} {G} {H}) }
          ; commute = λ { {_} {(F₂ , _) , _} _ →
            -- the proof is analogous to the one above, so write it
            -- combinator-style
            let module UF₂ = UnderlyingFunctor F₂
            in UD.identityˡ ○
               UD.∘-resp-≈ˡ (UF₂.homomorphism ○ UD.∘-resp-≈ˡ (⟺ V.assoc)) ○
               UD.assoc ○ ⟺ UD.identityʳ
            }
          }
        ; iso = λ{ ((F , G) , H) → iso (NI.associator {F = F} {G} {H}) }
        }
    ; unitˡ = λ {_ B} →
      let module UB = Underlying B
      in record
        { F⇒G = ntHelper record
          { η       = λ _ → from NI.unitorˡ
          ; commute = λ _ → UB.identityˡ ○ UB.∘-resp-≈ˡ V.identityˡ
          }
        ; F⇐G = ntHelper record
          { η       = λ _ → to NI.unitorˡ
          ; commute = λ _ →
            UB.identityˡ ○ ⟺ (UB.identityʳ ○ UB.identityʳ ○ V.identityˡ)
          }
        ; iso = λ _ → iso NI.unitorˡ
        }
    ; unitʳ = λ {_ B} →
      let module UB = Underlying B
      in record
        { F⇒G = ntHelper record
          { η       = λ _ → from NI.unitorʳ
          ; commute = λ{ {_} {G₂ , _} _ →
            let module UG₂ = UnderlyingFunctor G₂
            in UB.identityˡ ○ UB.∘-resp-≈ˡ UG₂.identity ○
               UB.identityˡ ○ ⟺ UB.identityʳ
            }
          }
        ; F⇐G = ntHelper record
          { η       = λ _ → to NI.unitorʳ
          ; commute = λ{ {_} {G₂ , _} _ →
            let module UG₂ = UnderlyingFunctor G₂
            in UB.identityˡ ○
               ⟺ (UB.identityʳ ○ UB.∘-resp-≈ˡ UG₂.identity ○ UB.identityˡ)
            }
          }
        ; iso = λ _ → iso NI.unitorʳ
        }
    }
  ; triangle = λ {_ _ C} → Underlying.identityʳ C
  ; pentagon = λ {_ B _ D E _ G H I} →
    let module B  = Category B
        module D  = Category D
        module E  = Category E
        module G  = Functor G
        module H  = Functor H
        module I  = Functor I
        module UE = Underlying E
        open UE using () renaming (_∘_ to _∙_)
    in begin
      ((I.₁ ∘ D.id) ∙ E.id) ∙ E.id ∙ ((I.₁ ∘ H.₁ ∘ G.₁) ∘ B.id) ∙ E.id
    ≈⟨ UE.∘-resp-≈ UE.identityʳ (UE.identityˡ ○ UE.identityʳ) ⟩
      (I.₁ ∘ D.id) ∙ ((I.₁ ∘ H.₁ ∘ G.₁) ∘ B.id)
    ≈⟨ UE.∘-resp-≈ I.identity (Functor.identity (I ∘F H ∘F G)) ⟩
      E.id ∙ E.id
    ∎
  }

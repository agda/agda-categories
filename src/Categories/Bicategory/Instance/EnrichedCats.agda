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
open import Categories.Enriched.Category M
open import Categories.Enriched.Functor M renaming (id to idF)
open import Categories.Enriched.NaturalTransformation M hiding (id)
import Categories.Enriched.NaturalTransformation.NaturalIsomorphism M as NI
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.Functor.Construction.Constant using (const)
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)

private
  module V = Setoid-Category V
  module UnderlyingReasoning {c} (C : Category c) where
    open Underlying C public hiding (id)
    open HomReasoning public
  open NaturalTransformation
  open NI.NaturalIsomorphism

  -- Aliases used to shorten some proof expressions

  module UF = UnderlyingFunctor
  infixr 14 _$₀_ _$₁_
  _$₀_ = UF.F₀
  _$₁_ = UF.F₁

-- The bicategory of V-enriched categories, functors and natural
-- transformations.
--
-- Note that all the equational reasoning happens in the underlying
-- (ordinary) categories!

EnrichedCats : Bicategory (ℓ ⊔ e ⊔ v) (ℓ ⊔ e ⊔ v) (e ⊔ v) (o ⊔ ℓ ⊔ e ⊔ suc v)
EnrichedCats = record
  { enriched = record
    { Obj = Category v
    ; hom = EnrichedFunctors
    ; id  = const idF
    ; ⊚   = ⊚
    ; ⊚-assoc = λ {_ _ C D} →
      let module C = Underlying C
          module D = Underlying D
          open UnderlyingReasoning D
      in niHelper record
        { η       = λ { ((F , G) , H) → from (NI.associator {F = F} {G} {H}) }
        ; η⁻¹     = λ { ((F , G) , H) → to   (NI.associator {F = F} {G} {H}) }
        ; commute = λ { {(_ , G₁) , H₁} {(F₂ , G₂) , _} ((α , β) , γ) {X} →
          begin
            D.id ∘ (F₂ ∘F G₂) $₁ γ [ X ] ∘ F₂ $₁ β [ H₁ $₀ X ] ∘
            α [ G₁ $₀ H₁ $₀ X ]
          ≈⟨ identityˡ ○ ⟺ assoc ⟩
            ((F₂ ∘F G₂) $₁ γ [ X ] ∘ F₂ $₁ β [ H₁ $₀ X ]) ∘ α [ G₁ $₀ H₁ $₀ X ]
          ≈⟨ V.assoc ⟩∘⟨refl ⟩∘⟨refl ⟩
            (F₂ $₁ G₂ $₁ γ [ X ] ∘ F₂ $₁ β [ H₁ $₀ X ]) ∘ α [ G₁ $₀ H₁ $₀ X ]
          ≈˘⟨ UF.homomorphism F₂ ⟩∘⟨refl ⟩
            F₂ $₁ (G₂ $₁ γ [ X ] C.∘ β [ H₁ $₀ X ]) ∘ α [ G₁ $₀ H₁ $₀ X ]
          ≈˘⟨ identityʳ ⟩
            (F₂ $₁ (G₂ $₁ γ [ X ] C.∘ β [ H₁ $₀ X ]) ∘ α [ G₁ $₀ H₁ $₀ X ]) ∘
            D.id
          ∎ }
        ; iso = λ{ ((F , G) , H) → iso (NI.associator {F = F} {G} {H}) }
        }
    ; unitˡ = λ {A B} →
      let module A = Underlying A
          module B = Underlying B
          open UnderlyingReasoning B
      in niHelper record
        { η       = λ _ → from NI.unitorˡ
        ; η⁻¹     = λ _ → to   NI.unitorˡ
        ; commute = λ { {_ , F} {_ , G} (_ , α) {X} →
          begin
            B.id ∘ (V.id V.∘ α [ X ]) ∘ B.id   ≈⟨ identityˡ ⟩
            (V.id V.∘ α [ X ]) ∘ B.id          ≈⟨ V.identityˡ ⟩∘⟨refl ⟩
            α [ X ] ∘ B.id                     ∎ }
        ; iso = λ _ → iso NI.unitorˡ
        }
    ; unitʳ = λ {A B} →
      let module A = Underlying A
          module B = Underlying B
          open UnderlyingReasoning B
      in niHelper record
        { η       = λ _ → from NI.unitorʳ
        ; η⁻¹     = λ _ → to   NI.unitorʳ
        ; commute = λ{ {_} {G , _} (α , _) {X} →
          begin
            B.id ∘ G $₁ A.id ∘ α [ X ]  ≈⟨ identityˡ ⟩
            G $₁ A.id ∘ α [ X ]         ≈⟨ UF.identity G ⟩∘⟨refl ⟩
            B.id ∘ α [ X ]              ≈⟨ identityˡ ○ ⟺ identityʳ ⟩
            α [ X ] ∘ B.id              ∎ }
        ; iso     = λ _ → iso NI.unitorʳ
        }
    }
  ; triangle = λ {_ B C _ G} →
    let module B = Underlying B
        module C = Underlying C
        open UnderlyingReasoning C
    in begin
      (G $₁ B.id ∘ C.id) ∘ C.id   ≈⟨ identityʳ ⟩
      G $₁ B.id ∘ C.id            ∎
  ; pentagon = λ {_ B _ D E _ G H I} →
    let module B  = Category B
        module D  = Category D
        module E  = Category E
        open UnderlyingReasoning E
    in begin
      (I $₁ D.id ∘ E.id) ∘ E.id ∘ (I ∘F H ∘F G) $₁ B.id ∘ E.id
    ≈⟨ identityʳ ⟩∘⟨ (identityˡ ○ identityʳ) ⟩
      I $₁ D.id ∘ (I ∘F H ∘F G) $₁ B.id
    ≈⟨ UF.identity I ⟩∘⟨ UF.identity (I ∘F H ∘F G) ⟩
      E.id ∘ E.id
    ∎
  }

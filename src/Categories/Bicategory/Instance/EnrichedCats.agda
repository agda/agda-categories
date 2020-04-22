{-# OPTIONS --without-K --safe #-}

open import Level
open import Categories.Category using () renaming (Category to Setoid-Category)
open import Categories.Category.Monoidal using (Monoidal)

module Categories.Bicategory.Instance.EnrichedCats
  {o ℓ e} {V : Setoid-Category o ℓ e} (M : Monoidal V) (v : Level) where

-- The 2-category of V-enriched categories

open import Data.Product as Prod using (_,_; proj₁)

open import Categories.Bicategory using (Bicategory)
open import Categories.Category.Construction.EnrichedFunctors M
import Categories.Morphism.Reasoning as MR
open import Categories.Enriched.Category M
open import Categories.Enriched.Category.Underlying M
open import Categories.Enriched.Functor M renaming (id to idF)
open import Categories.Enriched.NaturalTransformation M hiding (id)
import Categories.Enriched.NaturalTransformation.NaturalIsomorphism M as NI
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.Functor.Construction.Constant using (const)
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)

private
  module V = Setoid-Category V
  module UnderlyingReasoning {c} (C : Category c) where
    private
      CC = Underlying C
    open Underlying C using (_∘_; identityʳ; identityˡ; sym-assoc; module HomReasoning) public
    open HomReasoning public
    open MR CC using (id-comm-sym) public
  open NaturalTransformation
  open NI.NaturalIsomorphism

  -- Aliases used to shorten some proof expressions

  module UF = UnderlyingFunctor using (F₀; F₁; homomorphism; identity)
  infixr 14 _$₀_ _$₁_
  _$₀_ = UF.F₀
  _$₁_ = UF.F₁

-- The bicategory of V-enriched categories, functors and natural
-- transformations.
--
-- Note that all the equational reasoning happens in the underlying
-- (ordinary) categories!

-- below, a lot of specification of implicits make things typecheck faster.
EnrichedCats : Bicategory (ℓ ⊔ e ⊔ v) (ℓ ⊔ e ⊔ v) (e ⊔ v) (o ⊔ ℓ ⊔ e ⊔ suc v)
EnrichedCats = record
  { enriched = record
    { Obj = Category v
    ; hom = EnrichedFunctors
    ; id  = const idF
    ; ⊚   = ⊚
    ; ⊚-assoc =  λ {_ _ C D} →
      let module C = Underlying C
          module D = Underlying D
          open UnderlyingReasoning D
      in niHelper record
        { η       = λ { ((F , G) , H) → from (NI.associator {F = F} {G} {H}) }
        ; η⁻¹     = λ { ((F , G) , H) → to   (NI.associator {F = F} {G} {H}) }
        ; commute = λ { {(_ , G₁) , H₁} {(F₂ , G₂) , _} ((α , β) , γ) {X} →
          -- short hands for terms that never change
          let α′ = α [ G₁ $₀ H₁ $₀ X ]
              β′ = β [ H₁ $₀ X ]
          in begin
            D.id ∘ (F₂ ∘F G₂) $₁ γ [ X ] ∘ F₂ $₁ β′ ∘ α′ ≈⟨ identityˡ ○ sym-assoc ⟩
            ((F₂ ∘F G₂) $₁ γ [ X ] ∘ F₂ $₁ β′) ∘ α′      ≈⟨ V.assoc ⟩∘⟨refl ⟩∘⟨refl ⟩
            (F₂ $₁ G₂ $₁ γ [ X ] ∘ F₂ $₁ β′) ∘ α′        ≈˘⟨ UF.homomorphism F₂ ⟩∘⟨refl ⟩
            F₂ $₁ (G₂ $₁ γ [ X ] C.∘ β′) ∘ α′            ≈˘⟨ identityʳ ⟩
            (F₂ $₁ (G₂ $₁ γ [ X ] C.∘ β′) ∘ α′) ∘ D.id   ∎ }
        ; iso = λ{ ((F , G) , H) → iso (NI.associator {F = F} {G} {H}) }
        }
    ; unitˡ =  λ {A B} →
      let module A = Underlying A
          module B = Underlying B
          open UnderlyingReasoning B
      in niHelper record
        { η       = λ {(_ , F) → from (NI.unitorˡ {C = A} {B} {F})}
        ; η⁻¹     = λ {(lift tt , F) → to (NI.unitorˡ {C = A} {B} {F})}
        ; commute = λ { {_ , F} {_ , G} (_ , α) {X} →
          begin
            B.id ∘ (V.id V.∘ α [ X ]) ∘ B.id   ≈⟨ identityˡ ⟩
            (V.id V.∘ α [ X ]) ∘ B.id          ≈⟨ V.identityˡ ⟩∘⟨refl ⟩
            α [ X ] ∘ B.id                     ∎ }
        ; iso = λ {(_ , F) → iso (NI.unitorˡ {C = A} {B} {F})}
        }
    ; unitʳ = λ {A B} →
      let module A = Underlying A using (id)
          module B = Underlying B
          open UnderlyingReasoning B
      in niHelper record
        { η =  λ {(F , lift tt) → from (NI.unitorʳ {C = A} {B} {F}) }
        ; commute =  λ{ {_} {G , _} (α , _) {X} →
            begin
              B.id ∘ G $₁ A.id ∘ α [ X ]  ≈⟨ identityˡ ⟩
              G $₁ A.id ∘ α [ X ]         ≈⟨ UF.identity G ⟩∘⟨refl ⟩
              B.id ∘ α [ X ]              ≈⟨ id-comm-sym ⟩
              α [ X ] ∘ B.id              ∎ }
        ; η⁻¹  = λ { (F , lift tt) → to (NI.unitorʳ {C = A} {B} {F}) }
        ; iso  = λ { (F , lift tt) → iso (NI.unitorʳ {C = A} {B} {F}) }
        }
    }
  ; triangle = λ {_ _ C f g X} → UnderlyingReasoning.identityʳ C
  ; pentagon = λ {_ B _ D E _ G H I} →
    let module B  = Category B using (id)
        module D  = Category D using (id)
        module E  = Category E using (id)
        open UnderlyingReasoning E
    in begin
      (I $₁ D.id ∘ E.id) ∘ E.id ∘ (I ∘F H ∘F G) $₁ B.id ∘ E.id ≈⟨ identityʳ ⟩∘⟨ identityˡ ⟩
      I $₁ D.id ∘ (I ∘F H ∘F G) $₁ B.id ∘ E.id                 ≈⟨ refl⟩∘⟨ identityʳ ⟩
      I $₁ D.id ∘ (I ∘F H ∘F G) $₁ B.id                        ≈⟨ UF.identity I ⟩∘⟨ UF.identity (I ∘F H ∘F G) ⟩
      E.id ∘ E.id
    ∎
  }

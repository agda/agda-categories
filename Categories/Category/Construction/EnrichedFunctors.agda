{-# OPTIONS --without-K --safe #-}

open import Categories.Category using () renaming (Category to Setoid-Category)
open import Categories.Category.Monoidal

module Categories.Category.Construction.EnrichedFunctors
  {o ℓ e} {V : Setoid-Category o ℓ e} (M : Monoidal V) where

-- The (enriched) functor category for a given pair of V-enriched categories

open import Level
open import Data.Product using (_,_; uncurry′)

open import Categories.Enriched.Category M
open import Categories.Enriched.Functor M renaming (id to idF)
open import Categories.Enriched.NaturalTransformation M renaming (id to idNT)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.Morphism.Reasoning V
open import Categories.NaturalTransformation using (ntHelper)

open Setoid-Category V renaming (Obj to ObjV; id to idV)
open Monoidal M
open MonoidalReasoning V M
open NaturalTransformation

EnrichedFunctors : ∀ {c d} (C : Category c) (D : Category d) →
                   Setoid-Category (ℓ ⊔ e ⊔ c ⊔ d) (ℓ ⊔ e ⊔ c) (e ⊔ c)
EnrichedFunctors C D = record
  { Obj = Functor C D
  ; _⇒_ = NaturalTransformation
  ; _≈_ = λ α β → ∀ {X} → α [ X ] ≈ β [ X ]
  ; id  = idNT
  ; _∘_ = _∘ᵥ_
  ; assoc     = U.assoc
  ; sym-assoc = U.sym-assoc
  ; identityˡ = U.identityˡ
  ; identityʳ = U.identityʳ
  ; identity² = U.identity²
  ; equiv     = record
    { refl  = U.Equiv.refl
    ; sym   = λ α≈β → U.Equiv.sym α≈β
    ; trans = λ α≈β β≈γ → U.Equiv.trans α≈β β≈γ
    }
  ; ∘-resp-≈ = λ α₁≈β₁ α₂≈β₂ → U.∘-resp-≈ α₁≈β₁ α₂≈β₂
  }
  where module U = Underlying D

-- Horizontal composition of natural transformations (aka the Godement
-- product) induces a composition functor over functor categories.

⊚ : ∀ {c d e} {C : Category c} {D : Category d} {E : Category e} →
    Bifunctor (EnrichedFunctors D E) (EnrichedFunctors C D) (EnrichedFunctors C E)
⊚ {_} {_} {_} {_} {D} {E} = record
  { F₀ = uncurry′ _∘F_
  ; F₁ = uncurry′ _∘ₕ_
  ; identity = λ{ {F , G} {X} →
    let module F = Functor F
    in begin
      (F.₁ ∘ D.id) ∙ E.id   ≈⟨ UE.identityʳ ⟩
      F.₁ ∘ D.id            ≈⟨ UF.identity F ⟩
      E.id                  ∎ }
  ; homomorphism = λ{ {_ , F₂} {G₁ , G₂} {H₁ , _} {α₁ , α₂} {β₁ , β₂} {X} →
    let module F₂ = Functor F₂
        module G₁ = Functor G₁
        module G₂ = Functor G₂
        module H₁ = Functor H₁
    in begin
      (H₁.₁ ∘ β₂ [ X ] UD.∘ α₂ [ X ]) ∙ β₁ [ F₂.₀ X ] ∙ α₁ [ F₂.₀ X ]
    ≈⟨ UF.homomorphism H₁ UR.⟩∘⟨refl ⟩
      ((H₁.₁ ∘ β₂ [ X ]) ∙ (H₁.₁ ∘ α₂ [ X ])) ∙ β₁ [ F₂.₀ X ] ∙ α₁ [ F₂.₀ X ]
    ≈⟨ ⟺ UE.assoc ○ (UE.assoc UR.⟩∘⟨refl) ⟩
      ((H₁.₁ ∘ β₂ [ X ]) ∙ ((H₁.₁ ∘ α₂ [ X ]) ∙ β₁ [ F₂.₀ X ])) ∙
      α₁ [ F₂.₀ X ]
    ≈˘⟨ (UR.refl⟩∘⟨ UnderlyingNT.commute β₁ (α₂ [ X ])) UR.⟩∘⟨refl ⟩
      ((H₁.₁ ∘ β₂ [ X ]) ∙ (β₁ [ G₂.₀ X ] ∙ (G₁.₁ ∘ α₂ [ X ]))) ∙
      α₁ [ F₂.₀ X ]
    ≈˘⟨ ⟺ UE.assoc ○ UE.∘-resp-≈ UE.assoc UE.Equiv.refl ⟩
      ((H₁.₁ ∘ β₂ [ X ]) ∙ β₁ [ G₂.₀ X ]) ∙ (G₁.₁ ∘ α₂ [ X ]) ∙ α₁ [ F₂.₀ X ]
    ∎ }
  ; F-resp-≈ = λ{ {_} {F , _} (eq₁ , eq₂) → UE.∘-resp-≈ (UF.F-resp-≈ F eq₂) eq₁ }
  }
  where
    module D = Category D
    module E = Category E
    module UD = Underlying D
    module UE = Underlying E
    module UR = UE.HomReasoning
    module UF = UnderlyingFunctor
    open UE using () renaming (_∘_ to _∙_)

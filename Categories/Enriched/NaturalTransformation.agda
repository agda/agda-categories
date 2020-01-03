{-# OPTIONS --without-K --safe #-}

open import Level
open import Categories.Category
open import Categories.Category.Monoidal

module Categories.Enriched.NaturalTransformation {o ℓ e : Level} {V : Category o ℓ e} (M : Monoidal V) where

open import Categories.Enriched.Category renaming (Category to Enriched) hiding (_[_,_])
open import Categories.Enriched.Functor M hiding (id)

private
  variable
    v v′ : Level
    C D E : Enriched M v

open Monoidal M
open Category V hiding (id)
open HomReasoning
private
  λ⇐ = unitorˡ.to
  ρ⇐ = unitorʳ.to

record NaturalTransformation {C : Enriched M v}
                             {D : Enriched M v′}
                             (F G : Functor C D) : Set (ℓ ⊔ e ⊔ v) where
  eta-equality
  private
    module C = Enriched C
    module D = Enriched D
    module F = Functor F
    module G = Functor G
  open Enriched D

  field
    η           : (X : C.Obj) → V [ unit , D.hom (F.₀ X) (G.₀ X) ]
    commute    : {X Y : C.Obj} → V [ (⊚ ∘ (η Y ⊗₁ F.₁) ∘ λ⇐)  ≈ ( ⊚ ∘ G.₁ ⊗₁ η X ∘ ρ⇐) ]

{- This still needs to be completed
id : {F : Functor C D} → NaturalTransformation F F
id {C = C} {D = D} {F = F} = record
  { η = λ X → F₁ X X ∘ Enriched.id C X
  ; commute = λ {X} {Y} → begin
    D.⊚ ∘ (F₁ Y Y ∘ C.id Y) ⊗₁ (F₁ X Y) ∘ λ⇐   ≈⟨ {!!} ⟩
    D.⊚ ∘ (F₁ X Y) ⊗₁ (F₁ X X ∘ C.id X) ∘ ρ⇐   ∎
  }
  where
  open Functor F
  module C = Enriched C
  module D = Enriched D
-}

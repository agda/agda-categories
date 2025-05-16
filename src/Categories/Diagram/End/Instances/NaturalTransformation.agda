{-# OPTIONS --without-K --safe #-}

open import Data.Product using (Σ; _,_)
open import Function using (_$_)
open import Level

open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Category.Product
open import Categories.Diagram.End using () renaming (End to ∫)
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Hom
open import Categories.NaturalTransformation renaming (id to idN)
open import Categories.NaturalTransformation.Dinatural using (DinaturalTransformation; dtHelper)
open import Categories.NaturalTransformation.Equivalence
open import Function.Bundles using (Func)

import Categories.Diagram.Wedge as Wedges
import Categories.Morphism as M
import Categories.Morphism.Reasoning as MR

module Categories.Diagram.End.Instances.NaturalTransformation {ℓ e o′}
  {C : Category ℓ ℓ e} {D : Category o′ ℓ ℓ} (F G : Functor C D) where

private
  module C = Category C
  module D = Category D
  open module F = Functor F using (F₀; F₁)
  module G = Functor G

open Wedges (Hom[ D ][-,-] ∘F (F.op ⁂ G))
open D
open HomReasoning
open MR D
open NaturalTransformation renaming (η to app)
open ∫ hiding (dinatural)
open Wedge
open Func

NTs-are-End : ∫ (Hom[ D ][-,-] ∘F (F.op ⁂ G))
NTs-are-End .wedge .E = (≃-setoid F G)
NTs-are-End .wedge .dinatural = dtHelper record
  { α = λ C → record
    { to = λ η → η .app C
    ; cong = λ e → e
    }
  ; commute = λ {X} {Y} f {η} → begin
    G.₁ f ∘ η .app X ∘ F₁ C.id  ≈⟨ pullˡ (η .sym-commute f) ⟩
    (η .app Y ∘ F₁ f) ∘ F₁ C.id ≈⟨ refl⟩∘⟨ F.identity ⟩
    (η .app Y ∘ F₁ f) ∘ id      ≈⟨ id-comm ⟩
    id ∘ η .app Y ∘ F₁ f        ≈⟨ ⟺ G.identity ⟩∘⟨refl ⟩
    G.₁ C.id ∘ η .app Y ∘ F₁ f  ∎
  }
NTs-are-End .factor W .to s = ntHelper record
  { η = λ X → W.dinatural.α X .to s
  -- basically the opposite proof of above
  ; commute = λ {X} {Y} f → begin
    W.dinatural.α Y .to s ∘ F₁ f            ≈⟨ introˡ G.identity ⟩
    G.₁ C.id ∘ W.dinatural.α Y .to s ∘ F₁ f ≈˘⟨ W.dinatural.commute f ⟩
    G.₁ f ∘ W.dinatural.α X .to s ∘ F₁ C.id ≈⟨ refl⟩∘⟨ elimʳ F.identity ⟩
    G.F₁ f ∘ W.dinatural.α X .to s          ∎
  }
  where module W = Wedge W
NTs-are-End .factor W .cong e {x} = W .dinatural.α x .cong e
NTs-are-End .universal = Equiv.refl
NTs-are-End .unique h = Equiv.sym h

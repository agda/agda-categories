{-# OPTIONS --without-K --safe #-}
module Categories.Diagram.End.Parameterized where

open import Level
open import Function using (_$_)
open import Data.Product using (Σ; _,_)

open import Categories.Category
open import Categories.Category.Construction.Functors
open import Categories.Category.Product renaming (Product to _×ᶜ_)
open import Categories.Diagram.End renaming (End to ∫)
open import Categories.Diagram.End.Limit
open import Categories.Diagram.End.Properties hiding (EndF)
open import Categories.Diagram.Wedge
open import Categories.Functor hiding (id)
open import Categories.Functor.Bifunctor
open import Categories.Functor.Bifunctor.Properties
open import Categories.Functor.Limits
open import Categories.NaturalTransformation renaming (_∘ʳ_ to _▹ⁿ_; id to idN)
open import Categories.NaturalTransformation.Dinatural hiding (_≃_)
open import Categories.NaturalTransformation.NaturalIsomorphism renaming (_≃_ to _≃ⁱ_)
open import Categories.NaturalTransformation.Equivalence

import Categories.Category.Construction.Wedges as Wedges
import Categories.Morphism as M
import Categories.Morphism.Reasoning as MR

-- The following conventions are taken in this file: C is the 'source' category
-- and D is the destination. If two source categories are needed, the other is
-- called 'P' for "parameter", following MacLane. F, G and H are functors and ef,
-- eg and eh are witnesses of their respective ends.

private
  variable
    o ℓ e : Level
    P C D E : Category o ℓ e

-- we use MacLane's notation for paramaterized ends (CWM §IX.5)
_♯ : Functor (P ×ᶜ (Category.op C ×ᶜ C)) D → Functor (Category.op C ×ᶜ C) (Functors P D)
F ♯ = curry.₀ F.flip
  where module F = Bifunctor F

end-η♯ : {F G : Functor (P ×ᶜ (Category.op C ×ᶜ C)) D} (η : NaturalTransformation F G)
         ⦃ ef : ∫ (F ♯) ⦄ ⦃ eg : ∫ (G ♯) ⦄ → NaturalTransformation (∫.E ef) (∫.E eg)
end-η♯ η ⦃ ef ⦄ ⦃ eg ⦄ = end-η (curry.₁ (η ▹ⁿ Swap))

module _ (F : Functor (P ×ᶜ ((Category.op C) ×ᶜ C)) D) {ω : ∀ X → ∫ (appˡ F X)} where
  private
    module F = Functor F

    module C = Category C
    module D = Category D
    module P = Category P
    module NT = NaturalTransformation
    F′ = curry.₀ F
    module ω (p : P.Obj) = ∫ (ω p)
  open D
  open HomReasoning

  open MR D
  open module F′ = Functor F′
  open ∫ hiding (E)
  open NT using (η)

  EndF : Functor P D
  EndF = record
    { F₀           = λ X → ω.E X
    ; F₁           = λ {X} {Y} f → end-η (curry.₀.₁ F f) ⦃ ω X ⦄ ⦃ ω Y ⦄
    ; identity     = λ {A} → begin
      end-η (curry.₀.₁ F P.id) ⦃ ω A ⦄ ⦃ ω A ⦄ ≈⟨ end-η-resp-≈ ⦃ ω A ⦄ ⦃ ω A ⦄ (curry.₀.identity F) ⟩
      end-η idN ⦃ ω A ⦄ ⦃ ω A ⦄                ≈⟨ end-identity ⦃ ω A ⦄ ⟩
      id                                       ∎
    ; homomorphism = λ {A B C} {f g} → begin
      end-η (curry.₀.₁ F (P [ g ∘ f ])) ⦃ ω A ⦄ ⦃ ω C ⦄ 
        ≈⟨ end-η-resp-≈ ⦃ ω A ⦄ ⦃ ω C ⦄ (curry.₀.homomorphism F) ⟩
      end-η (curry.₀.₁ F g ∘ᵥ curry.₀.₁ F f ) ⦃ ω A ⦄ ⦃ ω C ⦄
        ≈⟨  end-η-resp-∘ (curry.₀.₁ F f) (curry.₀.₁ F g) ⦃ ω A ⦄ ⦃ ω B ⦄ ⦃ ω C ⦄ ⟩
      end-η (curry.₀.₁ F g) ⦃ ω B ⦄ ⦃ ω C ⦄ ∘ end-η (curry.₀.₁ F f) ⦃ ω A ⦄ ⦃ ω B ⦄
        ∎
    ; F-resp-≈     = λ {A B f g} eq → end-η-resp-≈ ⦃ ω A ⦄ ⦃ ω B ⦄ (curry.₀.F-resp-≈ F eq)
    }


  -- The parameter theorem
  EndF-is-End : ∫ (F ♯)
  EndF-is-End .∫.wedge .Wedge.E = EndF
  EndF-is-End .∫.wedge .Wedge.dinatural = dtHelper record
    { α = λ c → ntHelper record
      { η = λ p → ω.dinatural.α p c
      ; commute = λ {p} {q} f → begin
        ω.dinatural.α q c ∘ end-η (curry.₀.₁ F f) ⦃ ω p ⦄ ⦃ ω q ⦄
        ≈⟨ end-η-commute ⦃ ω p ⦄ ⦃ ω q ⦄ (curry.₀.₁ F f) c ⟩
        (curry.₀.₁ F f) .η (c , c) ∘ ω.dinatural.α p c
        ∎
      }
    ; commute = λ f {p} → ω.dinatural.commute p f
    }
  EndF-is-End .∫.factor W = ntHelper record
    { η = λ p → ω.factor p (W' p)
    ; commute = λ {p} {q} f → ω.unique′ q $ λ {c} → begin
      ω.dinatural.α q c ∘ ω.factor q (W' q) ∘ F'.₁ f
      ≈⟨ pullˡ (ω.universal q) ⟩
      W.dinatural.α c .η q ∘ F'.₁ f 
      ≈⟨ W.dinatural.α c .NaturalTransformation.commute f  ⟩
      (curry.₀.₁ F f) .η (c , c) ∘ W.dinatural.α c .η p
      ≈˘⟨ refl⟩∘⟨ ω.universal p ⟩
      (curry.₀.₁ F f) .η (c , c) ∘ ω.dinatural.α p c ∘ factor (ω p) (W' p)
      ≈˘⟨ extendʳ  (end-η-commute ⦃ ω p ⦄ ⦃ ω q ⦄ (curry.₀.₁ F f) c) ⟩
      ω.dinatural.α q c ∘ end-η (curry.₀.₁ F f) ⦃ ω p ⦄ ⦃ ω q ⦄ ∘ ω.factor p (W' p)
      ∎
    }
    where module W = Wedge W
          F' = W.E
          module F' = Functor F'
          W' : (p : P.Obj) → Wedge (appˡ F p)
          W' p = record
            { E = F'.₀ p
            ; dinatural = dtHelper record
              { α = λ c → W.dinatural.α c .η p
              ; commute = λ f → W.dinatural.commute f
              }
            }
          module W' p = Wedge (W' p)
  EndF-is-End .∫.universal {W} {c} {p} = ω.universal p
  EndF-is-End .∫.unique h {p} = ω.unique p h

-- Continuous functors preserve EndF
-- this takes way too much time to check for some reason
module _ {C : Category o ℓ e}
         (J : Functor (P ×ᶜ ((Category.op C) ×ᶜ C)) D)
         (F : Functor D E) {ω : ∀ X → ∫ (appˡ J X)} {cont : Continuous (o ⊔ ℓ) (ℓ ⊔ e) e F} where
  private
    module D = Category D
    module P = Category P
    module C = Category C
    module E = Category E
    open module F = Functor F using (F₀; F₁; F-resp-≈)
    open module J = Functor J using () renaming (F₀ to J₀; F₁ to J₁)
    module ω (X : P.Obj) = ∫ (ω X)
    module appˡJ  = curry.₀ J
    module appˡFJ  = curry.₀ (F ∘F J)

  open E
  open HomReasoning
  appˡ-resp-∘ : ∀ X → F ∘F appˡ J X ≃ⁱ appˡ (F ∘F J) X
  appˡ-resp-∘ X = niHelper record
    { η = λ Y → id
    ; η⁻¹ = λ Y → id
    ; commute = λ f → identityˡ ○ ⟺ identityʳ
    ; iso = λ Y → record
      { isoˡ = identity²
      ; isoʳ = identity²
      }
    }
  --module appˡ-resp-∘ X = NaturalIsomorphism (appˡ-resp-∘ X)

  open NaturalTransformation using (η)
  open MR E

  Fω : ∀ X → ∫ (appˡ (F ∘F J) X)
  Fω X = ≅-yields-end (appˡ-resp-∘ X) (contF-as-end (appˡ J X) F {cont} (ω X))
  module Fω (p : P.Obj) = ∫ (Fω p)

  Fω≈Fω : ∀ {p : P.Obj} {c : C.Obj} → Fω.dinatural.α p c ≈ F.₁ (ω.dinatural.α p c)
  Fω≈Fω {p} {A} = begin
    Fω.dinatural.α p A
      ≡⟨⟩
    id ∘ F₁ (J₁ (P.id , C.id , C.id)) ∘
    id ∘ F₁ (J₁ (P.id , C.id , C.id) D.∘ ω.dinatural.α p A)
      ≈⟨ identityˡ ⟩
    F₁ (J₁ (P.id , C.id , C.id)) ∘
    id ∘ F₁ (J₁ (P.id , C.id , C.id) D.∘ ω.dinatural.α p A)
      ≈⟨ F-resp-≈ J.identity ⟩∘⟨refl ⟩
    F₁ (D.id) ∘ id ∘ F₁ (J₁ (P.id , C.id , C.id) D.∘ ω.dinatural.α p A)
      ≈⟨ elimˡ F.identity ⟩
    id ∘ F₁ (J₁ (P.id , C.id , C.id) D.∘ ω.dinatural.α p A)
      ≈⟨ identityˡ ⟩
    F₁ (J₁ (P.id , C.id , C.id) D.∘ ω.dinatural.α p A)
      ≈⟨ F-resp-≈ (D.∘-resp-≈ˡ J.identity) ⟩
    F₁ (D.id D.∘ ω.dinatural.α p A)
      ≈⟨ F-resp-≈ D.identityˡ ⟩
    F₁ (ω.dinatural.α p A) 
      ∎

  Continuous-pres-EndF :  F ∘F (EndF J {ω}) ≃ⁱ EndF (F ∘F J) {Fω}
  Continuous-pres-EndF = niHelper record
    { η = λ X → E.id
    ; η⁻¹ = λ Y → E.id
    ; commute = λ {p} {q} f → begin
      id ∘ Functor.F₁ (F ∘F EndF J {ω}) f ≈⟨ identityˡ ⟩
      Functor.F₁ (F ∘F EndF J {ω}) f      ≡⟨⟩
      F₁ (end-η (appˡJ.₁ f) ⦃ ω p ⦄ ⦃ ω q ⦄)
        ≈⟨ Fω.unique′ q (λ {A} → begin
          Fω.dinatural.α q A ∘ F₁ (end-η (appˡJ.₁ f) ⦃ ω p ⦄ ⦃ ω q ⦄)
            ≈⟨ Fω≈Fω ⟩∘⟨refl ⟩
          F₁ (ω.dinatural.α q A) ∘ F₁ (end-η (appˡJ.₁ f) ⦃ ω p ⦄ ⦃ ω q ⦄)
            ≈˘⟨ F.homomorphism ⟩
          F₁ (ω.dinatural.α q A D.∘ end-η (appˡJ.₁ f) ⦃ ω p ⦄ ⦃ ω q ⦄)
            ≈⟨ F-resp-≈ (end-η-commute ⦃ ω p ⦄ ⦃ ω q ⦄ (appˡJ.₁ f) A ) ⟩
          F₁ ((appˡJ.₁ f) .η (A , A) D.∘ (ω.dinatural.α p A))
            ≈⟨ F.homomorphism ⟩
          F₁ ((appˡJ.₁ f) .η (A , A)) ∘ F₁ (ω.dinatural.α p A)
            ≈˘⟨ refl⟩∘⟨ Fω≈Fω ⟩
          F₁ ((appˡJ.₁ f) .η (A , A)) ∘ (Fω.dinatural.α p A)
            ≡⟨⟩
          appˡFJ.₁ f .η (A , A) ∘ Fω.dinatural.α p A
            ≈˘⟨ end-η-commute ⦃ Fω p ⦄ ⦃ Fω q ⦄ (appˡFJ.₁ f) A ⟩
          Fω.dinatural.α q A ∘ end-η (appˡFJ.₁ f) ⦃ Fω p ⦄ ⦃ Fω q ⦄
            ∎
        )⟩
      end-η (appˡFJ.₁ f) ⦃ Fω p ⦄ ⦃ Fω q ⦄
        ≡⟨⟩
      Functor.F₁ (EndF (F ∘F J) {Fω}) f   ≈˘⟨ identityʳ ⟩
      Functor.F₁ (EndF (F ∘F J) {Fω}) f ∘ id
        ∎
    ; iso = λ Y → record
      { isoˡ = E.identity²
      ; isoʳ = E.identity²
      }
    }
    where open E.HomReasoning

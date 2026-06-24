{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Experiments.Category.Abelian

-- The Faithful Embedding Theorem for Abelian Categories
module Experiments.Category.Abelian.Embedding.Faithful {o ℓ e} {𝒜 : Category o ℓ e} (abelian : Abelian 𝒜) where

open import Level
open import Data.Product using (_,_)

import Relation.Binary.Reasoning.Setoid as SR

open import Categories.Category.SubCategory
open import Categories.Category.Construction.Functors

open import Categories.Functor
open import Categories.NaturalTransformation
open import Categories.Yoneda

import Categories.Morphism.Reasoning as MR

open import Categories.Category.Preadditive
open import Experiments.Category.Additive
open import Experiments.Category.Instance.AbelianGroups

open import Experiments.Functor.Exact

open AbelianGroupHomomorphism
open AbelianGroup

Lex : ∀ (c′ ℓ′ : Level) → Category (o ⊔ ℓ ⊔ e ⊔ suc c′ ⊔ suc ℓ′) (o ⊔ ℓ ⊔ c′ ⊔ ℓ′) (o ⊔ c′ ⊔ ℓ′)
Lex c′ ℓ′ = FullSubCategory′ (Functors 𝒜 (AbelianGroups c′ ℓ′)) LeftExact


-- NOTE: I think I can do this with any functor, not just a lex functor...
LexPreadditive : ∀ (c′ ℓ′ : Level) → Preadditive (Lex c′ ℓ′)
LexPreadditive c′ ℓ′ = record
  { _+_ = λ { {F , F-Lex} {G , G-Lex} α β →
    let module F = Functor F
        module G = Functor G
        module α = NaturalTransformation α
        module β = NaturalTransformation β
    in ntHelper record
      { η = λ A →
        let open SR (setoid (G.F₀ A))
            -- Why do all of this work when we can get the combinators for freeeee
            open MR (Delooping (G.F₀ A))
        in record
          { ⟦_⟧ = λ fa → G.F₀ A [ ⟦ α.η A ⟧ fa ∙ ⟦ β.η A ⟧ fa ]
          ; cong = λ {fa} {fb} eq → begin
            G.F₀ A [ ⟦ α.η A ⟧ fa ∙ ⟦ β.η A ⟧ fa ] ≈⟨ ∙-cong (G.F₀ A) (cong (α.η A) eq) (cong (β.η A) eq) ⟩
            G.F₀ A [ ⟦ α.η A ⟧ fb ∙ ⟦ β.η A ⟧ fb ] ∎
          ; homo = λ x y → begin
            G.F₀ A [ (⟦ α.η A ⟧ (F.F₀ A [ x ∙ y ])) ∙ ⟦ β.η A ⟧ (F.F₀ A [ x ∙ y ]) ]                 ≈⟨ ∙-cong (G.F₀ A) (homo (α.η A) x y) (homo (β.η A) x y) ⟩
            G.F₀ A [ G.F₀ A [ ⟦ α.η A ⟧ x ∙ ⟦ α.η A ⟧ y ] ∙ G.F₀ A [ ⟦ β.η A ⟧ x ∙ ⟦ β.η A ⟧ y ] ]   ≈⟨ center (comm (G.F₀ A) _ _) ⟩
            G.F₀ A [ ⟦ α.η A ⟧ x ∙ G.F₀ A [ G.F₀ A [ ⟦ β.η A ⟧ x ∙ ⟦ α.η A ⟧ y ] ∙ ⟦ β.η A ⟧ y ] ]   ≈⟨ pull-first (refl (G.F₀ A)) ⟩
            G.F₀ A [ G.F₀ A [ ⟦ α.η A ⟧ x ∙ ⟦ β.η A ⟧ x ] ∙ G.F₀ A [ ⟦ α.η A ⟧ y ∙ ⟦ β.η A ⟧ y ] ]   ∎
          }
      ; commute = λ {X} {Y} f fx →
        let open SR (setoid (G.F₀ Y))
        in begin
          G.F₀ Y [ ⟦ α.η Y ⟧ (⟦ F.F₁ f ⟧ fx) ∙ ⟦ β.η Y ⟧ (⟦ F.F₁ f ⟧ fx) ] ≈⟨ ∙-cong (G.F₀ Y) (α.commute f fx) (β.commute f fx) ⟩
          G.F₀ Y [ ⟦ G.F₁ f ⟧ (⟦ α.η X ⟧ fx) ∙ ⟦ G.F₁ f ⟧ (⟦ β.η X ⟧ fx) ] ≈˘⟨ homo (G.F₁ f) (⟦ α.η X ⟧ fx) (⟦ β.η X ⟧ fx) ⟩
          ⟦ G.F₁ f ⟧ (G.F₀ X [ ⟦ α.η X ⟧ fx ∙ ⟦ β.η X ⟧ fx ])              ∎
      }}
  ; 0H = λ { {F , F-Lex} {G , G-Lex} →
    let module F = Functor F
        module G = Functor G
    in ntHelper record
      { η = λ A →
        let open SR (setoid (G.F₀ A))
        in record
          { ⟦_⟧ = λ _ → ε (G.F₀ A)
          ; cong = λ _ → refl (G.F₀ A)
          ; homo = λ _ _ → sym (G.F₀ A) (identityʳ (G.F₀ A) _)
          }
      ; commute = λ {X} {Y} f x → sym (G.F₀ Y) (ε-homo (G.F₁ f))
      }}
  ; -_ = λ { {F , F-Lex} {G , G-Lex} α →
    let module F = Functor F
        module G = Functor G
        module α = NaturalTransformation α
    in ntHelper record
      { η = λ A →
        let open SR (setoid (G.F₀ A))
        in record
          { ⟦_⟧ = λ fa → G.F₀ A [ ⟦ α.η A ⟧ fa ⁻¹]
          ; cong = λ {fa} {fb} eq → begin
            (G.F₀ A [ ⟦ α.η A ⟧ fa ⁻¹]) ≈⟨ ⁻¹-cong (G.F₀ A) (cong (α.η A) eq) ⟩
            (G.F₀ A [ ⟦ α.η A ⟧ fb ⁻¹]) ∎
          ; homo = λ x y → begin
            G.F₀ A [ ⟦ α.η A ⟧ (F.F₀ A [ x ∙ y ]) ⁻¹]                      ≈⟨ ⁻¹-cong (G.F₀ A) (homo (α.η A) x y) ⟩
            (G.F₀ A [ G.F₀ A [ ⟦ α.η A ⟧ x ∙ ⟦ α.η A ⟧ y ] ⁻¹] )           ≈⟨ ⁻¹-distrib-∙ (G.F₀ A) (⟦ α.η A ⟧ x) (⟦ α.η A ⟧ y) ⟩
            G.F₀ A [ G.F₀ A [ ⟦ α.η A ⟧ x ⁻¹] ∙ G.F₀ A [ ⟦ α.η A ⟧ y ⁻¹] ] ∎
          }
      ; commute = λ {X} {Y} f fx →
        let open SR (setoid (G.F₀ Y))
        in begin
          G.F₀ Y [ ⟦ α.η Y ⟧ (⟦ F.F₁ f ⟧ fx) ⁻¹] ≈⟨ ⁻¹-cong (G.F₀ Y) (α.commute f fx) ⟩
          G.F₀ Y [ ⟦ G.F₁ f ⟧ (⟦ α.η X ⟧ fx) ⁻¹] ≈˘⟨ ⁻¹-homo (G.F₁ f) (⟦ α.η X ⟧ fx) ⟩
          ⟦ G.F₁ f ⟧ (G.F₀ X [ ⟦ α.η X ⟧ fx ⁻¹]) ∎
      }}
  ; HomIsAbGroup = λ { (F , F-Lex) (G , G-Lex) →
    let module F = Functor F
        module G = Functor G
    in record
      { isGroup = record
        { isMonoid = record
          { isSemigroup = record
            { isMagma = record
              { isEquivalence = record
                { refl = λ {_} {A} _ → refl (G.F₀ A)
                ; sym = λ eq {A} fx → sym (G.F₀ A) (eq fx)
                ; trans = λ eq₁ eq₂ {A} fx → trans (G.F₀ A) (eq₁ fx) (eq₂ fx)
                }
              ; ∙-cong = λ eq₁ eq₂ {A} fx → ∙-cong (G.F₀ A) (eq₁ fx) (eq₂ fx)
              }
            ; assoc = λ _ _ _ {A} _ → assoc (G.F₀ A) _ _ _
            }
          ; identity = (λ _ {A} _ → identityˡ (G.F₀ A) _) , (λ _ {A} _ → identityʳ (G.F₀ A) _)
          }
        ; inverse = (λ _ {A} _ → inverseˡ (G.F₀ A) _) , (λ _ {A} _ → inverseʳ (G.F₀ A) _)
        ; ⁻¹-cong = λ eq {A} fx → ⁻¹-cong (G.F₀ A) (eq fx)
        }
      ; comm = λ _ _ {A} _ → comm (G.F₀ A) _ _
      }}
  ; +-resp-∘ = λ { {F , F-Lex} {G , G-Lex} {H , H-Lex} {I , I-Lex} {α} {β} {γ} {δ} {A} x →
    let module α = NaturalTransformation α
        module β = NaturalTransformation β
        module γ = NaturalTransformation γ
        module δ = NaturalTransformation δ
    in homo (δ.η A) (⟦ α.η A ⟧ (⟦ γ.η A ⟧ x)) (⟦ β.η A ⟧ (⟦ γ.η A ⟧ x))
    }
  }

LexAdditive : ∀ (c′ ℓ′ : Level) → Additive (Lex c′ ℓ′)
LexAdditive c′ ℓ′ = record
  { preadditive = LexPreadditive c′ ℓ′
  ; 𝟎 = record
    { 𝟘 =
      -- This will just map to the zero object
      let 𝟘F = record
            { F₀ = λ _ → {!!}
            ; F₁ = {!!}
            ; identity = {!!}
            ; homomorphism = {!!}
            ; F-resp-≈ = {!!}
            }
      in 𝟘F , {!!}
    ; isZero = {!!}
    }
  ; biproduct = {!!}
  }

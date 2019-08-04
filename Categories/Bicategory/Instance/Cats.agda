{-# OPTIONS --without-K --safe #-}

module Categories.Bicategory.Instance.Cats where

-- The category of categories (Cats) is a Bicategory
open import Level
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)

open import Categories.Bicategory using (Bicategory)
open import Categories.Category using (Category)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.NaturalTransformation using (NaturalTransformation) renaming (id to idN)
open import Categories.NaturalTransformation.NaturalIsomorphism
open import Categories.Category.Instance.One using (One)
open import Categories.Category.Product using (Product; πˡ; πʳ; _※_)
open import Categories.Category.Construction.Functors
open import Categories.Functor.Construction.Constant

private
  variable
    o ℓ e t : Level

Cats : (o ℓ e : Level) → Bicategory (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) (o ⊔ e) (suc (o ⊔ ℓ ⊔ e))
Cats o ℓ e = record
  { Obj = Category o ℓ e
  ; hom = Functors
  ; id = λ A → const {D = Functors A A} {C = One} idF
  ; ⊚ = product
    -- inline the proof of ⊚-assoc , otherwise typechecking time goes nuts
  ; ⊚-assoc = λ {A} {B} {C} {D} →
    let module D = Category D in
    let module C = Category C in record
    { F⇒G = record
      { η =  λ { ((F₁ , F₂) , F₃) → F⇐G (associator F₃ F₂ F₁)}
      ; commute = λ { {(G₁ , G₂) , G₃} {(H₁ , H₂) , H₃} ((η₁ , η₂) , η₃) {x} →
        let open Category D in let open HomReasoning in begin
        id ∘ F₁ H₁ (F₁ H₂ (η η₃ x) C.∘ η η₂ (F₀ G₃ x)) ∘ η η₁ (F₀ G₂ (F₀ G₃ x))
            ≈⟨ identityˡ ⟩
        F₁ H₁ (F₁ H₂ (η η₃ x) C.∘ η η₂ (F₀ G₃ x)) ∘ η η₁ (F₀ G₂ (F₀ G₃ x))
            ≈⟨ homomorphism H₁ ⟩∘⟨refl ⟩
        (F₁ H₁ (F₁ H₂ (η η₃ x)) ∘ F₁ H₁ (η η₂ (F₀ G₃ x))) ∘ η η₁ (F₀ G₂ (F₀ G₃ x))
            ≈⟨ assoc ⟩
        F₁ H₁ (F₁ H₂ (η η₃ x)) ∘ F₁ H₁ (η η₂ (F₀ G₃ x)) ∘ η η₁ (F₀ G₂ (F₀ G₃ x))
            ≈˘⟨ identityʳ ⟩
        (F₁ H₁ (F₁ H₂ (η η₃ x)) ∘ F₁ H₁ (η η₂ (F₀ G₃ x)) ∘ η η₁ (F₀ G₂ (F₀ G₃ x))) ∘ id ∎ }
      }
    ; F⇐G = record
      { η = λ { ((F₁ , F₂) , F₃) → F⇒G (associator F₃ F₂ F₁) }
      -- the proof is as obove, so write it raw combinator-style
      ; commute = λ { {(G₁ , G₂) , G₃} {(H₁ , H₂) , H₃} ((η₁ , η₂) , η₃) {x} →
          let open Category D in let open HomReasoning in
          identityˡ ○ ⟺ assoc ○ ∘-resp-≈ˡ (⟺ (homomorphism H₁)) ○ ⟺ identityʳ}
      }
    ; iso = λ X → record { isoˡ = D.identityˡ ; isoʳ = D.identityʳ }
    }
  ; unitˡ = λ {A} {B} → let module B = Category B in let open B.HomReasoning in record
    { F⇒G = record { η = λ _ → F⇒G unitorˡ ; commute = λ _ → B.identityˡ }
    ; F⇐G = record
      { η = λ _ → F⇐G unitorˡ
      ; commute = λ f → B.identityˡ ○ ⟺ B.identityʳ ○ ⟺ B.identityʳ
      }
    ; iso = λ _ → record { isoˡ = B.identityˡ ; isoʳ = B.identityʳ }
    }
  ; unitʳ = λ {A} {B} → let open Category B in let open HomReasoning in record
    { F⇒G = record
      { η = λ _ → F⇒G unitorʳ
      ; commute = λ { {_} {Y , _} (f , _) {x} → begin
        id ∘ F₁ Y (Category.id A) ∘ η f x ≈⟨ identityˡ ○ ∘-resp-≈ˡ (identity Y) ○ ⟺ id-comm ⟩
        η f x ∘ id                        ∎ }
      }
    ; F⇐G = record
       { η = λ _ → F⇐G unitorʳ
       ; commute = λ { {_} {Y , _} (f , _) {x} → begin
           id ∘ η f x                          ≈˘⟨  identity Y ⟩∘⟨refl ⟩
           F₁ Y (Category.id A) ∘ η f x        ≈˘⟨  identityʳ ⟩
           (F₁ Y (Category.id A) ∘ η f x) ∘ id ∎ }
       }
    ; iso = λ _ → record { isoˡ = identityˡ ; isoʳ = identityʳ }
    }
  }
  where
    open NaturalTransformation
    open NaturalIsomorphism
    open Functor

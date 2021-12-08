{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Properties.Setoids.Exact where

open import Level
open import Categories.Category.Instance.Setoids
open import Categories.Category.Exact
open import Categories.Diagram.Pullback
open import Categories.Diagram.Pullback.Properties
open import Categories.Category.Instance.Properties.Setoids.Limits.Canonical
open import Categories.Object.InternalRelation

open import Categories.Diagram.Coequalizer using (Coequalizer)
open import Categories.Morphism using (_≅_)
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-Cartesian)
open import Data.Product using (∃)
open import Data.Product using (Σ; proj₁; proj₂; _,_; Σ-syntax; _×_; -,_)
open import Relation.Binary using (Setoid; Rel; IsEquivalence)
open import Categories.Category using (Category)
open import Function.Equality as SΠ renaming (id to ⟶-id)

open Setoid renaming (_≈_ to [_][_≈_]; Carrier to ∣_∣) using (isEquivalence)

open Π

module _ ℓ where
  private
    S = Setoids ℓ ℓ
    module S = Category S
    
  open Pullback

  Quotient : ∀ {X : Setoid ℓ ℓ} → (E : Equivalence S X) → Rel ∣ X ∣ ℓ
  Quotient {X} E x₁ x₂ = ∃ λ y₁ → ∃ λ y₂ →
     [ R.dom ][ y₁ ≈ y₂ ] × [ X ][ R.p₁ ⟨$⟩ y₁ ≈ x₁ ] × [ X ][ R.p₂ ⟨$⟩ y₂ ≈ x₂ ]
       where
         open Equivalence E
         open Setoid

  Quotient-Equivalence : ∀ {X : Setoid ℓ ℓ} → (E : Equivalence S X) → IsEquivalence (Quotient E)
  Quotient-Equivalence {X} E = record
     { refl = λ {x} →
          EqSpan.refl eqspan ⟨$⟩ x 
        , EqSpan.refl eqspan ⟨$⟩ x
        , refl R.dom
        , EqSpan.is-refl₁ eqspan (refl X) 
        , EqSpan.is-refl₂ eqspan (refl X) 
     ; sym = λ (y₁ , y₂ , y₁≈y₂ , eq₁ , eq₂) →
          EqSpan.sym eqspan ⟨$⟩ y₁
        , EqSpan.sym eqspan ⟨$⟩ y₂
        , cong (EqSpan.sym eqspan) y₁≈y₂ 
        , trans X (EqSpan.is-sym₁ eqspan y₁≈y₂) eq₂
        , trans X (EqSpan.is-sym₂ eqspan (sym R.dom y₁≈y₂)) eq₁ 
     ; trans = λ { {x₁}{x₂}{x₃} (y₁ , y₂ , y₁≈y₂ , eq₁ , eq₂) (y₃ , y₄ , y₃≈y₄ , eq₃ , eq₄) →
          EqSpan.trans eqspan ⟨$⟩ (f y₁≈y₂ y₃≈y₄ eq₁ eq₂ eq₃ eq₄ ⟨$⟩ y₁′ y₁≈y₂ y₃≈y₄ eq₁ eq₂ eq₃ eq₄)
        , EqSpan.trans eqspan ⟨$⟩ (f y₁≈y₂ y₃≈y₄ eq₁ eq₂ eq₃ eq₄ ⟨$⟩ y₂′ y₁≈y₂ y₃≈y₄ eq₁ eq₂ eq₃ eq₄)
        , cong (EqSpan.trans eqspan SΠ.∘ f y₁≈y₂ y₃≈y₄ eq₁ eq₂ eq₃ eq₄) (y₃≈y₄ , y₁≈y₂)
        , trans X (trans X (EqSpan.is-trans₁ eqspan (refl (P (EqSpan.R×R eqspan)))) (cong R.p₁ (h y₁≈y₂ y₃≈y₄ eq₁ eq₂ eq₃ eq₄))) eq₁
        , trans X (trans X {!!} {!!}) eq₄
       } 
     }
     where
       open Equivalence E
       open Setoid
       open Category S

       module Transitivity {x₁ x₂ x₃ : ∣ X ∣} {y₁ y₂ y₃ y₄ : ∣ R.dom ∣}
         (y₁≈y₂  : [ R.dom ][ y₁ ≈ y₂ ])  (y₃≈y₄ : [ R.dom ][ y₃ ≈ y₄ ])
         (eq₁ : [ X ][ R.p₁ ⟨$⟩ y₁ ≈ x₁ ]) (eq₂ : [ X ][ R.p₂ ⟨$⟩ y₂ ≈ x₂ ])
         (eq₃ : [ X ][ R.p₁ ⟨$⟩ y₃ ≈ x₂ ]) (eq₄ : [ X ][ R.p₂ ⟨$⟩ y₄ ≈ x₃ ]) where

         y₁′ : FiberProduct R.p₁ R.p₂
         y₁′ = record { elem₁ = y₃ ; elem₂ = y₁ ; commute = trans X (trans X eq₃ (sym X eq₂)) (sym X (cong R.p₂ y₁≈y₂)) }

         y₂′ : FiberProduct R.p₁ R.p₂
         y₂′ = record { elem₁ = y₄ ; elem₂ = y₂ ; commute = trans X (cong R.p₁ (sym R.dom y₃≈y₄)) (trans X eq₃ (sym X eq₂))}

         f : P (pullback ℓ ℓ R.p₁ R.p₂) ⇒ P (EqSpan.R×R eqspan)
         f = _≅_.from (up-to-iso S (pullback ℓ ℓ R.p₁ R.p₂) (EqSpan.R×R eqspan))

         h : [ R.dom ][ p₁ (EqSpan.R×R eqspan) ⟨$⟩ (f ⟨$⟩ y₁′) ≈ y₁ ]
         h = {!!} --p₁∘universal≈h₁ {f = R.p₁}{g = R.p₂} {!EqSpan.R×R eqspan!}  -- p₁∘universal≈h₁

         h′ : [ R.dom ][ p₁ (EqSpan.R×R eqspan) ⟨$⟩ (f ⟨$⟩ y₁′) ≈ y₃ ]
         h′ = p₁∘universal≈h₁ {_}{_}{_}{S}{ {!y₁′!}} {!!} {!!} -- (EqSpan.R×R eqspan) (refl R.dom , refl R.dom) 

       open Transitivity
       
  Quotient-Coequalizer : ∀ {X : Setoid ℓ ℓ} (E : Equivalence S X) → Coequalizer S (Equivalence.R.p₁ E) (Equivalence.R.p₂ E)
  Quotient-Coequalizer {X} E = record
    { obj = record
       { Carrier = ∣ X ∣
       ; _≈_ = Quotient E
       ; isEquivalence = Quotient-Equivalence E
       }
    ; arr = record
       { _⟨$⟩_ = λ x → x
       ; cong = λ {x₁}{x₂} eq →
            EqSpan.refl eqspan ⟨$⟩ x₁
          , EqSpan.refl eqspan ⟨$⟩ x₂
          , cong (EqSpan.refl eqspan) eq
          , EqSpan.is-refl₁ eqspan (refl X)
          , EqSpan.is-refl₂ eqspan (refl X)
       }
    ; isCoequalizer = {!!}
    }
      where
        open Equivalence E
        open Setoid

  Setoids-Exact : Exact (Setoids ℓ ℓ)
  Setoids-Exact = record
    { regular = record
        { finitely-complete = record
           { cartesian = Setoids-Cartesian
           ; equalizer = λ _ _ → pullback×cartesian⇒equalizer S (pullback ℓ ℓ) Setoids-Cartesian
           }
        ; coeq-of-kernelpairs = λ f kp → Quotient-Coequalizer record
           { R = record
              { dom = P kp
              ; p₁  = p₁ kp
              ; p₂  = p₂ kp
              ; relation = KP⇒Relation (Setoids ℓ ℓ) f kp (pullback ℓ ℓ (p₁ kp) (p₂ kp))
              } 
           ; eqspan = KP⇒EqSpan (Setoids ℓ ℓ) f kp (pullback ℓ ℓ (p₁ kp) (p₂ kp))
           } 
        ; pullback-of-regularepi-is-regularepi =
            λ { f record { C = C ; h = h ; g = g ; coequalizer = coeq } pb → record
                { h = p₂ (pullback ℓ ℓ h (p₁ pb))
                ; g = {!!} 
                ; coequalizer = {!!}
                }
            }
        }
    ; quotient = Quotient-Coequalizer
    ; effective = λ {X} E → record
        { commute = λ {x₁}{x₂} eq → x₁ , x₂ , eq , refl X , refl X
        ; universal = λ {Y}{h₁}{h₂} eq → record { _⟨$⟩_ = λ x → {!!} ; cong = {!!} }
        ; unique = {!!}
        ; p₁∘universal≈h₁ = {!!}
        ; p₂∘universal≈h₂ = {!!}
        }
    }
      where
        open Equivalence 
        open Setoid

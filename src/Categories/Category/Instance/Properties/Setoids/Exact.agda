{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Properties.Setoids.Exact where

open import Level
open import Categories.Category.Instance.Setoids
open import Categories.Category.Exact
open import Categories.Diagram.Pullback
open import Categories.Diagram.Pullback.Properties
open import Categories.Category.Instance.Properties.Setoids.Limits.Canonical
open import Categories.Object.InternalRelation

open import Categories.Diagram.Coequalizer using (Coequalizer; IsCoequalizer)
open import Categories.Morphism using (_≅_; JointMono; Epi)
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-Cartesian)
open import Data.Product using (∃; proj₁; proj₂; _,_; Σ-syntax; _×_; -,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary using (Setoid; Rel; IsEquivalence)
open import Categories.Category using (Category)
open import Function.Equality as SΠ using (Π; _⇨_) renaming (id to ⟶-id)

open import Data.Fin using (Fin; zero) renaming (suc to nzero)

open Setoid renaming (_≈_ to [_][_≈_]; Carrier to ∣_∣) using (isEquivalence)

open Π

module _ ℓ where
  private
    S = Setoids ℓ ℓ
    open Category S
    
  open Pullback
  open Setoid

  Quotient : ∀ {X : Setoid ℓ ℓ} → (E : Equivalence S X) → Rel ∣ X ∣ ℓ
  Quotient {X} E x₁ x₂ = ∃ λ y → [ X ][ R.p₁ ⟨$⟩ y ≈ x₁ ] × [ X ][ R.p₂ ⟨$⟩ y ≈ x₂ ]
       where open Equivalence E
         
  Quotient-Equivalence : ∀ {X : Setoid ℓ ℓ} → (E : Equivalence S X) → IsEquivalence (Quotient E)
  Quotient-Equivalence {X} E = record
      {
        refl = λ {x} → ES.refl ⟨$⟩ x , ES.is-refl₁ (refl X) , ES.is-refl₂ (refl X)
      ; sym = λ { (x , eq₁ , eq₂) →  ES.sym ⟨$⟩ x , trans X (ES.is-sym₁ (refl R.dom)) eq₂ , trans X (ES.is-sym₂ (refl R.dom)) eq₁}
      ; trans = λ { (r , x≈ , ≈y) (s , y≈ , ≈z) →
         let t = record { elem₁ = s ; elem₂ = r ; commute = trans X y≈ (sym X ≈y) } in
           ES.trans ⟨$⟩ (to-R×R ⟨$⟩ t)
         , trans X (ES.is-trans₁ (refl ES.R×R.dom)) (trans X (cong R.p₁ (p₂-to-R×R t)) x≈)
         , trans X (ES.is-trans₂ (refl ES.R×R.dom)) (trans X (cong R.p₂ (p₁-to-R×R t)) ≈z)
         }
      }
        where
          open Equivalence E
          module ES = EqSpan eqspan 

          to-R×R : P (pullback ℓ ℓ R.p₁ R.p₂) ⇒ P ES.R×R
          to-R×R = _≅_.from (up-to-iso S (pullback ℓ ℓ R.p₁ R.p₂) ES.R×R)

          p₁-to-R×R : (p : FiberProduct R.p₁ R.p₂) → [ R.dom ][ ES.R×R.p₁ ⟨$⟩ (to-R×R ⟨$⟩ p) ≈  FiberProduct.elem₁ p ]
          p₁-to-R×R p = p₁∘universal≈h₁ ES.R×R {eq = λ {x y} → commute (pullback ℓ ℓ R.p₁ R.p₂) {x} {y}} {p} {p} (refl R.dom , refl R.dom)

          p₂-to-R×R : (p : FiberProduct R.p₁ R.p₂) → [ R.dom ][ ES.R×R.p₂ ⟨$⟩ (to-R×R ⟨$⟩ p) ≈  FiberProduct.elem₂ p ]
          p₂-to-R×R p = p₂∘universal≈h₂ ES.R×R {eq = λ {x y} → commute (pullback ℓ ℓ R.p₁ R.p₂) {x} {y}} {p} {p} (refl R.dom , refl R.dom)

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
            ES.refl ⟨$⟩ x₁
          , ES.is-refl₁ (refl X) 
          , trans X (ES.is-refl₂ (refl X)) eq 
       } 
    ; isCoequalizer = record
       { equality = λ {x}{y} x≈y → x , refl X , cong R.p₂ x≈y
       ; coequalize = λ {C}{h} eq → record
           { _⟨$⟩_ = λ x → h ⟨$⟩ x
           ; cong = λ { (r , x≈ , ≈y) → trans C (cong h (sym X x≈)) (trans C (eq (refl R.dom)) (cong h ≈y))}
           }
       ; universal = λ {C}{h} → cong h
       -- TODO : Reformulate with equational reasoning
       ; unique = λ { {C} {h}{i}{eq'} eq (r , x≈ , ≈y) → trans C (trans C (sym C (trans C (cong h x≈) (eq (refl X)))) (eq' (refl R.dom))) (cong h ≈y) }
       }
    }
      where
          open Equivalence E
          module ES = EqSpan eqspan

  -- hm, this must be true, but how to show it?
  Epi-Regular : ∀ {X Y : Setoid ℓ ℓ} (f : X ⇒ Y) → Epi S f → IsCoequalizer S (p₁ (pullback ℓ ℓ f f)) (p₂ (pullback ℓ ℓ f f)) f
  Epi-Regular {X}{Y} f epi = record
      { equality   = λ { {x}{y} (eq₁ , eq₂) → commute (pullback ℓ ℓ f f) {x} {y} (eq₁ , eq₂) }
      ; coequalize = λ x → {!!}
      ; universal  = {!!}
      ; unique     = {!!}
      }
  
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
          -- instead, just use the general fact that all epis are regular
        ; pullback-of-regularepi-is-regularepi =
            λ { {A}{B}{D} f {u} record { C = C ; h = h ; g = g ; coequalizer = coeq } pb → record
                { h = {!!}
                ; g = {!!} -- p₂ (pullback ℓ ℓ h (p₁ pb)) --record { _⟨$⟩_ = λ x → {!!} ; cong = {!!} } 
                ; coequalizer = {!!}
                }
            }
        }
    ; quotient = Quotient-Coequalizer
    ; effective = λ {X} E → record
        { commute = λ {x} eq → x , refl X , cong (Relation.p₂ (R E)) eq 
        ; universal = λ {_}{h} eq → EqSpan.refl (eqspan E) ∘ h
        ; unique = λ {C}{h}{u}{f}{g} eq₁ eq₂ → Relation.relation (R E) f (EqSpan.refl (eqspan E) ∘ h) λ {zero →  trans (C ⇨ X) eq₁ {!!} ; (nzero _) → {!!}}
          --{x}{y} eq → trans (Relation.dom (R E) ) {!!} (cong (EqSpan.refl (eqspan E)) (eq₁ eq)) -- (cong {!f!} eq₁ )
        ; p₁∘universal≈h₁ = λ {_}{h} eq → trans X (EqSpan.is-refl₁ (eqspan E) (refl X)) (cong h eq)
        ; p₂∘universal≈h₂ = λ {_}{h'}{h}{eq'}{x}{y} eq → let a , b , c = eq' eq in {!!} --trans X (EqSpan.is-refl₂ (eqspan E) (refl X)) (trans X (sym X {!b!}) c)
        }
    }
      where
        open Equivalence 
        open Setoid


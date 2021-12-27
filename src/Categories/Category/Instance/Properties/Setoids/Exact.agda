{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Properties.Setoids.Exact where

open import Categories.Category using (Category)
open import Categories.Category.Exact using (Exact)
open import Categories.Category.Instance.Properties.Setoids.Limits.Canonical
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-Cartesian)
open import Categories.Diagram.Coequalizer using (Coequalizer; IsCoequalizer)
open import Categories.Diagram.Pullback using (Pullback; up-to-iso)
open import Categories.Diagram.Pullback.Properties
open import Categories.Morphism using (_≅_; JointMono; Epi)
open import Categories.Morphism.Regular using (RegularEpi)
open import Categories.Object.InternalRelation using (Equivalence; EqSpan; KP⇒Relation; KP⇒EqSpan; module Relation)

open import Level
open import Data.Fin using (Fin; zero) renaming (suc to nzero)
open import Data.Product using (∃; proj₁; proj₂; _,_; Σ-syntax; _×_; -,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using () renaming (id to id→)
open import Function.Equality as SΠ using (Π; _⇨_) renaming (id to ⟶-id)
open import Relation.Binary using (Setoid; Rel; IsEquivalence)
import Relation.Binary.Reasoning.Setoid as SR

open Setoid renaming (_≈_ to [_][_≈_]; Carrier to ∣_∣) using (isEquivalence; refl; sym; trans)
open Π using (_⟨$⟩_; cong)

module _ ℓ where
  private
    S = Setoids ℓ ℓ
    open Category S

  open Pullback using (P; p₁; p₂; p₁∘universal≈h₁; commute; p₂∘universal≈h₂)

  record Quotient {X : Setoid ℓ ℓ} (E : Equivalence S X) (x₁ x₂ : ∣ X ∣) : Set ℓ where
    constructor quot
    open Equivalence E using (module R)
    field
      y     : ∣ R.dom ∣
      py≈x₁ : [ X ][ R.p₁ ⟨$⟩ y ≈ x₁ ]
      py≈x₂ : [ X ][ R.p₂ ⟨$⟩ y ≈ x₂ ]

  Quotient-Equivalence : ∀ {X : Setoid ℓ ℓ} → (E : Equivalence S X) → IsEquivalence (Quotient E)
  Quotient-Equivalence {X} E = record
      {
        refl  = quot _ (ES.is-refl₁ X.refl) (ES.is-refl₂ X.refl)
      ; sym   = λ { (quot r eq₁ eq₂) →  quot (ES.sym ⟨$⟩ r) (X.trans (ES.is-sym₁ D.refl) eq₂) (X.trans (ES.is-sym₂ D.refl) eq₁) }
      ; trans = λ { (quot r x≈ ≈y) (quot s y≈ ≈z) →
         let t = record { elem₁ = s ; elem₂ = r ; commute = X.trans y≈ (X.sym ≈y) } in
           quot
             (ES.trans ⟨$⟩ (to-R×R ⟨$⟩ t))
             (X.trans (ES.is-trans₁ R×R.refl) (X.trans (cong R.p₁ (p₂-to-R×R t)) x≈))
             (X.trans (ES.is-trans₂ R×R.refl) (X.trans (cong R.p₂ (p₁-to-R×R t)) ≈z))
         }
      }
        where
          open Equivalence E
          module ES = EqSpan eqspan
          module X = Setoid X             using (refl; sym; trans)
          module D = Setoid R.dom         using (refl; _≈_)
          module R×R = Setoid ES.R×R.dom  using (refl)
          
          fp : Pullback S R.p₁ R.p₂
          fp = pullback ℓ ℓ R.p₁ R.p₂

          to-R×R : P fp ⇒ P ES.R×R
          to-R×R = _≅_.from (up-to-iso S fp ES.R×R)

          p₁-to-R×R : (p : FiberProduct R.p₁ R.p₂) → ES.R×R.p₁ ⟨$⟩ (to-R×R ⟨$⟩ p) D.≈ FiberProduct.elem₁ p
          p₁-to-R×R p = p₁∘universal≈h₁ ES.R×R {eq = λ {x y} → commute fp {x} {y}} {p} {p} (D.refl , D.refl)

          p₂-to-R×R : (p : FiberProduct R.p₁ R.p₂) → ES.R×R.p₂ ⟨$⟩ (to-R×R ⟨$⟩ p) D.≈ FiberProduct.elem₂ p
          p₂-to-R×R p = p₂∘universal≈h₂ ES.R×R {eq = λ {x y} → commute fp {x} {y}} {p} {p} (D.refl , D.refl)

  Quotient-Setoid : {X : Setoid ℓ ℓ} (E : Equivalence S X) → Setoid ℓ ℓ
  Quotient-Setoid {X} E = record { Carrier = ∣ X ∣ ; _≈_ = Quotient E; isEquivalence = Quotient-Equivalence E }

  Quotient-Coequalizer : {X : Setoid ℓ ℓ} (E : Equivalence S X) → Coequalizer S (Equivalence.R.p₁ E) (Equivalence.R.p₂ E)
  Quotient-Coequalizer {X} E = record
    { obj = X∼
    ; arr = inj
    ; isCoequalizer = record
       { equality = inj-≈
       ; coequalize = λ {_} {h} eq → quotient h eq
       ; universal = λ {_}{h} → cong h
       ; unique = λ {_}{h}{i}{eq′} eq → unique {_}{h}{i}{eq′} eq
       }
    }
    where
      open Equivalence E
      module X = Setoid X
      module ES = EqSpan eqspan
      X∼ : Setoid ℓ ℓ
      X∼ = Quotient-Setoid E
      inj : X ⇒ X∼
      inj = record
       { _⟨$⟩_ = id→
       ; cong = λ {x₁} eq → quot (ES.refl ⟨$⟩ x₁) (ES.is-refl₁ X.refl) (X.trans (ES.is-refl₂ X.refl) eq)
       }
      inj-≈ : inj ∘ R.p₁ ≈ inj ∘ R.p₂
      inj-≈ {x} {y} x≈y = quot x X.refl (cong R.p₂ x≈y)
      -- coEqualizer wants the 'h' to be implicit, but can't figure it out, so make it explicit here
      quotient : {C : Obj} (h : X ⇒ C) → h ∘ R.p₁ ≈ h ∘ R.p₂ → X∼ ⇒ C
      quotient {C} h eq = record
        { _⟨$⟩_ = h ⟨$⟩_
        ; cong = λ { (quot r x≈ ≈y) → trans C (cong h (X.sym x≈)) (trans C (eq (refl R.dom)) (cong h ≈y))}
        }
      unique : {C : Obj} {h : X ⇒ C} {i : X∼ ⇒ C} {eq : h ∘ R.p₁ ≈ h ∘ R.p₂} → h ≈ i ∘ inj → i ≈ quotient h eq
      unique {C} {h} {i} {eq′} eq {x} {y} (quot r x≈ ≈y) = begin
        i ⟨$⟩ x           ≈˘⟨ eq X.refl ⟩
        h ⟨$⟩ x           ≈˘⟨ cong h x≈ ⟩
        h ⟨$⟩ (R.p₁ ⟨$⟩ r) ≈⟨ eq′ (refl R.dom) ⟩
        h ⟨$⟩ (R.p₂ ⟨$⟩ r) ≈⟨ cong h ≈y ⟩
        h ⟨$⟩ y ∎
        where open SR C
{-
  -- hm, this must be true, but how to show it?
  Epi-Regular : ∀ {X Y : Setoid ℓ ℓ} (f : X ⇒ Y) → Epi S f → IsCoequalizer S (p₁ (pullback ℓ ℓ f f)) (p₂ (pullback ℓ ℓ f f)) f
  Epi-Regular {X}{Y} f epi = record
      { equality   = λ { {x}{y} (eq₁ , eq₂) → commute (pullback ℓ ℓ f f) {x} {y} (eq₁ , eq₂) }
      ; coequalize = λ {C} {h} x → record
        { _⟨$⟩_ = λ y → {!!}
        ; cong = {!!}
        }
      ; universal  = {!!}
      ; unique     = {!!}
      }
-}
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
          -- no, that must be harder. Trying to finish the proof below..
        ; pullback-of-regularepi-is-regularepi =
            λ { {A}{B}{D} f {u} record { C = C ; h = h ; g = g ; coequalizer = coeq } pb → record
                { C = record
                    { Carrier = Σ[ x ∈ ∣ C ∣ ]  Σ[ y ∈ ∣ D ∣ ] [ A ][ f ⟨$⟩ (h ⟨$⟩ x) ≈ u ⟨$⟩ y ] × [ A ][ f ⟨$⟩ (g ⟨$⟩ x) ≈ u ⟨$⟩ y ]
                    ; _≈_ = λ (x₁ , y₁ , _) (x₂ , y₂ , _) → [ C ][ x₁ ≈ x₂ ] × [ D ][ y₁ ≈ y₂ ] 
                    ; isEquivalence = record
                        { refl  = refl C , refl D 
                        ; sym   = λ (x₁≈y₁ , x₂≈y₂) → sym C x₁≈y₁ , sym D x₂≈y₂ 
                        ; trans = λ (x₁≈y₁ , x₂≈y₂) (y₁≈z₁ , y₂≈z₂) → trans C x₁≈y₁ y₁≈z₁ , trans D x₂≈y₂ y₂≈z₂
                        }
                    } 
                ; h = record
                    { _⟨$⟩_ = λ { (x , y , fhx≈uy , fgx≈uy) → to-R×R f u pb ⟨$⟩ record { elem₁ = h ⟨$⟩ x ; elem₂ = y ; commute = fhx≈uy }}
                    ; cong = λ { (x≈x′ , y≈y′) → cong (to-R×R f u pb) (cong h x≈x′ , y≈y′) }
                    }
                ; g = record
                    { _⟨$⟩_ = λ { (x , y , fhx≈uy , fgx≈uy) → to-R×R f u pb ⟨$⟩ record { elem₁ = g ⟨$⟩ x ; elem₂ = y ; commute = fgx≈uy }}
                    ; cong = λ { (x≈x′ , y≈y′) → cong (to-R×R f u pb) (cong g x≈x′ , y≈y′) }
                    } 
                ; coequalizer = record
                    { equality   = λ { (fst , snd) → {!!} }
                    ; coequalize = {!!}
                    ; universal  = {!!}
                    ; unique     = {!!}
                    }
                }
            }
        }
    ; quotient = Quotient-Coequalizer
    ; effective = λ {X} E → record
        { commute = λ {x} eq → quot _ (refl X) (cong (Relation.p₂ (R E)) eq)
        ; universal = λ {_}{h} eq → EqSpan.refl (eqspan E) ∘ h
        ; unique = λ {C}{h}{u}{f}{g} eq₁ eq₂ → Relation.relation (R E) f (EqSpan.refl (eqspan E) ∘ h) λ {zero →  trans (C ⇨ X) eq₁ {!!} ; (nzero _) → {!!}}
          --{x}{y} eq → trans (Relation.dom (R E) ) {!!} (cong (EqSpan.refl (eqspan E)) (eq₁ eq)) -- (cong {!f!} eq₁ )
        ; p₁∘universal≈h₁ = λ {_}{h} eq → trans X (EqSpan.is-refl₁ (eqspan E) (refl X)) (cong h eq)
        ; p₂∘universal≈h₂ = λ {_}{h'}{h}{eq'}{x}{y} eq → let (quot _ b c) = eq' eq in {!!} --trans X (EqSpan.is-refl₂ (eqspan E) (refl X)) (trans X (sym X {!b!}) c)
        }
    }
      where
        open Equivalence 
        open Setoid

        to-R×R : {A B C : Setoid ℓ ℓ} (f : A ⇒ B)(u : C ⇒ B) → (pb : Pullback (Setoids ℓ ℓ) f u) → P (pullback ℓ ℓ f u) ⇒ P pb
        to-R×R f u pb = _≅_.from (up-to-iso S (pullback ℓ ℓ f u) pb)

        pb-of-re-is-re : {A B C : Setoid ℓ ℓ} (f : B SΠ.⟶ A) {g : C SΠ.⟶ A} → RegularEpi S f → (p : Pullback S f g) → RegularEpi S (p₂ p)
        pb-of-re-is-re f {g} re p = record
          { C = Quotient-Setoid (record
            { R = record
              { dom = {!!}
              ; p₁ = {!!}
              ; p₂ = {!!}
              ; relation = {!!}
              }
            ; eqspan = {!!}
            })
          ; h = record { _⟨$⟩_ = {!!} ; cong = {!!} }
          ; g = record { _⟨$⟩_ = {!!} ; cong = {!!} }
          ; coequalizer = {!!}
          }

{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Properties.Setoids.Exact where

open import Categories.Category using (Category)
open import Categories.Category.Exact using (Exact)
open import Categories.Category.Instance.Properties.Setoids.Limits.Canonical using (pullback; FiberProduct; mk-×; FP-≈)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-Cartesian)
open import Categories.Category.Regular using (Regular)
open import Categories.Diagram.Coequalizer using (Coequalizer; IsCoequalizer)
open import Categories.Diagram.Coequalizer.Properties
open import Categories.Diagram.KernelPair using (KernelPair)
open import Categories.Diagram.Pullback using (Pullback; up-to-iso)
open import Categories.Diagram.Pullback.Properties
open import Categories.Morphism using (_≅_; Epi)
open import Categories.Morphism.Regular using (RegularEpi)
open import Categories.Object.InternalRelation using (Equivalence; EqSpan; KP⇒Relation; KP⇒EqSpan; KP⇒Equivalence; module Relation; rel)

open import Level
open import Data.Fin using (Fin; zero) renaming (suc to nzero)
open import Data.Product using (∃; proj₁; proj₂; _,_; Σ-syntax; _×_; -,_; map; zip)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool
open import Data.Empty
open import Function using () renaming (id to id→)
open import Function.Equality as SΠ using (Π; _⇨_) renaming (id to ⟶-id; _∘_ to _∘⟶_)
open import Relation.Binary using (Setoid; Rel; IsEquivalence)
import Relation.Binary.Reasoning.Setoid as SR

open import Categories.Diagram.Coequalizer.Properties
open import Data.Unit.Polymorphic.Base
open import Categories.Category.Instance.SingletonSet

open Setoid renaming (_≈_ to [_][_≈_]; Carrier to ∣_∣) using (isEquivalence; refl; sym; trans)
open Π using (_⟨$⟩_; cong)


module _ ℓ where
  private
    S = Setoids ℓ ℓ
    open Category S hiding (_≈_)
    module S = Category S

  open Pullback using (P; p₁; p₂)

  -- the next bits all depend on a Setoid X and an Equivalence E, factor those out
  module _ {X : Setoid ℓ ℓ} (E : Equivalence S X) where
    -- let some things have short names
    open Equivalence E using (R; module R; eqspan)
    module ES = EqSpan eqspan

    private
      module X = Setoid X using (refl; sym; trans; _≈_)
    -- convenient inline versions
    infix 2 ⟺
    infixr 3 _○_
    ⟺ : {x₁ x₂ : ∣ X ∣} → x₁ X.≈ x₂ → x₂ X.≈ x₁
    ⟺ = Setoid.sym X
    _○_ : {x₁ x₂ x₃ : ∣ X ∣} → x₁ X.≈ x₂ → x₂ X.≈ x₃ → x₁ X.≈ x₃
    _○_ = Setoid.trans X

    record Equation (x₁ x₂ : ∣ X ∣) : Set ℓ where
      constructor eqn
      open Setoid X using (_≈_)
      field
        name : ∣ R.dom ∣
        x₁≈  : R.p₁ ⟨$⟩ name ≈ x₁
        ≈x₂  : R.p₂ ⟨$⟩ name ≈ x₂

    open Equation

    -- is re-used below, so make it easier to do so by exposing directly
    quotient-trans : {x₁ x₂ y₁ y₂ : ∣ X ∣} →
      (p : Equation x₁ y₁) → (q : Equation x₂ y₂) →
      [ X ][ x₁ ≈ x₂ ] → [ X ][ y₁ ≈ y₂ ] → [ R.dom ][ name p ≈ name q ]

    quotient-trans {x₁} {x₂} {y₁} {y₂} (eqn eq x₁≈ ≈y₁) (eqn eq′ x₂≈ ≈y₂) x₁≈x₂ y₁≈y₂ =
      R.relation {SingletonSetoid}
      (record { _⟨$⟩_ = λ _ → eq  ; cong = λ _ → refl R.dom})
      (record { _⟨$⟩_ = λ _ → eq′ ; cong = λ _ → refl R.dom})
      (λ { zero      _ → x₁≈ ○ x₁≈x₂ ○ ⟺ x₂≈
         ; (nzero _) _ → ≈y₁ ○ y₁≈y₂ ○ ⟺ ≈y₂}) tt

    Quotient-Equivalence : IsEquivalence Equation
    Quotient-Equivalence = record
        {
          refl  = eqn _ (ES.is-refl₁ X.refl) (ES.is-refl₂ X.refl)
        ; sym   = λ { (eqn r eq₁ eq₂) → eqn (ES.sym ⟨$⟩ r) (ES.is-sym₁ D.refl ○ eq₂) (ES.is-sym₂ D.refl ○ eq₁) }
        ; trans = λ { (eqn r x≈ ≈y) (eqn s y≈ ≈z) →
           let t = record { elem₁ = _ ; elem₂ = _ ; commute = y≈ ○ ⟺ ≈y } in
             eqn
               (ES.trans ∘⟶ P₀⇒P₁ ⟨$⟩ t)
               (ES.is-trans₁ R×R.refl ○ (cong R.p₁ (p₂-≈ {t} {t} (D.refl , D.refl)) ○ x≈))
               (ES.is-trans₂ R×R.refl ○ (cong R.p₂ (p₁-≈ {t} {t} (D.refl , D.refl)) ○ ≈z))
           }
        }
          where
            module D = Setoid R.dom         using (refl)
            module R×R = Setoid ES.R×R.dom  using (refl)

            fp : Pullback S R.p₁ R.p₂
            fp = pullback ℓ ℓ R.p₁ R.p₂
            open IsoPb S fp ES.R×R using (P₀⇒P₁; p₁-≈; p₂-≈)

    Quotient-Setoid : Setoid ℓ ℓ
    Quotient-Setoid = record { Carrier = ∣ X ∣ ; _≈_ = Equation; isEquivalence = Quotient-Equivalence }

    Quotient-Coequalizer : Coequalizer S (Equivalence.R.p₁ E) (Equivalence.R.p₂ E)
    Quotient-Coequalizer = record
      { obj = X∼
      ; arr = inj
      ; isCoequalizer = record
         { equality   = inj-≈
         ; coequalize = λ {_}{h} → quotient h
         ; universal  = λ {_}{h} → cong h
         ; unique     = λ {_}{h}{i}{eq′} → unique {_}{h}{i}{eq′}
         }
      }
      where
        X∼ : Setoid ℓ ℓ
        X∼ = Quotient-Setoid

        inj : X ⇒ X∼
        inj = record
         { _⟨$⟩_ = id→
         ; cong = λ {x₁} eq → eqn (ES.refl ⟨$⟩ x₁) (ES.is-refl₁ X.refl) (ES.is-refl₂ X.refl ○ eq)
         }

        inj-≈ : inj ∘ R.p₁ S.≈ inj ∘ R.p₂
        inj-≈ {x} x≈y = eqn x X.refl (cong R.p₂ x≈y)

        -- coEqualizer wants the 'h' to be implicit, but can't figure it out, so make it explicit here
        quotient : {C : Obj} (h : X ⇒ C) → h ∘ R.p₁ S.≈ h ∘ R.p₂ → X∼ ⇒ C
        quotient {C} h eq = record
          { _⟨$⟩_ = h ⟨$⟩_
          ; cong = λ { (eqn r x≈ ≈y) → trans C (cong h (X.sym x≈)) (trans C (eq (refl R.dom)) (cong h ≈y))}
          }

        unique : {C : Obj} {h : X ⇒ C} {i : X∼ ⇒ C} {eq : h ∘ R.p₁ S.≈ h ∘ R.p₂} → h S.≈ i ∘ inj → i S.≈ quotient h eq
        unique {C} {h} {i} {eq′} eq {x} {y} (eqn r x≈ ≈y) = begin
          i ⟨$⟩ x           ≈˘⟨ eq X.refl ⟩
          h ⟨$⟩ x           ≈˘⟨ cong h x≈ ⟩
          h ⟨$⟩ (R.p₁ ⟨$⟩ r) ≈⟨ eq′ (refl R.dom) ⟩
          h ⟨$⟩ (R.p₂ ⟨$⟩ r) ≈⟨ cong h ≈y ⟩
          h ⟨$⟩ y ∎
          where open SR C
  -- Proposition 1 from "Olov Wilander, Setoids and universes"  
  Epi-Surjective : ∀ {A B : Setoid ℓ ℓ} (f : A ⇒ B) → Epi S f → ((y : ∣ B ∣) → Σ[ x ∈ ∣ A ∣ ] [ B ][ f ⟨$⟩ x ≈ y ])
  Epi-Surjective {A}{B} f epi y = let a , b = g≈h (refl B {y}) in a (λ ()) tt

    where
      π : Bool → Set ℓ
      π false = Lift _ ⊥
      π true  = ⊤

      infix 3 _↔_

      _↔_ : Set ℓ → Set ℓ → Set ℓ
      A ↔ B = (A → B) × (B → A)

      B′ : Setoid ℓ ℓ
      B′ = record
        { Carrier =  Bool × ∣ B ∣
        ; _≈_ = λ { (a , x)  (b , y) → ((π a → Σ[ z ∈ ∣ A ∣ ] [ B ][ f ⟨$⟩ z ≈ x ]) ↔ (π b → Σ[ z ∈ ∣ A ∣ ] [ B ][ f ⟨$⟩ z ≈ y ])) }
        ; isEquivalence = record
            { refl  = (λ p → p) , (λ p → p)
            ; sym   = λ (p , q) → q , p
            ; trans = λ (p , q) (p′ , q′) → (λ x → p′ (p x)) , (λ x → q (q′ x))
            }
        }

      g : B ⇒ B′
      g = record { _⟨$⟩_ = λ x → false , x ; cong = λ _ → (λ _ ()) , (λ _ ()) }

      h : B ⇒ B′
      h = record
          { _⟨$⟩_ = λ x → true , x
          ; cong = λ x≈y →
                (λ eq _ → let (a , eq′) = eq tt in a , trans B eq′ x≈y)
              , (λ eq _ → let (a , eq′) = eq tt in a , (trans B eq′ (sym B x≈y)))
          }

      g≈h : [ B ⇨ B′ ][ g ≈ h ] 
      g≈h = epi g h (λ {x}{y} x≈y → (λ u _ → x , cong f x≈y) , λ _ ())
  Setoids-Regular : Regular (Setoids ℓ ℓ)
  Setoids-Regular = record
    { finitely-complete = record
       { cartesian = Setoids-Cartesian
       ; equalizer = λ _ _ → pullback×cartesian⇒equalizer S (pullback ℓ ℓ) Setoids-Cartesian
       }
    ; coeq-of-kernelpairs = λ f kp → Quotient-Coequalizer record
       { R = KP⇒Relation S f kp
       ; eqspan = KP⇒EqSpan S f kp (pb kp)
       }
    ; pullback-of-regularepi-is-regularepi = pb-of-re-is-re
    }
    where
      pb : ∀ {A B} {f : A ⇒ B} (kp : KernelPair S f) → Pullback S (p₁ kp) (p₂ kp)
      pb kp = pullback ℓ ℓ (p₁ kp) (p₂ kp)
      -- See Prop. 3.5 at https://ncatlab.org/nlab/show/regular+epimorphism ??
      -- instead, just use the general fact that all epis are regular
      -- no, that must be harder. Trying to finish the proof below..
      pb-of-re-is-re : {A B D : Setoid ℓ ℓ} (f : B ⇒ A) {u : D ⇒ A} → RegularEpi S f → (pb : Pullback S f u) → RegularEpi S (p₂ pb)
      pb-of-re-is-re {A}{B}{D} f {u} record { C = C ; h = h ; g = g ; coequalizer = coeq } pb = 
       record
         { C = record
             { Carrier = Σ[ x ∈ ∣ C ∣ ]  Σ[ y ∈ ∣ D ∣ ] [ A ][ f ⟨$⟩ (h ⟨$⟩ x) ≈ u ⟨$⟩ y ] × [ A ][ f ⟨$⟩ (g ⟨$⟩ x) ≈ u ⟨$⟩ y ]
             ; _≈_ = λ (x₁ , y₁ , _) (x₂ , y₂ , _) → [ C ][ x₁ ≈ x₂ ] × [ D ][ y₁ ≈ y₂ ]
             ; isEquivalence = record
                 { refl  = λ { {x , _} → C.refl {x} , D.refl}
                 ; sym   = map C.sym D.sym
                 ; trans = zip C.trans D.trans
                 }
             }
         ; h = record
             { _⟨$⟩_ = λ { (x , y , fhx≈uy , _) → P₀⇒P₁ ⟨$⟩ mk-× (h ⟨$⟩ x) y fhx≈uy }
             ; cong = λ { (x≈x′ , y≈y′) → cong P₀⇒P₁ (cong h x≈x′ , y≈y′) }
             }
         ; g = record
             { _⟨$⟩_ = λ { (x , y , _ , fgx≈uy) → P₀⇒P₁ ⟨$⟩ mk-× (g ⟨$⟩ x) y fgx≈uy }
             ; cong = λ { (x≈x′ , y≈y′) → cong P₀⇒P₁ (cong g x≈x′ , y≈y′) }
             }
         ; coequalizer = record
             { equality   = λ { {x , y , fhx≈uy , fgx≈uy} {x′ , y′ , fhx≈uy′ , fgx≈uy′} (x≈x′ , y≈y′) →
                 let fp-xy  = mk-× {f = f} {u} (h ⟨$⟩ x) y fhx≈uy in
                 let fp-xy′ = mk-× {f = f} {u} (g ⟨$⟩ x′) y′ fgx≈uy′ in
                 begin
                   (p₂ pb ∘ P₀⇒P₁) ⟨$⟩ fp-xy    ≈⟨ p₂-≈ {fp-xy} {fp-xy} (B.refl , D.refl) ⟩
                   p₂ pb-fu ⟨$⟩ fp-xy           ≈⟨ y≈y′ ⟩
                   p₂ pb-fu ⟨$⟩ fp-xy′          ≈⟨ D.sym (p₂-≈ {fp-xy′} {fp-xy′} (B.refl , D.refl)) ⟩
                   (p₂ pb ∘ P₀⇒P₁) ⟨$⟩ mk-× (g ⟨$⟩ x′) y′ fgx≈uy′ ∎
                  }
             ; coequalize = λ {X} {w} eq → record
               { _⟨$⟩_ = λ d → let (b , eq′) = Epi-Surjective f (Coequalizer⇒Epi S (record { arr = f ; isCoequalizer = coeq })) (u ⟨$⟩ d) in
                 w ⟨$⟩ (P₀⇒P₁ ⟨$⟩ mk-× b d eq′)
               ; cong = λ x≈y → {!!}
               }
             ; universal  = λ {S} {pb⟶S} {eq} {x} {y} x≈y → {!!}
             ; unique     = {!!}
             }
         }
         where
           
           module B = Setoid B
           module C = Setoid C
           module D = Setoid D
           open SR D

           pb-fu : Pullback S f u
           pb-fu = pullback ℓ ℓ f u

           open IsoPb S pb-fu pb 

  Setoids-Exact : Exact (Setoids ℓ ℓ)
  Setoids-Exact = record
    { regular   = Setoids-Regular
    ; quotient  = Quotient-Coequalizer
    ; effective = λ {X} E → record
        { commute   = λ eq → eqn _ (refl X) (cong (Relation.p₂ (R E)) eq)
        ; universal = λ { {Z}{h₁}{h₂} → universal E h₁ h₂ }
        ; unique    = λ {Z}{h₁}{h₂}{u}{eq} eq₁ eq₂ {x}{y} → Relation.relation (R E) u (universal E h₁ h₂ eq)
            λ { zero {x}{y} eq′      → trans X (eq₁ eq′) (sym X (p₁∘universal≈h₁ E h₁ h₂ eq (refl Z)))
              ; (nzero _) {x}{y} eq′ → trans X (eq₂ eq′) (sym X (p₂∘universal≈h₂ E h₁ h₂ eq (refl Z)))
              }
        ; p₁∘universal≈h₁ = λ {Z}{h₁}{h₂}{eq} → p₁∘universal≈h₁ E h₁ h₂ eq
        ; p₂∘universal≈h₂ = λ {Z}{h₁}{h₂}{eq} → p₂∘universal≈h₂ E h₁ h₂ eq
        }
    }
      where
        open Equivalence
        open Setoid
        open Coequalizer using (arr)

        universal : {X Z : Setoid ℓ ℓ} → (E : Equivalence S X) → (h₁ h₂ : Z ⇒ X) →
          (eq : [ Z ⇨ Quotient-Setoid E ][ arr (Quotient-Coequalizer E) ∘ h₁ ≈ arr (Quotient-Coequalizer E) ∘ h₂ ]) →
          Z ⇒ Relation.dom (R E)
        universal {X}{Z} E h₁ h₂ eq = record
          { _⟨$⟩_ = λ z → let (eqn eq _ _) = eq {z}{z} (refl Z) in eq
          ; cong = λ {z}{z′} z≈z′ → quotient-trans E (eq {z}{z} (refl Z)) (eq {z′}{z′} (refl Z)) (cong h₁ z≈z′) (cong h₂ z≈z′)
          }
        p₁∘universal≈h₁ : {X Z : Setoid ℓ ℓ} → (E : Equivalence S X) → (h₁ h₂ : Z ⇒ X) →
          (eq : [ Z ⇨ Quotient-Setoid E ][ arr (Quotient-Coequalizer E) ∘ h₁ ≈ arr (Quotient-Coequalizer E) ∘ h₂ ]) →
          [ Z ⇨ X ][ Relation.p₁ (R E) ∘ (universal E h₁ h₂ eq) ≈ h₁ ]
        p₁∘universal≈h₁ {X}{Z} _ h₁ h₂ eq x≈y = let (eqn _ p₁z≈ _) = eq (refl Z) in trans X p₁z≈ (cong h₁ x≈y)

        p₂∘universal≈h₂ : {X Z : Setoid ℓ ℓ} → (E : Equivalence S X) → (h₁ h₂ : Z ⇒ X) →
          (eq : [ Z ⇨ Quotient-Setoid E ][ arr (Quotient-Coequalizer E) ∘ h₁ ≈ arr (Quotient-Coequalizer E) ∘ h₂ ]) →
          [ Z ⇨ X ][ Relation.p₂ (R E) ∘ (universal E h₁ h₂ eq) ≈ h₂ ]
        p₂∘universal≈h₂ {X}{Z} _ h₁ h₂ eq x≈y = let (eqn _ _ p₂z≈) = eq (refl Z) in trans X p₂z≈ (cong h₂ x≈y)


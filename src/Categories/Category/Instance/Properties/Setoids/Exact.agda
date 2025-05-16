{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Properties.Setoids.Exact where

open import Data.Bool.Base using (Bool; true; false; T)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Fin using (Fin; zero) renaming (suc to nzero)
open import Data.Product using (∃; proj₁; proj₂; _,_; Σ-syntax; _×_; -,_; map; zip; swap; map₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Function using (flip) renaming (id to id→; _∘′_ to _∘→_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Function.Construct.Identity using () renaming (function to ⟶-id)
open import Function.Construct.Composition using (function)
open import Function.Construct.Setoid using () renaming (setoid to _⇨_)
open import Function.Definitions using (StrictlySurjective)
open import Level using (Level)
open import Relation.Binary using (Setoid; Rel; IsEquivalence)
import Relation.Binary.Reasoning.Setoid as SR

open import Categories.Category using (Category)
open import Categories.Category.Exact using (Exact)
open import Categories.Category.Instance.Properties.Setoids.Limits.Canonical using (pullback; FiberProduct; mk-×; FP-≈)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Instance.SingletonSet using (SingletonSetoid)
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-Cartesian)
open import Categories.Category.Regular using (Regular)
open import Categories.Diagram.Coequalizer using (Coequalizer; IsCoequalizer; Coequalizer⇒Epi)
open import Categories.Diagram.Coequalizer.Properties
open import Categories.Diagram.KernelPair using (KernelPair)
open import Categories.Diagram.Pullback using (Pullback; up-to-iso)
open import Categories.Diagram.Pullback.Properties
open import Categories.Morphism using (_≅_; Epi)
open import Categories.Morphism.Regular using (RegularEpi)
open import Categories.Object.InternalRelation using (Equivalence; EqSpan; KP⇒Relation; KP⇒EqSpan; KP⇒Equivalence; module Relation; rel)

open Setoid renaming (_≈_ to [_][_≈_]; Carrier to ∣_∣) using (isEquivalence; refl; sym; trans)
open Func

module _ ℓ where
  private
    S = Setoids ℓ ℓ
    open Category S hiding (_≈_)
    module S = Category S

    infixr 9 _∙_
    _∙_ : {a₁ a₂ b₁ b₂ c₁ c₂ : Level} {A : Setoid a₁ a₂} {B : Setoid b₁ b₂}
      {C : Setoid c₁ c₂} → Func B C → Func A B → Func A C
    f ∙ g = function g f

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
      (record { to = λ _ → eq  ; cong = λ _ → refl R.dom})
      (record { to = λ _ → eq′ ; cong = λ _ → refl R.dom})
      (λ { zero      → x₁≈ ○ x₁≈x₂ ○ ⟺ x₂≈
         ; (nzero _) → ≈y₁ ○ y₁≈y₂ ○ ⟺ ≈y₂})

    Quotient-Equivalence : IsEquivalence Equation
    Quotient-Equivalence = record
        {
          refl  = eqn _ (ES.is-refl₁) (ES.is-refl₂)
        ; sym   = λ { (eqn r eq₁ eq₂) → eqn (ES.sym ⟨$⟩ r) (ES.is-sym₁ ○ eq₂) (ES.is-sym₂ ○ eq₁) }
        ; trans = λ { (eqn r x≈ ≈y) (eqn s y≈ ≈z) →
           let t = record { elem₁ = _ ; elem₂ = _ ; commute = y≈ ○ ⟺ ≈y } in
             eqn
               (ES.trans ∙ P₀⇒P₁ ⟨$⟩ t)
               (ES.is-trans₁ ○ (cong R.p₁ (p₂-≈ {t}) ○ x≈))
               (ES.is-trans₂ ○ (cong R.p₂ (p₁-≈ {t}) ○ ≈z))
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
         ; universal  = λ {C} → Setoid.refl C
         ; unique     = λ {_}{h}{i}{eq′} → unique {_}{h}{i}{eq′}
         }
      }
      where
        X∼ : Setoid ℓ ℓ
        X∼ = Quotient-Setoid

        inj : X ⇒ X∼
        inj = record
         { to = id→
         ; cong = λ {x₁} eq → eqn (ES.refl ⟨$⟩ x₁) ES.is-refl₁ (ES.is-refl₂ ○ eq)
         }

        inj-≈ : inj ∘ R.p₁ S.≈ inj ∘ R.p₂
        inj-≈ {x} = eqn x X.refl X.refl

        -- coEqualizer wants the 'h' to be implicit, but can't figure it out, so make it explicit here
        quotient : {C : Obj} (h : X ⇒ C) → h ∘ R.p₁ S.≈ h ∘ R.p₂ → X∼ ⇒ C
        quotient {C} h eq = record
          { to = h ⟨$⟩_
          ; cong = λ { (eqn r x≈ ≈y) → trans C (cong h (X.sym x≈)) (trans C eq (cong h ≈y))}
          }

        unique : {C : Obj} {h : X ⇒ C} {i : X∼ ⇒ C} {eq : h ∘ R.p₁ S.≈ h ∘ R.p₂} → h S.≈ i ∘ inj → i S.≈ quotient h eq
        unique {C} eq {x} = sym C (eq {x})

  -- Setoid (strict) Surjectivity
  SSurj : {A B : Setoid ℓ ℓ} (f : A ⇒ B) → Set ℓ
  SSurj {A} {B} f = StrictlySurjective (Setoid._≈_ B) (f ⟨$⟩_)

  -- Proposition 1 from "Olov Wilander, Setoids and universes"
  Epi⇒Surjective : ∀ {A B : Setoid ℓ ℓ} (f : A ⇒ B) → Epi S f → SSurj f
  Epi⇒Surjective {A} {B} f epi y = g≈h .proj₁ (λ ()) _
    where
      infix 3 _↔_

      _↔_ : Set ℓ → Set ℓ → Set ℓ
      A ↔ B = (A → B) × (B → A)

      B′ : Setoid ℓ ℓ
      B′ = record
        { Carrier =  Bool × ∣ B ∣
        ; _≈_ = λ { (a , x)  (b , y) → ((T a → Σ[ z ∈ ∣ A ∣ ] [ B ][ f ⟨$⟩ z ≈ x ]) ↔ (T b → Σ[ z ∈ ∣ A ∣ ] [ B ][ f ⟨$⟩ z ≈ y ])) }
        ; isEquivalence = record
            { refl  = id→ , id→
            ; sym   = swap
            ; trans = zip (flip _∘→_) _∘→_
            }
        }

      g : B ⇒ B′
      g = record { to = λ x → false , x ; cong = λ _ → (λ _ ()) , (λ _ ()) }

      h : B ⇒ B′
      h = record
          { to = true ,_
          ; cong = λ x≈y →
                (λ eq _ → map₂ (λ z → trans B z x≈y) (eq _))
              , (λ eq _ → let (a , eq′) = eq _ in a , (trans B eq′ (sym B x≈y)))
          }

      g≈h : [ B ⇨ B′ ][ g ≈ h ]
      g≈h = epi g h λ {x} → (λ _ u → x , Setoid.refl B) , λ _ ()

  -- not needed for exactness, but worthwhile
  Surjective⇒RegularEpi : ∀ {A B : Setoid ℓ ℓ} (f : A ⇒ B) → ((y : ∣ B ∣) → Σ[ x ∈ ∣ A ∣ ] [ B ][ f ⟨$⟩ x ≈ y ]) → RegularEpi S f
  Surjective⇒RegularEpi {A}{B} f surj = record
    { h = p₁ kp
    ; g = p₂ kp
    ; coequalizer = record
        { equality   = λ {x} → commute kp {x}
        ; coequalize = λ {_} {h} → Coeq.coeq {h = h}
        ; universal = λ {C} {h} {eq} → Coeq.universal′ {C} {h} (λ {x} → eq {x})
        ; unique = λ {_}{h}{i}{eq} h≈i∘f → Coeq.unique″ {_} {h} (λ {x} → eq {x}) {i} h≈i∘f
        }
    }
    where
      kp = pullback ℓ ℓ f f
      open Pullback
      module Coeq {C : S.Obj} {h : A S.⇒ C} where
        open SR C
        f⁻¹∘h : ∣ B ∣ → ∣ C ∣
        f⁻¹∘h b = h ⟨$⟩ proj₁ (surj b)
        module _ (h∘p₁≈h∘p₂ : h S.∘ p₁ kp S.≈ h S.∘ p₂ kp) where
          cong′ : {i j : ∣ B ∣} → [ B ][ i ≈ j ] → [ C ][ h ⟨$⟩ proj₁ (surj i) ≈ h ⟨$⟩ proj₁ (surj j) ]
          cong′ {y₁}{y₂} y₁≈y₂ = h∘p₁≈h∘p₂ {pt₁}
            where
              x₁ x₂ : ∣ A ∣
              x₁ = surj y₁ .proj₁
              x₂ = surj y₂ .proj₁
              eq₁ : [ B ][ f ⟨$⟩ x₁ ≈ y₁ ]
              eq₁ = surj y₁ .proj₂
              eq₂ : [ B ][ f ⟨$⟩ x₂ ≈ y₂ ]
              eq₂ = surj y₂ .proj₂
              pt₁ : FiberProduct f f
              pt₁ = mk-× x₁ x₂ (trans B eq₁ (trans B y₁≈y₂ (sym B eq₂)))
          coeq : B S.⇒ C
          coeq = record { to = f⁻¹∘h ; cong = cong′ }
          universal′ : h S.≈ coeq S.∘ f
          universal′ {x} = begin
            h ⟨$⟩ x                     ≈⟨ h∘p₁≈h∘p₂ {mk-× x x₁ (sym B eq₁)} ⟩
            h ⟨$⟩ proj₁ (surj (f ⟨$⟩ x)) ≡⟨⟩ -- by definition of f⁻¹∘h
            f⁻¹∘h (f ⟨$⟩ x)             ≡⟨⟩ -- by definition of coeq
            coeq S.∘ f ⟨$⟩ x            ∎
            where
              x₁ : ∣ A ∣
              x₁ = surj (f ⟨$⟩ x) .proj₁
              eq₁ : [ B ][ f ⟨$⟩ x₁ ≈ f ⟨$⟩ x ]
              eq₁ = surj (f ⟨$⟩ x) .proj₂
          unique″ : {i : B S.⇒ C} → h S.≈ i S.∘ f → i S.≈ coeq
          unique″ {i} h≈i∘f {y} = begin
            i ⟨$⟩ y              ≈⟨ cong i (sym B eq₁) ⟩
            i ∘ f ⟨$⟩ x₁         ≈⟨ sym C h≈i∘f ⟩
            h ⟨$⟩ x₁             ≡⟨⟩ -- by definition of f⁻¹∘h
            f⁻¹∘h y             ∎
            where
              x₁ : ∣ A ∣
              x₁ = surj y .proj₁
              eq₁ : [ B ][ f ⟨$⟩ x₁ ≈ y ]
              eq₁ = surj y .proj₂

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

      pb-of-re-is-re : {A B D : Setoid ℓ ℓ} (f : B ⇒ A) {u : D ⇒ A} →
        RegularEpi S f → (pb : Pullback S f u) → RegularEpi S (p₂ pb)
      pb-of-re-is-re {A}{B}{D} f {u} record { C = C ; h = _ ; g = _ ; coequalizer = coeq } pb =
        Surjective⇒RegularEpi (p₂ pb) λ y →
          let (x , eq) = Epi⇒Surjective f (Coequalizer⇒Epi S record { arr = f ; isCoequalizer = coeq }) (u ⟨$⟩ y) in
          let pt = mk-× x y eq in
          P₀⇒P₁ ⟨$⟩ pt , p₂-≈ {pt}
         where

           pb-fu : Pullback S f u
           pb-fu = pullback ℓ ℓ f u
           pb-ff : Pullback S f f
           pb-ff = pullback ℓ ℓ f f
           module B = Setoid B
           module C = Setoid C
           module D = Setoid D
           open IsoPb S pb-fu pb

  Setoids-Exact : Exact (Setoids ℓ ℓ)
  Setoids-Exact = record
    { regular   = Setoids-Regular
    ; quotient  = Quotient-Coequalizer
    ; effective = λ {X} E → record
        { commute         = eqn _ (refl X) (refl X)
        ; universal       = λ {Z} {h₁} {h₂} → universal E h₁ h₂
        ; p₁∘universal≈h₁ = λ { {eq = eq} → x₁≈ eq }
        ; p₂∘universal≈h₂ = λ { {eq = eq} → ≈x₂ eq }
        ; unique-diagram  = λ {Z} {h₁} {h₂} eq₁ eq₂ → Relation.relation (R E) h₁ h₂
            λ { zero      → eq₁
              ; (nzero _) → eq₂
              }
        }
    }
      where
        open Equivalence
        open Setoid
        open Coequalizer using (arr)
        open Equation

        universal : {X Z : Setoid ℓ ℓ} → (E : Equivalence S X) → (h₁ h₂ : Z ⇒ X) →
          (eq : [ Z ⇨ Quotient-Setoid E ][ arr (Quotient-Coequalizer E) ∘ h₁ ≈ arr (Quotient-Coequalizer E) ∘ h₂ ]) →
          Z ⇒ Relation.dom (R E)
        universal E h₁ h₂ eq = record
          { to = λ _ → name eq
          ; cong = λ {z}{z′} z≈z′ → quotient-trans E (eq {z}) (eq {z′}) (cong h₁ z≈z′) (cong h₂ z≈z′)
          }

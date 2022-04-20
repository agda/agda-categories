{-# OPTIONS --without-K --safe #-}
module Categories.Double.Core where

open import Level

open import Relation.Binary using (Rel; IsEquivalence; Setoid; REL)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as SetoidR

import Categories.Category.Unbundled as Cat

-- Equality of squares in a double category
module _ {o ℓ ℓ' e e' : Level} {Obj : Set o} 
         (Hor : Cat.Category Obj ℓ e) (Ver : Cat.Category Obj ℓ' e') where
  private
    module H = Cat.Category Hor
    module V = Cat.Category Ver
    _≈ₕ_ : ∀ {A B} → Rel (A H.⇒ B) e
    _≈ₕ_ = H._≈_
    _≈ᵥ_ : ∀ {A B} → Rel (A V.⇒ B) e'
    _≈ᵥ_ = V._≈_
  record SqEquality
    {T₁ T₂ B₁ B₂ : Obj}
    (hT₁ hT₂ : T₁ H.⇒ T₂)
    (hB₁ hB₂ : B₁ H.⇒ B₂)
    (vL₁ vL₂ : T₁ V.⇒ B₁)
    (vR₁ vR₂ : T₂ V.⇒ B₂) : Set (e ⊔ e') where
      field
        horT≈ : hT₁ ≈ₕ hT₂
        horB≈ : hB₁ ≈ₕ hB₂
        verL≈ : vL₁ ≈ᵥ vL₂
        verR≈ : vR₁ ≈ᵥ vR₂

module _ {o ℓ ℓ' e e' : Level} {Obj : Set o} 
         (Hor : Cat.Category Obj ℓ e) (Ver : Cat.Category Obj ℓ' e') where
  private
    module H = Cat.Category Hor
    module V = Cat.Category Ver
  dual≈ :
    ∀ {T₁ T₂ B₁ B₂ : Obj} →
    {hT₁ hT₂ : T₁ H.⇒ T₂} →
    {hB₁ hB₂ : B₁ H.⇒ B₂} →
    {vL₁ vL₂ : T₁ V.⇒ B₁} →
    {vR₁ vR₂ : T₂ V.⇒ B₂} →
    SqEquality Hor Ver hT₁ hT₂ hB₁ hB₂ vL₁ vL₂ vR₁ vR₂ →
    SqEquality Ver Hor vL₁ vL₂ vR₁ vR₂ hT₁ hT₂ hB₁ hB₂
  dual≈ S = record
      { horT≈ = S.verL≈
      ; horB≈ = S.verR≈
      ; verL≈ = S.horT≈
      ; verR≈ = S.horB≈
      }
    where module S = SqEquality S

-- Basic definition of a |Double Category|
record Category (o ℓ ℓ' e e' : Level) : Set (suc (o ⊔ ℓ ⊔ e ⊔ ℓ' ⊔ e')) where
  field
    Obj : Set o
    Hor : Cat.Category Obj ℓ e
    Ver : Cat.Category Obj ℓ e
  private
    module H = Cat.Category Hor
    module V = Cat.Category Ver
  _⇒ₕ_ : Rel Obj ℓ
  _⇒ₕ_ = H._⇒_
  _≈ₕ_ : ∀ {A B} → Rel (A ⇒ₕ B) e
  _≈ₕ_ = H._≈_
  _⇒ᵥ_ : Rel Obj ℓ
  _⇒ᵥ_ = V._⇒_
  _≈ᵥ_ : ∀ {A B} → Rel (A ⇒ᵥ B) e
  _≈ᵥ_ = V._≈_
  _∘₁ₕ_ : ∀ {A B C} → (B ⇒ₕ C) → (A ⇒ₕ B) → (A ⇒ₕ C)
  _∘₁ₕ_ = H._∘_
  _∘₁ᵥ_ : ∀ {A B C} → (B ⇒ᵥ C) → (A ⇒ᵥ B) → (A ⇒ᵥ C)
  _∘₁ᵥ_ = V._∘_

  field
    Sq₂ : {T₁ T₂ B₁ B₂ : Obj} → T₁ ⇒ₕ T₂ → B₁ ⇒ₕ B₂ → T₁ ⇒ᵥ B₁ → T₂ ⇒ᵥ B₂ → Set ℓ

  Sq≈ : ∀ {T₁ T₂ B₁ B₂ : Obj}
    {hT₁ hT₂ : T₁ ⇒ₕ T₂} →
    {hB₁ hB₂ : B₁ ⇒ₕ B₂} →
    {vL₁ vL₂ : T₁ ⇒ᵥ B₁} →
    {vR₁ vR₂ : T₂ ⇒ᵥ B₂} →
    REL (Sq₂ hT₁ hB₁ vL₁ vR₁) (Sq₂ hT₂ hB₂ vL₂ vR₂) e
  Sq≈ {_} {_} {_} {_} {hT₁} {hT₂} {hB₁} {hB₂} {vL₁} {vL₂} {vR₁} {vR₂} _ _ =
    SqEquality Hor Ver hT₁ hT₂ hB₁ hB₂ vL₁ vL₂ vR₁ vR₂

  field
{-
horizontal 2-composition:

        T₂  →  T₃      T₁  →  T₂     T₁ → T₃
        ↓   s₂  ↓   ∘₂ₕ  ↓   s₁  ↓  ~>  ↓     ↓
        B₁  →  B₂      B₁  →  B₂     B₁ → B₃
-}
    _∘₂ₕ_ : 
      {T₁ T₂ T₃ B₁ B₂ B₃ : Obj} →
      {hT₁ : T₁ ⇒ₕ T₂} {hT₂ : T₂ ⇒ₕ T₃} →
      {hB₁ : B₁ ⇒ₕ B₂} {hB₂ : B₂ ⇒ₕ B₃} →
      {v₁  : T₁ ⇒ᵥ B₁} {v₂  : T₂ ⇒ᵥ B₂} {v₃  : T₃ ⇒ᵥ B₃} →
      Sq₂ hT₂ hB₂ v₂ v₃ →
      Sq₂ hT₁ hB₁ v₁ v₂ →
      Sq₂ (hT₂ ∘₁ₕ hT₁) (hB₂ ∘₁ₕ hB₁) v₁ v₃

{-
horizontal 2-identity

        V₁  →  V₁
      v ↓   id  ↓ v
        V₂  →  V₂
-}
    id₂ₕ : {V₁ V₂ : Obj} →
      (v : V₁ ⇒ᵥ V₂) →
      Sq₂ H.id H.id v v

{-
vertical 2-composition

        M₁  →  M₁
        ↓   s₂  ↓
        B₁  →  B₂      T₁ → T₂
           ∘₂ᵥ       ~>  ↓    ↓
        T₁  →  T₁      B₁ → B₂
        ↓   s₁  ↓
        M₁  →  M₂

-}
    _∘₂ᵥ_ :
      {T₁ T₂ M₁ M₂ B₁ B₂ : Obj} →
      {hT : T₁ ⇒ₕ T₂} {hM : M₁ ⇒ₕ M₂}{hB : B₁ ⇒ₕ B₂} →
      {vL₁ : T₁ ⇒ᵥ M₁} {vL₂ : M₁ ⇒ᵥ B₁} →
      {vR₁ : T₂ ⇒ᵥ M₂} {vR₂ : M₂ ⇒ᵥ B₂} →
      Sq₂ hM hB vL₂ vR₂ →
      Sq₂ hT hM vL₁ vR₁ →
      Sq₂ hT hB (vL₂ ∘₁ᵥ vL₁) (vR₂ ∘₁ᵥ vR₁)

{-
vertical 2-identity

             h
         H₁  →  H₂
         ↓   id  ↓
         H₁  →  H₂
             h
-}
    id₂ᵥ : {H₁ H₂ : Obj}
      (h : H₁ ⇒ₕ H₂) →
      Sq₂ h h V.id V.id

  field
    identity₂ₕʳ :
      {T₁ T₂ B₁ B₂ : Obj} →
      {hT : T₁ ⇒ₕ T₂} {hB : B₁ ⇒ₕ B₂} →
      {vL : T₁ ⇒ᵥ B₁} {vR : T₂ ⇒ᵥ B₂} →
      (sq : Sq₂ hT hB vL vR) →
      Sq≈ (id₂ₕ vR ∘₂ₕ sq) sq

    identity₂ₕˡ :
      {T₁ T₂ B₁ B₂ : Obj} →
      {hT : T₁ ⇒ₕ T₂} {hB : B₁ ⇒ₕ B₂} →
      {vL : T₁ ⇒ᵥ B₁} {vR : T₂ ⇒ᵥ B₂} →
      (sq : Sq₂ hT hB vL vR) →
      Sq≈ (sq ∘₂ₕ (id₂ₕ vL)) sq

    identity₂ᵥʳ :
      {T₁ T₂ B₁ B₂ : Obj} →
      {hT : T₁ ⇒ₕ T₂} {hB : B₁ ⇒ₕ B₂} →
      {vL : T₁ ⇒ᵥ B₁} {vR : T₂ ⇒ᵥ B₂} →
      (sq : Sq₂ hT hB vL vR) →
      Sq≈ ((id₂ᵥ hB) ∘₂ᵥ sq) sq

    identity₂ᵥˡ :
      {T₁ T₂ B₁ B₂ : Obj} →
      {hT : T₁ ⇒ₕ T₂} {hB : B₁ ⇒ₕ B₂} →
      {vL : T₁ ⇒ᵥ B₁} {vR : T₂ ⇒ᵥ B₂} →
      (sq : Sq₂ hT hB vL vR) →
      Sq≈ (sq ∘₂ᵥ (id₂ᵥ hT)) sq

    identity₂ₕ² : ∀ {V₁ V₂} {v : V₁ ⇒ᵥ V₂} → Sq≈ (id₂ₕ v ∘₂ₕ id₂ₕ v) (id₂ₕ v)
    identity₂ᵥ² : ∀ {H₁ H₂} {h : H₁ ⇒ₕ H₂} → Sq≈ (id₂ᵥ h ∘₂ᵥ id₂ᵥ h) (id₂ᵥ h)

{-
horizontal 2-associativity:

        T₁  →  T₂  →  T₃  →  T₄
        ↓   s₁  ↓   s₂  ↓   s₃  ↓
        B₁  →  B₂  →  B₃  →  B₄
-}
    assocₕ :
      {T₁ T₂ T₃ T₄ B₁ B₂ B₃ B₄ : Obj} →
      {hT₁ : T₁ ⇒ₕ T₂} {hT₂ : T₂ ⇒ₕ T₃} {hT₃ : T₃ ⇒ₕ T₄} →
      {hB₁ : B₁ ⇒ₕ B₂} {hB₂ : B₂ ⇒ₕ B₃} {hB₃ : B₃ ⇒ₕ B₄} →
      {v₁  : T₁ ⇒ᵥ B₁} {v₂  : T₂ ⇒ᵥ B₂} {v₃  : T₃ ⇒ᵥ B₃} {v₄ : T₄ ⇒ᵥ B₄} →
      (s₃ : Sq₂ hT₃ hB₃ v₃ v₄) →
      (s₂ : Sq₂ hT₂ hB₂ v₂ v₃) →
      (s₁ : Sq₂ hT₁ hB₁ v₁ v₂) →
      Sq≈ ((s₃ ∘₂ₕ s₂) ∘₂ₕ s₁) (s₃ ∘₂ₕ (s₂ ∘₂ₕ s₁))

    sym-assocₕ :
      {T₁ T₂ T₃ T₄ B₁ B₂ B₃ B₄ : Obj} →
      {hT₁ : T₁ ⇒ₕ T₂} {hT₂ : T₂ ⇒ₕ T₃} {hT₃ : T₃ ⇒ₕ T₄} →
      {hB₁ : B₁ ⇒ₕ B₂} {hB₂ : B₂ ⇒ₕ B₃} {hB₃ : B₃ ⇒ₕ B₄} →
      {v₁  : T₁ ⇒ᵥ B₁} {v₂  : T₂ ⇒ᵥ B₂} {v₃  : T₃ ⇒ᵥ B₃} {v₄ : T₄ ⇒ᵥ B₄} →
      (s₃ : Sq₂ hT₃ hB₃ v₃ v₄) →
      (s₂ : Sq₂ hT₂ hB₂ v₂ v₃) →
      (s₁ : Sq₂ hT₁ hB₁ v₁ v₂) →
      Sq≈ (s₃ ∘₂ₕ (s₂ ∘₂ₕ s₁)) ((s₃ ∘₂ₕ s₂) ∘₂ₕ s₁)

{-
vertical 2-associativity:

        T₁  →  T₂
        ↓   s₁  ↓
        T₃  →  T₄
        ↓   s₂  ↓
        B₁  →  B₂
        ↓   s₃  ↓
        B₃  →  B₄

-}
    assocᵥ :
      {T₁ T₂ T₃ T₄ B₁ B₂ B₃ B₄ : Obj} →
      {hT₁ : T₁ ⇒ₕ T₂} {hT₂ : T₃ ⇒ₕ T₄}
      {hB₁ : B₁ ⇒ₕ B₂} {hB₂ : B₃ ⇒ₕ B₄}
      {vL₁  : T₁ ⇒ᵥ T₃} {vL₂  : T₃ ⇒ᵥ B₁} {vL₃  : B₁ ⇒ᵥ B₃} →
      {vR₁  : T₂ ⇒ᵥ T₄} {vR₂  : T₄ ⇒ᵥ B₂} {vR₃  : B₂ ⇒ᵥ B₄} →
      (s₃ : Sq₂ hB₁ hB₂ vL₃ vR₃) →
      (s₂ : Sq₂ hT₂ hB₁ vL₂ vR₂) →
      (s₁ : Sq₂ hT₁ hT₂ vL₁ vR₁) →
      Sq≈ ((s₃ ∘₂ᵥ s₂) ∘₂ᵥ s₁) (s₃ ∘₂ᵥ (s₂ ∘₂ᵥ s₁))

    sym-assocᵥ :
      {T₁ T₂ T₃ T₄ B₁ B₂ B₃ B₄ : Obj} →
      {hT₁ : T₁ ⇒ₕ T₂} {hT₂ : T₃ ⇒ₕ T₄}
      {hB₁ : B₁ ⇒ₕ B₂} {hB₂ : B₃ ⇒ₕ B₄}
      {vL₁  : T₁ ⇒ᵥ T₃} {vL₂  : T₃ ⇒ᵥ B₁} {vL₃  : B₁ ⇒ᵥ B₃} →
      {vR₁  : T₂ ⇒ᵥ T₄} {vR₂  : T₄ ⇒ᵥ B₂} {vR₃  : B₂ ⇒ᵥ B₄} →
      (s₃ : Sq₂ hB₁ hB₂ vL₃ vR₃) →
      (s₂ : Sq₂ hT₂ hB₁ vL₂ vR₂) →
      (s₁ : Sq₂ hT₁ hT₂ vL₁ vR₁) →
      Sq≈ (s₃ ∘₂ᵥ (s₂ ∘₂ᵥ s₁)) ((s₃ ∘₂ᵥ s₂) ∘₂ᵥ s₁)

{-
interchange law:

        T₁  →  T₂  →  T₃
        ↓   s₁  ↓   s₂  ↓
        M₁  →  M₂  →  M₃
        ↓   s₃  ↓   s₄  ↓
        B₁  →  B₂  →  B₃
-}
    interchange :
      {T₁ T₂ T₃ M₁ M₂ M₃ B₁ B₂ B₃ : Obj} →
      {hT₁ : T₁ ⇒ₕ T₂} {hT₂ : T₂ ⇒ₕ T₃} →
      {hM₁ : M₁ ⇒ₕ M₂} {hM₂ : M₂ ⇒ₕ M₃} →
      {hB₁ : B₁ ⇒ₕ B₂} {hB₂ : B₂ ⇒ₕ B₃} →
      {vL₁  : T₁ ⇒ᵥ M₁} {vL₂  : M₁ ⇒ᵥ B₁} →
      {vM₁  : T₂ ⇒ᵥ M₂} {vM₂  : M₂ ⇒ᵥ B₂} →
      {vR₁  : T₃ ⇒ᵥ M₃} {vR₂  : M₃ ⇒ᵥ B₃} →
      (s₄ : Sq₂ hM₂ hB₂ vM₂ vR₂) →
      (s₃ : Sq₂ hM₁ hB₁ vL₂ vM₂) →
      (s₂ : Sq₂ hT₂ hM₂ vM₁ vR₁)
      (s₁ : Sq₂ hT₁ hM₁ vL₁ vM₁) →
      Sq≈ ((s₄ ∘₂ₕ s₃) ∘₂ᵥ (s₂ ∘₂ₕ s₁)) ((s₄ ∘₂ᵥ s₂) ∘₂ₕ (s₃ ∘₂ᵥ s₁))

  dual : Category o ℓ ℓ' e e'
  dual = record
    { Obj = Obj
    ; Hor = Ver
    ; Ver = Hor
    ; Sq₂ = λ v₁ v₂ h₁ h₂ → Sq₂ h₁ h₂ v₁ v₂
    ; _∘₂ₕ_ = _∘₂ᵥ_
    ; id₂ₕ = id₂ᵥ
    ; _∘₂ᵥ_ = _∘₂ₕ_
    ; id₂ᵥ = id₂ₕ
    ; identity₂ₕʳ = λ s → dual≈ Hor Ver (identity₂ᵥʳ s)
    ; identity₂ₕˡ = λ s → dual≈ Hor Ver (identity₂ᵥˡ s)
    ; identity₂ᵥʳ = λ s → dual≈ Hor Ver (identity₂ₕʳ s)
    ; identity₂ᵥˡ = λ s → dual≈ Hor Ver (identity₂ₕˡ s)
    ; identity₂ₕ² = dual≈ Hor Ver identity₂ᵥ²
    ; identity₂ᵥ² = dual≈ Hor Ver identity₂ₕ²
    ; assocₕ = λ s₁ s₂ s₃ → dual≈ Hor Ver (assocᵥ s₁ s₂ s₃)
    ; sym-assocₕ = λ s₁ s₂ s₃ → dual≈ Hor Ver (sym-assocᵥ s₁ s₂ s₃)
    ; assocᵥ = λ s₁ s₂ s₃ → dual≈ Hor Ver (assocₕ s₁ s₂ s₃)
    ; sym-assocᵥ = λ s₁ s₂ s₃ → dual≈ Hor Ver (sym-assocₕ s₁ s₂ s₃)
    ; interchange = λ s₄ s₃ s₂ s₁ → dual≈ Hor Ver (interchange s₄ s₂ s₃ s₁)
    }

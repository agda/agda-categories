{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Category.Displayed where

open import Data.Product
open import Level

open import Categories.Functor.Core
open import Relation.Binary.Displayed
import Relation.Binary.Displayed.Reasoning.Setoid as DisplayedSetoidR

-- A displayed category captures the idea of placing extra structure
-- over a base category. For example, the category of monoids can be
-- considered as the category of setoids with extra structure on the
-- objects and extra conditions on the morphisms.
record Displayed {o ℓ e} (B : Category o ℓ e) o′ ℓ′ e′ : Set (o ⊔ ℓ ⊔ e ⊔ suc (o′ ⊔ ℓ′ ⊔ e′)) where
  open Category B
  open Equiv

  infix 4 _⇒[_]_ _≈[_]_
  infixr 9 _∘′_

  field
    Obj[_] : Obj → Set o′
    _⇒[_]_ : ∀ {X Y} → Obj[ X ] → X ⇒ Y → Obj[ Y ] → Set ℓ′
    _≈[_]_ : ∀ {A B X Y} {f g : A ⇒ B} → X ⇒[ f ] Y → f ≈ g → X ⇒[ g ] Y → Set e′

    id′ : ∀ {A} {X : Obj[ A ]} → X ⇒[ id ] X
    _∘′_ : ∀ {A B C X Y Z} {f : B ⇒ C} {g : A ⇒ B}
         → Y ⇒[ f ] Z → X ⇒[ g ] Y → X ⇒[ f ∘ g ] Z

    identityʳ′ : ∀ {A B X Y} {f : A ⇒ B} → {f′ : X ⇒[ f ] Y} → f′ ∘′ id′ ≈[ identityʳ ] f′
    identityˡ′ : ∀ {A B X Y} {f : A ⇒ B} → {f′ : X ⇒[ f ] Y} → id′ ∘′ f′ ≈[ identityˡ ] f′
    identity²′ : ∀ {A} {X : Obj[ A ]} → id′ {X = X} ∘′ id′ ≈[ identity² ] id′
    assoc′ : ∀ {A B C D W X Y Z} {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B}
           → {f′ : Y ⇒[ f ] Z} → {g′ : X ⇒[ g ] Y} → {h′ : W ⇒[ h ] X}
           → (f′ ∘′ g′) ∘′ h′ ≈[ assoc ] f′ ∘′ (g′ ∘′ h′)
    sym-assoc′ : ∀ {A B C D W X Y Z} {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B}
           → {f′ : Y ⇒[ f ] Z} → {g′ : X ⇒[ g ] Y} → {h′ : W ⇒[ h ] X}
           → f′ ∘′ (g′ ∘′ h′) ≈[ sym-assoc ] (f′ ∘′ g′) ∘′ h′


    equiv′ : ∀ {A B X Y} → IsDisplayedEquivalence equiv (_≈[_]_ {A} {B} {X} {Y})

    ∘′-resp-≈[] : ∀ {A B C X Y Z} {f h : B ⇒ C} {g i : A ⇒ B}
                    {f′ : Y ⇒[ f ] Z} {h′ : Y ⇒[ h ] Z} {g′ : X ⇒[ g ] Y} {i′ : X ⇒[ i ] Y}
                    {p : f ≈ h} {q : g ≈ i}
                → f′ ≈[ p ] h′ → g′ ≈[ q ] i′ → f′ ∘′ g′ ≈[ ∘-resp-≈ p q ] h′ ∘′ i′

  module Equiv′ {A B X Y} = IsDisplayedEquivalence (equiv′ {A} {B} {X} {Y})

  open Equiv′

  ∘′-resp-≈[]ˡ : ∀ {A B C X Y Z} {f h : B ⇒ C} {g : A ⇒ B} {f′ : Y ⇒[ f ] Z} {h′ : Y ⇒[ h ] Z} {g′ : X ⇒[ g ] Y}
                 → {p : f ≈ h} → f′ ≈[ p ] h′ → f′ ∘′ g′ ≈[ ∘-resp-≈ˡ p ] h′ ∘′ g′
  ∘′-resp-≈[]ˡ pf = ∘′-resp-≈[] pf refl′

  ∘′-resp-≈[]ʳ : ∀ {A B C X Y Z} {f : B ⇒ C} {g i : A ⇒ B} {f′ : Y ⇒[ f ] Z} {g′ : X ⇒[ g ] Y} {i′ : X ⇒[ i ] Y}
                 → {p : g ≈ i} → g′ ≈[ p ] i′ → f′ ∘′ g′ ≈[ ∘-resp-≈ʳ p ] f′ ∘′ i′
  ∘′-resp-≈[]ʳ pf = ∘′-resp-≈[] refl′ pf

  hom-setoid′ : ∀ {A B} {X : Obj[ A ]} {Y : Obj[ B ]} → DisplayedSetoid hom-setoid _ _
  hom-setoid′ {X = X} {Y = Y} = record
    { Carrier′ = X ⇒[_] Y
    ; _≈[_]_ = _≈[_]_
    ; isDisplayedEquivalence = equiv′
    }

  module HomReasoning′ {A B : Obj} {X : Obj[ A ]} {Y : Obj[ B ]} where
    open DisplayedSetoidR (hom-setoid′ {X = X} {Y = Y}) public
    open HomReasoning

    infixr 4 _⟩∘′⟨_ refl′⟩∘′⟨_
    infixl 5 _⟩∘′⟨refl′
    _⟩∘′⟨_ : ∀ {M} {f h : M ⇒ B} {g i : A ⇒ M} {f≈h : f ≈ h} {g≈i : g ≈ i}
               {M′ : Obj[ M ]} {f′ : M′ ⇒[ f ] Y} {h′ : M′ ⇒[ h ] Y} {g′ : X ⇒[ g ] M′} {i′ : X ⇒[ i ] M′}
             → f′ ≈[ f≈h ] h′ → g′ ≈[ g≈i ] i′ → f′ ∘′ g′ ≈[ f≈h ⟩∘⟨ g≈i ] h′ ∘′ i′
    _⟩∘′⟨_ = ∘′-resp-≈[]

    refl′⟩∘′⟨_ : ∀ {M} {f : M ⇒ B} {g i : A ⇒ M} {g≈i : g ≈ i}
                  {M′ : Obj[ M ]} {f′ : M′ ⇒[ f ] Y} {g′ : X ⇒[ g ] M′} {i′ : X ⇒[ i ] M′}
                → g′ ≈[ g≈i ] i′ → f′ ∘′ g′ ≈[ refl⟩∘⟨ g≈i ] f′ ∘′ i′
    refl′⟩∘′⟨_ = ∘′-resp-≈[]ʳ

    _⟩∘′⟨refl′ : ∀ {M} {f h : M ⇒ B} {g : A ⇒ M} {f≈h : f ≈ h}
                   {M′ : Obj[ M ]} {f′ : M′ ⇒[ f ] Y} {h′ : M′ ⇒[ h ] Y} {g′ : X ⇒[ g ] M′}
                 → f′ ≈[ f≈h ] h′ → f′ ∘′ g′ ≈[ f≈h ⟩∘⟨refl ] h′ ∘′ g′
    _⟩∘′⟨refl′ = ∘′-resp-≈[]ˡ

  op′ : Displayed op o′ ℓ′ e′
  op′ = record
    { Obj[_] = Obj[_]
    ; _⇒[_]_ = λ X f Y → Y ⇒[ f ] X
    ; _≈[_]_ = _≈[_]_
    ; id′ = id′
    ; _∘′_ = λ f′ g′ → g′ ∘′ f′
    ; identityʳ′ = identityˡ′
    ; identityˡ′ = identityʳ′
    ; identity²′ = identity²′
    ; assoc′ = sym-assoc′
    ; sym-assoc′ = assoc′
    ; equiv′ = equiv′
    ; ∘′-resp-≈[] = λ p q → ∘′-resp-≈[] q p
    }

module Definitions′ {o ℓ e} {B : Category o ℓ e} {o′ ℓ′ e′} (C : Displayed B o′ ℓ′ e′) where
  open Category B
  open Displayed C
  open Definitions B

  CommutativeSquare′ : ∀ {A B C D : Obj} {A′ : Obj[ A ]} {B′ : Obj[ B ]} {C′ : Obj[ C ]} {D′ : Obj[ D ]}
                         {f : A ⇒ B} {g : A ⇒ C} {h : B ⇒ D} {i : C ⇒ D}
                         (f′ : A′ ⇒[ f ] B′) (g′ : A′ ⇒[ g ] C′) (h′ : B′ ⇒[ h ] D′) (i′ : C′ ⇒[ i ] D′)
                         (sq : CommutativeSquare f g h i)
                       → Set _
  CommutativeSquare′ f′ g′ h′ i′ sq = h′ ∘′ f′ ≈[ sq ] i′ ∘′ g′

{-# OPTIONS --without-K --safe #-}

-- In symmetric monoidal categories left and right strength imply each other

module Categories.Monad.Strong.Properties where

open import Level
open import Data.Product using (_,_; _×_)

open import Categories.Category.Core
open import Categories.Category.Product
open import Categories.Functor renaming (id to idF)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.NaturalTransformation using (ntHelper)
open import Categories.Monad using (Monad)
open import Categories.Monad.Strong using (Strength; RightStrength; StrongMonad; RightStrongMonad)

import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e : Level

module _ {C : Category o ℓ e} {V : Monoidal C} (S : Symmetric V) where
  open Category C
  open Symmetric S
  open import Categories.Category.Monoidal.Braided.Properties braided
  open HomReasoning
  open Equiv
  open MR C

  Strength⇒RightStrength : ∀ {M : Monad C} → Strength V M → RightStrength V M
  Strength⇒RightStrength {M} strength = record
    { strengthen = ntHelper (record 
      { η = τ
      ; commute = λ (f , g) → commute' f g
      })
    ; identityˡ = identityˡ'
    ; η-comm = η-comm'
    ; μ-η-comm = μ-η-comm'
    ; strength-assoc = strength-assoc'
    }
    where
      open Monad M using (F; μ; η)
      module strength = Strength strength
      module t = strength.strengthen
      B = braiding.⇒.η
      τ : ∀ ((X , Y) : Obj × Obj) → F.₀ X ⊗₀ Y ⇒ F.₀ (X ⊗₀ Y)
      τ (X , Y) = F.₁ (B (Y , X)) ∘ t.η (Y , X) ∘ B (F.₀ X , Y)
      α = associator.to
      α⁻¹ = associator.from
      braiding-eq : ∀ {X Y} → braiding.⇐.η (X , Y) ≈ B (Y , X)
      braiding-eq = introʳ commutative ○ cancelˡ (braiding.iso.isoˡ _)
      commute' : ∀ {X Y U V : Obj} (f : X ⇒ U) (g : Y ⇒ V) → τ (U , V) ∘ (F.₁ f ⊗₁ g) ≈ F.₁ (f ⊗₁ g) ∘ τ (X , Y)
      commute' {X} {Y} {U} {V} f g = begin
        (F.₁ (B (V , U)) ∘ t.η (V , U) ∘ B (F.₀ U , V)) ∘ (F.₁ f ⊗₁ g)   ≈⟨ pullʳ (pullʳ (braiding.⇒.commute (F.₁ f , g))) ⟩ 
        F.₁ (B (V , U)) ∘ t.η (V , U) ∘ ((g ⊗₁ F.₁ f) ∘ B (F.₀ X , Y))   ≈⟨ refl⟩∘⟨ pullˡ (t.commute (g , f)) ⟩ 
        F.₁ (B (V , U)) ∘ ((F.₁ (g ⊗₁ f) ∘ t.η (Y , X)) ∘ B (F.₀ X , Y)) ≈⟨ pullˡ (pullˡ (sym F.homomorphism)) ⟩ 
        (F.₁ (B (V , U) ∘ (g ⊗₁ f)) ∘ t.η (Y , X)) ∘ B (F.₀ X , Y)       ≈⟨ F.F-resp-≈ (braiding.⇒.commute (g , f)) ⟩∘⟨refl ⟩∘⟨refl ⟩ 
        (F.₁ ((f ⊗₁ g) ∘ B (Y , X)) ∘ t.η (Y , X)) ∘ B (F.₀ X , Y)       ≈⟨ pushˡ F.homomorphism ⟩∘⟨refl ⟩ 
        (F.₁ (f ⊗₁ g) ∘ F.₁ (B (Y , X)) ∘ t.η (Y , X)) ∘ B (F.₀ X , Y)   ≈⟨ assoc²' ⟩ 
        (F.₁ (f ⊗₁ g) ∘ τ (X , Y))                                       ∎
      identityˡ' : ∀ {X : Obj} → F.₁ unitorʳ.from ∘ τ (X , unit) ≈ unitorʳ.from
      identityˡ' {X} = begin 
        F.₁ unitorʳ.from ∘ F.₁ (B (unit , X)) ∘ t.η (unit , X) ∘ B (F.₀ X , unit) ≈⟨ pullˡ (sym F.homomorphism) ⟩ 
        F.₁ (unitorʳ.from ∘ B (unit , X)) ∘ t.η (unit , X) ∘ B (F.₀ X , unit)     ≈⟨ ((F.F-resp-≈ ((refl⟩∘⟨ sym braiding-eq) ○ inv-braiding-coherence)) ⟩∘⟨refl) ⟩
        F.₁ unitorˡ.from ∘ t.η (unit , X) ∘ B (F.₀ X , unit)                      ≈⟨ pullˡ strength.identityˡ ⟩ 
        unitorˡ.from ∘ B (F.₀ X , unit)                                           ≈⟨ braiding-coherence ⟩ 
        unitorʳ.from                                                              ∎
      η-comm' : ∀ {X Y : Obj} → τ (X , Y) ∘ η.η X ⊗₁ id ≈ η.η (X ⊗₀ Y)
      η-comm' {X} {Y} = begin 
        (F.₁ (B (Y , X)) ∘ t.η (Y , X) ∘ B (F.₀ X , Y)) ∘ (η.η X ⊗₁ id) ≈⟨ pullʳ (pullʳ (braiding.⇒.commute (η.η X , id))) ⟩ 
        F.₁ (B (Y , X)) ∘ t.η (Y , X) ∘ ((id ⊗₁ η.η X) ∘ B (X , Y))     ≈⟨ (refl⟩∘⟨ (pullˡ strength.η-comm)) ⟩ 
        F.₁ (B (Y , X)) ∘ η.η (Y ⊗₀ X) ∘ B (X , Y)                      ≈⟨ pullˡ (sym (η.commute (B (Y , X)))) ⟩ 
        (η.η (X ⊗₀ Y) ∘ B (Y , X)) ∘ B (X , Y)                          ≈⟨ cancelʳ commutative ⟩
        η.η (X ⊗₀ Y)                                                                          ∎
      μ-η-comm' : ∀ {X Y : Obj} → μ.η (X ⊗₀ Y) ∘ F.₁ (τ (X , Y)) ∘ τ (F.₀ X , Y) ≈ τ (X , Y) ∘ μ.η X ⊗₁ id
      μ-η-comm' {X} {Y} = begin 
        μ.η (X ⊗₀ Y) ∘ F.F₁ (τ (X , Y)) ∘ F.₁ (B (Y , F.₀ X)) ∘ t.η (Y , F.₀ X) ∘ B (F.₀ (F.₀ X) , Y)      ≈⟨ (refl⟩∘⟨ (pullˡ (sym F.homomorphism))) ⟩ 
        μ.η (X ⊗₀ Y) ∘ F.₁ (τ (X , Y) ∘ B (Y , F.₀ X)) ∘ t.η (Y , F.₀ X) ∘ B (F.₀ (F.₀ X) , Y)             ≈⟨ (refl⟩∘⟨ ((F.F-resp-≈ (pullʳ (cancelʳ commutative))) ⟩∘⟨refl)) ⟩
        μ.η (X ⊗₀ Y) ∘ F.₁ (F.₁ (B (Y , X)) ∘ t.η (Y , X)) ∘ t.η (Y , F.₀ X) ∘ B (F.₀ (F.₀ X) , Y)         ≈⟨ (refl⟩∘⟨ (F.homomorphism ⟩∘⟨refl)) ⟩ 
        μ.η (X ⊗₀ Y) ∘ (F.₁ (F.₁ (B (Y , X))) ∘ F.₁ (t.η (Y , X))) ∘ t.η (Y , F.₀ X) ∘ B (F.₀ (F.₀ X) , Y) ≈⟨ pullˡ (pullˡ (μ.commute (B (Y , X)))) ⟩ 
        ((F.₁ (B (Y , X)) ∘ μ.η (Y ⊗₀ X)) ∘ F.₁ (t.η (Y , X))) ∘ t.η (Y , F.₀ X) ∘ B (F.₀ (F.₀ X) , Y)     ≈⟨ (assoc² ○ (refl⟩∘⟨ sym assoc²')) ⟩ 
        F.₁ (B (Y , X)) ∘ (μ.η (Y ⊗₀ X) ∘ F.₁ (t.η (Y , X)) ∘ t.η (Y , F.₀ X)) ∘ B ((F.₀ (F.₀ X)) , Y)     ≈⟨ refl⟩∘⟨ pushˡ strength.μ-η-comm ⟩ 
        F.₁ (B (Y , X)) ∘ t.η (Y , X) ∘ (id ⊗₁ μ.η X) ∘ B ((F.₀ (F.₀ X)) , Y)                              ≈˘⟨ pullʳ (pullʳ (braiding.⇒.commute (μ.η X , id))) ⟩ 
        τ (X , Y) ∘ μ.η X ⊗₁ id ∎
      strength-assoc' : {X Y Z : Obj} → F.₁ associator.to ∘ τ (X , Y ⊗₀ Z) ≈ τ (X ⊗₀ Y , Z) ∘ τ (X , Y) ⊗₁ id ∘ associator.to
      strength-assoc' {X} {Y} {Z} = begin 
        F.₁ α ∘ F.₁ (B (Y ⊗₀ Z , X)) ∘ t.η (Y ⊗₀ Z , X) ∘ B (F.₀ X , Y ⊗₀ Z) ≈⟨ {!   !} ⟩ 
        (F.₁ (B (Z , X ⊗₀ Y)) ∘ t.η (Z , X ⊗₀ Y) ∘ B (F.₀ (X ⊗₀ Y) , Z)) ∘ (τ (X , Y) ⊗₁ id) ∘ associator.to ∎ 

  StrongMonad⇒RightStrongMonad : StrongMonad V → RightStrongMonad V
  StrongMonad⇒RightStrongMonad SM = record { M = M ; rightStrength = Strength⇒RightStrength strength }
    where
      open StrongMonad SM

  RightStrength⇒Strength : ∀ {M : Monad C} → RightStrength V M → Strength V M
  RightStrength⇒Strength {M} rightStrength = {!   !}

  RightStrongMonad⇒StrongMonad : RightStrongMonad V → StrongMonad V
  RightStrongMonad⇒StrongMonad RSM = record { M = M ; strength = RightStrength⇒Strength rightStrength }
    where
      open RightStrongMonad RSM
        
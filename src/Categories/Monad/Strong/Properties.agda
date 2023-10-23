{-# OPTIONS --without-K --safe #-}

-- In symmetric monoidal categories left and right strength imply each other

module Categories.Monad.Strong.Properties where

open import Level
open import Data.Product using (_,_; _×_)

open import Categories.Category
open import Categories.Category.Product
open import Categories.Functor renaming (id to idF)
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Symmetric
open import Categories.NaturalTransformation hiding (id)
open import Categories.Monad
open import Categories.Monad.Strong

import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e : Level

module _ {C : Category o ℓ e} (V : Monoidal C) (S : Symmetric V) where
  open Category C
  -- open Monoidal V
  open Symmetric S
  open import Categories.Category.Monoidal.Braided.Properties braided
  open HomReasoning
  open Equiv
  open MR C

  Strength⇒RightStrength : ∀ {M : Monad C} → Strength V M → RightStrength V M
  Strength⇒RightStrength {M} strength = record
    { strengthen = ntHelper (record 
      { η = η'
      ; commute = commute'
      })
    ; identityˡ = identityˡ'
    ; η-comm = η-comm'
    ; μ-η-comm = μ-η-comm'
    ; strength-assoc = strength-assoc'
    }
    where
      open Monad M using (F; μ; η)
      -- open Strength strength
      module strength = Strength strength
      module t = strength.strengthen
        -- TODO use ⇒ for both
      η' : ∀ ((X , Y) : Obj × Obj) → F.₀ X ⊗₀ Y ⇒ F.₀ (X ⊗₀ Y)
      η' (X , Y) = F.₁ (braiding.⇐.η (X , Y)) ∘ t.η (Y , X) ∘ braiding.⇒.η (F.₀ X , Y)
      commute' : ∀ {(X , Y) (U , V) : Obj × Obj} ((f , g) : Product C C [ (X , Y) , (U , V) ]) → η' (U , V) ∘ (F.₁ f ⊗₁ g) ≈ F.₁ (f ⊗₁ g) ∘ η' (X , Y)
      commute' {X , Y} {U , V} (f , g) = begin
        (F.₁ (braiding.⇐.η (U , V)) ∘ t.η (V , U) ∘ braiding.⇒.η (F.₀ U , V)) ∘ (F.₁ f ⊗₁ g)   ≈⟨ pullʳ (pullʳ (braiding.⇒.commute (F.₁ f , g))) ⟩ 
        F.₁ (braiding.⇐.η (U , V)) ∘ t.η (V , U) ∘ ((g ⊗₁ F.₁ f) ∘ braiding.⇒.η (F.₀ X , Y))   ≈⟨ refl⟩∘⟨ pullˡ (t.commute (g , f)) ⟩ 
        F.₁ (braiding.⇐.η (U , V)) ∘ ((F.₁ (g ⊗₁ f) ∘ t.η (Y , X)) ∘ braiding.⇒.η (F.₀ X , Y)) ≈⟨ pullˡ (pullˡ (sym F.homomorphism)) ⟩ 
        (F.₁ (braiding.⇐.η (U , V) ∘ (g ⊗₁ f)) ∘ t.η (Y , X)) ∘ braiding.⇒.η (F.₀ X , Y)       ≈⟨ F.F-resp-≈ (braiding.⇐.commute (f , g)) ⟩∘⟨refl ⟩∘⟨refl ⟩ 
        (F.₁ ((f ⊗₁ g) ∘ braiding.⇐.η (X , Y)) ∘ t.η (Y , X)) ∘ braiding.⇒.η (F.₀ X , Y)       ≈⟨ pushˡ F.homomorphism ⟩∘⟨refl ⟩ 
        (F.₁ (f ⊗₁ g) ∘ F.₁ (braiding.⇐.η (X , Y)) ∘ t.η (Y , X)) ∘ braiding.⇒.η (F.₀ X , Y)   ≈⟨ assoc²' ⟩ 
        (F.₁ (f ⊗₁ g) ∘ η' (X , Y))                                                            ∎
      identityˡ' : ∀ {A : Obj} → F.₁ unitorʳ.from ∘ η' (A , unit) ≈ unitorʳ.from
      identityˡ' {A} = begin 
        F.₁ unitorʳ.from ∘ F.₁ (braiding.⇐.η (A , unit)) ∘ t.η (unit , A) ∘ braiding.⇒.η (F.₀ A , unit) ≈⟨ pullˡ (sym F.homomorphism) ⟩ 
        F.₁ (unitorʳ.from ∘ braiding.⇐.η (A , unit)) ∘ t.η (unit , A) ∘ braiding.⇒.η (F.₀ A , unit)     ≈⟨ ((F.F-resp-≈ inv-braiding-coherence) ⟩∘⟨refl) ⟩ 
        F.₁ unitorˡ.from ∘ t.η (unit , A) ∘ braiding.⇒.η (F.₀ A , unit)                                 ≈⟨ pullˡ strength.identityˡ ⟩ 
        unitorˡ.from ∘ braiding.⇒.η (F.₀ A , unit)                                                      ≈⟨ braiding-coherence ⟩ 
        unitorʳ.from                                                                                    ∎
      η-comm' : ∀ {A B : Obj} → η' (A , B) ∘ η.η A ⊗₁ id ≈ η.η (A ⊗₀ B)
      η-comm' {A} {B} = begin 
        (F.₁ (braiding.⇐.η (A , B)) ∘ t.η (B , A) ∘ braiding.⇒.η (F.₀ A , B)) ∘ (η.η A ⊗₁ id) ≈⟨ pullʳ (pullʳ (braiding.⇒.commute (η.η A , id))) ⟩ 
        F.₁ (braiding.⇐.η (A , B)) ∘ t.η (B , A) ∘ ((id ⊗₁ η.η A) ∘ braiding.⇒.η (A , B))     ≈⟨ (refl⟩∘⟨ (pullˡ strength.η-comm)) ⟩ 
        F.₁ (braiding.⇐.η (A , B)) ∘ η.η (B ⊗₀ A) ∘ braiding.⇒.η (A , B)                      ≈⟨ pullˡ (sym (η.commute (braiding.⇐.η (A , B)))) ⟩ 
        (η.η (A ⊗₀ B) ∘ braiding.⇐.η (A , B)) ∘ braiding.⇒.η (A , B)                          ≈⟨ cancelʳ (braiding.iso.isoˡ (A , B)) ⟩
        η.η (A ⊗₀ B)                                                                          ∎
      μ-η-comm' : ∀ {A B : Obj} → μ.η (A ⊗₀ B) ∘ F.₁ (η' (A , B)) ∘ η' (F.₀ A , B) ≈ η' (A , B) ∘ μ.η A ⊗₁ id
      μ-η-comm' {A} {B} = begin 
        μ.η (A ⊗₀ B) ∘ F.F₁ (η' (A , B)) ∘ F.₁ (braiding.⇐.η (F.₀ A , B)) ∘ t.η (B , F.₀ A) ∘ braiding.⇒.η (F.₀ (F.₀ A) , B)     ≈⟨ (refl⟩∘⟨ (pullˡ (sym F.homomorphism))) ⟩ 
        μ.η (A ⊗₀ B) ∘ F.₁ (η' (A , B) ∘ braiding.⇐.η (F.₀ A , B)) ∘ t.η (B , F.₀ A) ∘ braiding.⇒.η (F.₀ (F.₀ A) , B)            ≈⟨ (refl⟩∘⟨ ((F.F-resp-≈ (pullʳ (cancelʳ (braiding.iso.isoʳ (F.₀ A , B))))) ⟩∘⟨refl)) ⟩ 
        μ.η (A ⊗₀ B) ∘ F.₁ (F.₁ (braiding.⇐.η (A , B)) ∘ t.η (B , A)) ∘ t.η (B , F.₀ A) ∘ braiding.⇒.η (F.₀ (F.₀ A) , B)         ≈⟨ (refl⟩∘⟨ (F.homomorphism ⟩∘⟨refl)) ⟩ 
        μ.η (A ⊗₀ B) ∘ (F.₁ (F.₁ (braiding.⇐.η (A , B))) ∘ F.₁ (t.η (B , A))) ∘ t.η (B , F.₀ A) ∘ braiding.⇒.η (F.₀ (F.₀ A) , B) ≈⟨ pullˡ (pullˡ (μ.commute (braiding.⇐.η (A , B)))) ⟩ 
        ((F.₁ (braiding.⇐.η (A , B)) ∘ μ.η (B ⊗₀ A)) ∘ F.₁ (t.η (B , A))) ∘ t.η (B , F.₀ A) ∘ braiding.⇒.η (F.₀ (F.₀ A) , B)     ≈⟨ (assoc² ○ (refl⟩∘⟨ sym assoc²')) ⟩ 
        F.₁ (braiding.⇐.η (A , B)) ∘ (μ.η (B ⊗₀ A) ∘ F.₁ (t.η (B , A)) ∘ t.η (B , F.₀ A)) ∘ braiding.⇒.η ((F.₀ (F.₀ A)) , B)     ≈⟨ refl⟩∘⟨ pushˡ strength.μ-η-comm ⟩ 
        F.₁ (braiding.⇐.η (A , B)) ∘ t.η (B , A) ∘ (id ⊗₁ μ.η A) ∘ braiding.⇒.η ((F.₀ (F.₀ A)) , B)                              ≈˘⟨ pullʳ (pullʳ (braiding.⇒.commute (μ.η A , id))) ⟩ 
        η' (A , B) ∘ μ.η A ⊗₁ id ∎
      strength-assoc' : {X Y Z : Obj} → F.₁ associator.to ∘ η' (X , Y ⊗₀ Z) ≈ η' (X ⊗₀ Y , Z) ∘ η' (X , Y) ⊗₁ id ∘ associator.to
      strength-assoc' {X} {Y} {Z} = begin 
        F.₁ associator.to ∘ F.₁ (braiding.⇐.η (X , Y ⊗₀ Z)) ∘ t.η (Y ⊗₀ Z , X) ∘ braiding.⇒.η (F.₀ X , Y ⊗₀ Z) ≈⟨ pullˡ (sym F.homomorphism) ⟩ 
        F.₁ (associator.to ∘ braiding.⇐.η (X , Y ⊗₀ Z)) ∘ t.η (Y ⊗₀ Z , X) ∘ braiding.⇒.η (F.₀ X , Y ⊗₀ Z) ≈⟨ {!   !} ⟩ 
        F.₁ ((associator.to ∘ braiding.⇐.η (X , Y ⊗₀ Z)) ∘ associator.to ∘ associator.from) ∘ t.η (Y ⊗₀ Z , X) ∘ braiding.⇒.η (F.₀ X , Y ⊗₀ Z) ≈⟨ {!   !} ⟩ 
        F.₁ (((braiding.⇒.η (Y , X) ⊗₁ id) ∘ associator.to ∘ (id ⊗₁ braiding.⇒.η (Z , X))) ∘ associator.from) ∘ t.η (Y ⊗₀ Z , X) ∘ braiding.⇒.η (F.₀ X , Y ⊗₀ Z) ≈⟨ {!   !} ⟩ 
        {!   !} ≈⟨ {!   !} ⟩
        F.₁ (braiding.⇒.η (Y , X) ⊗₁ id) ∘ F.₁ associator.to ∘ F.₁ (id ⊗₁ braiding.⇒.η (Z , X)) ∘ F.₁ associator.from ∘ t.η (Y ⊗₀ Z , X) ∘ braiding.⇒.η (F.₀ X , Y ⊗₀ Z) ≈⟨ {!   !} ⟩ 
        F.₁ (braiding.⇒.η (Y , X) ⊗₁ id) ∘ F.₁ associator.to ∘ F.₁ (id ⊗₁ braiding.⇒.η (Z , X)) ∘ (t.η (Y , Z ⊗₀ X) ∘ (id ⊗₁ t.η (Z , X)) ∘ associator.from) ∘ braiding.⇒.η (F.₀ X , Y ⊗₀ Z) ≈⟨ (refl⟩∘⟨ refl⟩∘⟨ pullˡ (pullˡ (sym (t.commute (id , braiding.⇒.η (Z , X)))))) ⟩ 
        F.₁ (braiding.⇒.η (Y , X) ⊗₁ id) ∘ F.₁ associator.to ∘ ((t.η (Y , (X ⊗₀ Z)) ∘ (id ⊗₁ F.₁ (braiding.⇒.η (Z , X)))) ∘ ((id ⊗₁ t.η (Z , X)) ∘ associator.from)) ∘ braiding.⇒.η (F.₀ X , Y ⊗₀ Z) ≈⟨ {!   !} ⟩ 
        (F.₁ (braiding.⇒.η (Y , X) ⊗₁ id) ∘ F.₁ associator.to ∘ ((t.η (Y , (X ⊗₀ Z)) ∘ (id ⊗₁ F.₁ (braiding.⇒.η (Z , X)))) ∘ ((id ⊗₁ t.η (Z , X)) ∘ associator.from)) ∘ braiding.⇒.η (F.₀ X , Y ⊗₀ Z)) ∘ associator.from ∘ associator.to ≈⟨ pullʳ (pullʳ (pullˡ assoc²)) ⟩ 
        F.₁ (braiding.⇒.η (Y , X) ⊗₁ id) ∘ F.₁ associator.to ∘ (((t.η (Y , X ⊗₀ Z) ∘ (id ⊗₁ F.₁ (braiding.⇒.η (Z , X)))) ∘ (id ⊗₁ t.η (Z , X) ∘ associator.from) ∘ braiding.⇒.η (F.₀ X , Y ⊗₀ Z) ∘ associator.from) ∘ associator.to) ≈⟨ (refl⟩∘⟨ refl⟩∘⟨ (pullʳ (refl⟩∘⟨ pullʳ (sym hexagon₁)) ⟩∘⟨refl)) ⟩ 
        F.₁ (braiding.⇒.η (Y , X) ⊗₁ id) ∘ F.₁ associator.to ∘ (t.η (Y , X ⊗₀ Z) ∘ (id ⊗₁ F.₁ (braiding.⇒.η (Z , X))) ∘ (id ⊗₁ t.η (Z , X)) ∘ (id ⊗₁ braiding.⇒.η (F.₀ X , Z)) ∘ associator.from ∘ (braiding.⇒.η (F.₀ X , Y) ⊗₁ id)) ∘ associator.to ≈⟨ {!   !} ⟩ 
        {!   !} ≈⟨ {!   !} ⟩ 
        (F.₁ (braiding.⇒.η (Y , X) ⊗₁ id) ∘ F.₁ associator.to ∘ (t.η (Y , X ⊗₀ Z) ∘ (id ⊗₁ η' (X , Z)) ∘ associator.from ∘ (braiding.⇒.η (F.₀ X , Y) ⊗₁ id)) ∘ associator.to) ≈⟨ {! t.commute  !} ⟩ 
        {!   !} ≈⟨ {!   !} ⟩ 
        {!   !} ≈⟨ {!   !} ⟩ 
        {!   !} ≈˘⟨ {!   !} ⟩ 
        ((F.₁ (braiding.⇐.η (X ⊗₀ Y , Z)) ∘ t.η (Z , X ⊗₀ Y)) ∘ ((id ⊗₁ η' (X , Y)) ∘ braiding.⇒.η (F.₀ X ⊗₀ Y , Z)) ∘ associator.to) ≈˘⟨ {!   !} ⟩ 
        (F.₁ (braiding.⇐.η (X ⊗₀ Y , Z)) ∘ t.η (Z , X ⊗₀ Y) ∘ braiding.⇒.η (F.₀ (X ⊗₀ Y) , Z)) ∘ (η' (X , Y) ⊗₁ id) ∘ associator.to ∎ 
        where
          braiding-eq : ∀ {X Y} → braiding.⇐.η (X , Y) ≈ braiding.⇒.η (Y , X)
          braiding-eq = introʳ commutative ○ cancelˡ (braiding.iso.isoˡ _)
        
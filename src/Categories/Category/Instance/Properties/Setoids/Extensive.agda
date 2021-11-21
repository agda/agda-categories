{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Properties.Setoids.Extensive where

open import Level
open import Data.Product using (Σ; proj₁; proj₂; _,_; Σ-syntax; _×_; -,_)
open import Function.Equality using (Π)
open import Relation.Binary using (Setoid; Rel)

open import Categories.Category using (Category; _[_,_])
open import Categories.Functor
open import Categories.Category.Instance.Setoids
open import Categories.Category.Complete
open import Categories.Category.Extensive
open import Categories.Category.Instance.Properties.Setoids.Cocomplete
open import Categories.Category.Instance.Properties.Setoids.Complete
open import Categories.Category.Cocomplete.Properties
open import Categories.Category.Cocomplete.Finitely
open import Categories.Category.Complete.Finitely
open import Categories.Category.Complete.Properties
open import Categories.Category.Cocartesian
open import Categories.Diagram.Pullback

open import Categories.Category.Instance.Properties.Setoids.Limits.Canonical
open import Categories.Category.Monoidal.Instance.Setoids -- using (Setoids-Cartesian)
open import Data.Sum.Relation.Binary.Pointwise
open import Data.Unit.Polymorphic using (⊤; tt)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum.Base using ([_,_]′)

open import Function.Equality as SΠ renaming (id to ⟶-id)

import Relation.Binary.PropositionalEquality as P -- using (inspect; [_])

open Π

module _ ℓ where
  private
    S = Setoids ℓ ℓ
    module S = Category S
    
  open Pullback
  
  Setoids-Extensive : (ℓ : Level) → Extensive (Setoids ℓ ℓ)
  Setoids-Extensive ℓ = record
     { cocartesian = record { initial = initial ; coproducts = coproducts }
     ; pullback-of-inl = λ f → pullback ℓ ℓ f i₁ 
     ; pullback-of-inr = λ f → pullback ℓ ℓ f i₂ 
     ; pullback-of-cp-is-cp = λ {C A B} f → record
         { [_,_] = λ g h →
             record
             { _⟨$⟩_ = copair-$ f g h
             ; cong = λ {z z'} → copair-cong f g h z z'
             }
          ; inject₁ = λ {X g h z} eq →
              trans (Setoid.isEquivalence {ℓ} X) (copair-inject₁ f g h z) (cong g eq)  
          ; inject₂ = λ {X g h z} eq →
              trans (Setoid.isEquivalence {ℓ} X) (copair-inject₂ f g h z) (cong h eq)
          ; unique = λ {X u g h} x eq {z} eq' → trans (Setoid.isEquivalence {ℓ} X) (copair-unique f g h u z eq) (cong u eq')
          }
     ; inl-is-mono = λ _ _ eq x≈y → drop-inj₁ (eq x≈y)
     ; inr-is-mono = λ _ _ eq x≈y → drop-inj₂ (eq x≈y)
     ; disjoint = λ {A B} → record
          { commute = λ { {()} _}
          ; universal = λ {C f g} eq → record
             { _⟨$⟩_ = λ z → conflict A B (f ⟨$⟩ z) (g ⟨$⟩ z) (eq (refl (Setoid.isEquivalence {ℓ} C)))
             ; cong = λ z → tt
             } 
          ; unique = λ { {a} {b} {c} x x₁ x₂ → tt }
          ; p₁∘universal≈h₁ = λ {C h₁ h₂ eq x y} x≈y → conflict A B (h₁ ⟨$⟩ x) (h₂ ⟨$⟩ y) (eq x≈y) 
          ; p₂∘universal≈h₂ = λ {C h₁ h₂ eq x y} x≈y → conflict A B (h₁ ⟨$⟩ x) (h₂ ⟨$⟩ y) (eq x≈y)
          }
     }
       where
         open Cocartesian (Setoids-Cocartesian {ℓ} {ℓ})
         open Relation.Binary.IsEquivalence 
         open import Data.Sum using (inj₁; inj₂)
         open Setoid renaming (_≈_ to [_][_≈_]) using ()

         -- must be in the standard library. Maybe it is?
         conflict : ∀ {ℓ ℓ' ℓ''} (X Y : Setoid ℓ ℓ') {Z : Set ℓ''}
           (x : Setoid.Carrier X) (y : Setoid.Carrier Y) →
           ((⊎-setoid X Y) Setoid.≈ inj₁ x) (inj₂ y) → Z
         conflict X Y x y ()

         copair-$ : ∀ {A B C X : Setoid ℓ ℓ} (f : C ⟶ ⊎-setoid A B)
           (g : P (pullback ℓ ℓ f i₁) ⟶ X)
           (h : P (pullback ℓ ℓ f i₂) ⟶ X) →
           Setoid.Carrier C → Setoid.Carrier X
         copair-$ {A} {B} f g h z with (f ⟨$⟩ z) | P.inspect (f ⟨$⟩_) z
         ... | inj₁ x | P.[ eq ] = g ⟨$⟩ record { elem₁ = z ; elem₂ = x ; commute = reflexive (Setoid.isEquivalence (⊎-setoid A B)) eq }
         ... | inj₂ y | P.[ eq ] = h ⟨$⟩ record { elem₁ = z ; elem₂ = y ; commute = reflexive (Setoid.isEquivalence (⊎-setoid A B)) eq }
      
         copair-cong : ∀ {A B C X : Setoid ℓ ℓ} (f : C ⟶ ⊎-setoid A B)
           (g : P (pullback ℓ ℓ f i₁) ⟶ X) (h : P (pullback ℓ ℓ f i₂) ⟶ X) →
           (z z' : Setoid.Carrier C) → (z≈z' : [ C ][ z ≈ z' ]) → [ X ][ copair-$ f g h z ≈ copair-$ f g h z' ]
         copair-cong {A} {B} {C} f g h z z' z≈z' with (f ⟨$⟩ z) | P.inspect (_⟨$⟩_ f) z | (f ⟨$⟩ z') | P.inspect (_⟨$⟩_ f) z'
         ... | inj₁ x | P.[ eq ] | inj₁ x' | P.[ eq' ] = Π.cong g
          (z≈z' , drop-inj₁ (trans-A⊎B (sym-A⊎B (reflexive-A⊎B eq)) (trans-A⊎B (cong f z≈z') (reflexive-A⊎B eq'))))
           where
             trans-A⊎B = trans (Setoid.isEquivalence (⊎-setoid A B))
             sym-A⊎B = sym (Setoid.isEquivalence (⊎-setoid A B))
             reflexive-A⊎B = reflexive (Setoid.isEquivalence (⊎-setoid A B))
         ... | inj₁ x | P.[ eq ] | inj₂ y  | P.[ eq' ] = conflict A B x y
          (trans-A⊎B (sym-A⊎B (reflexive-A⊎B eq)) (trans-A⊎B (cong f z≈z') (reflexive-A⊎B eq')))
           where
             trans-A⊎B = trans (Setoid.isEquivalence (⊎-setoid A B))
             sym-A⊎B = sym (Setoid.isEquivalence (⊎-setoid A B))
             reflexive-A⊎B = reflexive (Setoid.isEquivalence (⊎-setoid A B))
         ... | inj₂ y | P.[ eq ] | inj₁ x  | P.[ eq' ] = conflict A B x y
          (trans-A⊎B (sym-A⊎B (reflexive-A⊎B eq')) (trans-A⊎B (cong f (sym-C z≈z')) (reflexive-A⊎B eq)))
           where
             trans-A⊎B = trans (Setoid.isEquivalence (⊎-setoid A B))
             sym-A⊎B = sym (Setoid.isEquivalence (⊎-setoid A B))
             sym-C = sym (Setoid.isEquivalence C)
             reflexive-A⊎B = reflexive (Setoid.isEquivalence (⊎-setoid A B))
         ... | inj₂ y | P.[ eq ] | inj₂ y' | P.[ eq' ] = cong h (z≈z' , drop-inj₂
          (trans-A⊎B (sym-A⊎B (reflexive-A⊎B eq)) (trans-A⊎B (cong f z≈z') (reflexive-A⊎B eq'))))
           where
             trans-A⊎B = trans (Setoid.isEquivalence (⊎-setoid A B))
             sym-A⊎B = sym (Setoid.isEquivalence (⊎-setoid A B))
             reflexive-A⊎B = reflexive (Setoid.isEquivalence (⊎-setoid A B))

         copair-inject₁ : ∀ {A B C X : Setoid ℓ ℓ} (f : C ⟶ ⊎-setoid A B)
           (g : P (pullback ℓ ℓ f i₁) ⟶ X) (h : P (pullback ℓ ℓ f i₂) ⟶ X) 
           (z : FiberProduct f i₁) → [ X ][ copair-$ f g h (FiberProduct.elem₁ z) ≈ g ⟨$⟩ z ]
         copair-inject₁ f g h record { elem₁ = z ; elem₂ = x ; commute = eq} = {!!} -- with (f ⟨$⟩ z)
         -- ... | a = {!!}

         copair-inject₂ : ∀ {A B C X : Setoid ℓ ℓ} (f : C ⟶ ⊎-setoid A B)
           (g : P (pullback ℓ ℓ f i₁) ⟶ X) (h : P (pullback ℓ ℓ f i₂) ⟶ X) 
           (z : FiberProduct f i₂) → [ X ][ copair-$ f g h (FiberProduct.elem₁ z) ≈ h ⟨$⟩ z ]
         copair-inject₂ f g h record { elem₁ = z ; elem₂ = elem₂ ; commute = commute } = {!!} -- with f ⟨$⟩ z
         -- ... | a = {!!}

         copair-unique : ∀ {A B C X : Setoid ℓ ℓ} (f : C ⟶ ⊎-setoid A B)
           (g : P (pullback ℓ ℓ f i₁) ⟶ X) (h : P (pullback ℓ ℓ f i₂) ⟶ X)
           (u : C ⟶ X) (z : Setoid.Carrier C) →
           [ P (pullback ℓ ℓ f i₂) ⇨ X ][ u ∘ p₁ (pullback ℓ ℓ f i₂) ≈ h ] →
           [ X ][ copair-$ f g h z ≈ u ⟨$⟩ z ]
         copair-unique f g h u z eq = {!!} -- with (f ⟨$⟩ z)
         -- ... | inj₁ x = ?
         -- ... | inj₂ y = ?
        

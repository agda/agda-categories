{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Properties.Setoids.Extensive where

open import Level
open import Data.Product using (Σ; proj₁; proj₂; _,_; Σ-syntax; _×_; -,_)
open import Function.Equality using (Π)
open import Relation.Binary using (Setoid; Rel)
open import Categories.Category using (Category; _[_,_])
open import Categories.Category.Instance.Setoids
open import Categories.Category.Extensive
open import Categories.Category.Cocartesian
open import Categories.Diagram.Pullback
open import Categories.Category.Instance.Properties.Setoids.Limits.Canonical
open import Categories.Category.Monoidal.Instance.Setoids 
open import Data.Sum.Relation.Binary.Pointwise
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum.Base using ([_,_]′; _⊎_)
open import Function.Equality as SΠ renaming (id to ⟶-id)
open import Data.Product using (∃)

open import Relation.Binary.PropositionalEquality using (_≡_; [_]; inspect)

open Π

module _ ℓ where
  private
    S = Setoids ℓ ℓ
    module S = Category S
    
  open Pullback
  
  Setoids-Extensive : (ℓ : Level) → Extensive (Setoids ℓ ℓ)
  Setoids-Extensive ℓ = record
     { cocartesian = record { initial = initial ; coproducts = coproducts }
     ; pullback₁ = λ f → pullback ℓ ℓ f i₁ 
     ; pullback₂ = λ f → pullback ℓ ℓ f i₂ 
     ; pullback-of-cp-is-cp = λ {C A B} f → record
          { [_,_] = λ g h → record
              { _⟨$⟩_ = copair-$ f g h
              ; cong = λ {z z′} → copair-cong f g h z z′
              }
          ; inject₁ = λ {X g h z} eq →
               trans (isEquivalence {ℓ} X) (copair-inject₁ f g h z) (cong g eq)
          ; inject₂ = λ {X g h z} eq →
               trans (isEquivalence {ℓ} X) (copair-inject₂ f g h z) (cong h eq)
          ; unique = λ {X u g h} feq₁ feq₂ {z z′} eq →
               trans (isEquivalence {ℓ} X) (copair-unique f g h u z (λ {z} → feq₁ {z}) (λ {z} → feq₂ {z})) (cong u eq)
          }
     ; pullback₁-is-mono = λ _ _ eq x≈y → drop-inj₁ (eq x≈y)
     ; pullback₂-is-mono = λ _ _ eq x≈y → drop-inj₂ (eq x≈y)
     ; disjoint = λ {A B} → record
          { commute = λ { {()} _}
          ; universal = λ {C f g} eq → record
             { _⟨$⟩_ = λ z → conflict A B (f ⟨$⟩ z) (g ⟨$⟩ z) (eq (refl (isEquivalence {ℓ} C)))
             ; cong = λ z → tt
             } 
          ; unique = λ _ _ _ → tt
          ; p₁∘universal≈h₁ = λ {C h₁ h₂ eq x y} x≈y → conflict A B (h₁ ⟨$⟩ x) (h₂ ⟨$⟩ y) (eq x≈y) 
          ; p₂∘universal≈h₂ = λ {C h₁ h₂ eq x y} x≈y → conflict A B (h₁ ⟨$⟩ x) (h₂ ⟨$⟩ y) (eq x≈y)
          }
     }
       where
         open Cocartesian (Setoids-Cocartesian {ℓ} {ℓ})
         open Relation.Binary.IsEquivalence 
         open import Data.Sum using (inj₁; inj₂)
         open Setoid renaming (_≈_ to [_][_≈_]; Carrier to ∣_∣) using (isEquivalence)

         -- must be in the standard library. Maybe it is?
         conflict : ∀ {ℓ ℓ' ℓ''} (X Y : Setoid ℓ ℓ') {Z : Set ℓ''}
           (x : ∣ X ∣) (y : ∣ Y ∣) → [ ⊎-setoid X Y ][ inj₁ x ≈ inj₂ y ] → Z
         conflict X Y x y ()

         module Diagram {A B C X : Setoid ℓ ℓ} (f : C ⟶ ⊎-setoid A B)
           (g : P (pullback ℓ ℓ f i₁) ⟶ X) (h : P (pullback ℓ ℓ f i₂) ⟶ X) where

           private
             A⊎B = ⊎-setoid A B
             A′ = P (pullback ℓ ℓ f i₁)
             B′ = P (pullback ℓ ℓ f i₂)

             refl-A = refl (isEquivalence A)
             refl-B = refl (isEquivalence B)
             refl-C = refl (isEquivalence C)
             refl-A⊎B = refl (isEquivalence A⊎B)

             reflexive-A⊎B = reflexive (isEquivalence A⊎B)

             sym-A = sym (isEquivalence A)
             sym-B = sym (isEquivalence B)
             sym-C = sym (isEquivalence C)
             sym-X = sym (isEquivalence X)
             sym-A⊎B = sym (isEquivalence A⊎B)

             trans-X = trans (isEquivalence X)
             trans-A⊎B = trans (isEquivalence A⊎B)

           -- copairing of g : A′ → X and h : B′ → X, resulting in C → X 
           copair-$ : ∣ C ∣ → ∣ X ∣
           copair-$ z with (f ⟨$⟩ z) | inspect (f ⟨$⟩_) z
           ... | inj₁ x | [ eq ] = g ⟨$⟩ record { elem₁ = z ; elem₂ = x ; commute = reflexive-A⊎B eq }
           ... | inj₂ y | [ eq ] = h ⟨$⟩ record { elem₁ = z ; elem₂ = y ; commute = reflexive-A⊎B eq }

           -- somewhat roundabout way to expand the definition of copair-$ z if f ⟨$⟩ z ≈ inj₁ x,
           -- in order to circumwent the pitfalls of the with-abstraction
           copair-$-i₁ : (x : ∣ A ∣) (z : ∣ C ∣) → (eq : [ A⊎B ][ f ⟨$⟩ z ≈ inj₁ x ]) →
             ∃ (λ v → [ X ][ copair-$ z ≈ g ⟨$⟩ v ] ×
                        [ C ][ FiberProduct.elem₁ v ≈ z ] ×
                        [ A ][ FiberProduct.elem₂ v ≈ x ])
           copair-$-i₁ x z eq with (f ⟨$⟩ z) | inspect (f ⟨$⟩_) z
           ... | inj₁ x′ | [ eq′ ] =
             record { elem₁ = z ; elem₂ =  x′ ; commute = reflexive-A⊎B eq′}
             , cong g (refl-C , refl-A)
             , refl-C
             , drop-inj₁ eq

           -- same for f ⟨$⟩ z ≈ inj₂ y
           copair-$-i₂ : (y : ∣ B ∣) (z : ∣ C ∣) → (eq : [ A⊎B ][ f ⟨$⟩ z ≈ inj₂ y ]) →
             ∃ (λ v → [ X ][ copair-$ z ≈ h ⟨$⟩ v ] × [ C ][ FiberProduct.elem₁ v ≈ z ] × [ B ][ FiberProduct.elem₂ v ≈ y ])
           copair-$-i₂ y z eq with (f ⟨$⟩ z) | inspect (f ⟨$⟩_) z
           ... | inj₂ y′ | [ eq′ ] =
             record { elem₁ = z ; elem₂ =  y′ ; commute = reflexive-A⊎B eq′}
             , cong h (refl-C , refl-B)
             , refl-C
             , drop-inj₂ eq

           case-f⟨$⟩z : (z : ∣ C ∣) → (∃ λ x → [ A⊎B ][ f ⟨$⟩ z ≈ inj₁ x ]) ⊎ (∃ λ y → [ A⊎B ][ f ⟨$⟩ z ≈ inj₂ y ])
           case-f⟨$⟩z z with (f ⟨$⟩ z)
           ... | inj₁ x = inj₁ (x , refl-A⊎B)
           ... | inj₂ y = inj₂ (y , refl-A⊎B)
             
           copair-cong : (z z′ : ∣ C ∣) → (z≈z′ : [ C ][ z ≈ z′ ]) → [ X ][ copair-$ z ≈ copair-$ z′ ]
           copair-cong z z′ z≈z′ with (f ⟨$⟩ z) | inspect (_⟨$⟩_ f) z | (f ⟨$⟩ z′) | inspect (_⟨$⟩_ f) z′
           ... | inj₁ x | [ eq ] | inj₁ x′ | [ eq′ ] = cong g
             (z≈z′ , drop-inj₁ (trans-A⊎B (sym-A⊎B (reflexive-A⊎B eq)) (trans-A⊎B (cong f z≈z′) (reflexive-A⊎B eq′))))
           ... | inj₁ x | [ eq ] | inj₂ y  | [ eq′ ] = conflict A B x y
             (trans-A⊎B (sym-A⊎B (reflexive-A⊎B eq)) (trans-A⊎B (cong f z≈z′) (reflexive-A⊎B eq′)))
           ... | inj₂ y | [ eq ] | inj₁ x  | [ eq′ ] = conflict A B x y
             (trans-A⊎B (sym-A⊎B (reflexive-A⊎B eq′)) (trans-A⊎B (cong f (sym-C z≈z′)) (reflexive-A⊎B eq)))
           ... | inj₂ y | [ eq ] | inj₂ y′ | [ eq′ ] = cong h (z≈z′ , drop-inj₂
             (trans-A⊎B (sym-A⊎B (reflexive-A⊎B eq)) (trans-A⊎B (cong f z≈z′) (reflexive-A⊎B eq′))))

           copair-inject₁ : (z : FiberProduct f i₁) → [ X ][ copair-$ (FiberProduct.elem₁ z) ≈ g ⟨$⟩ z ]
           copair-inject₁ record { elem₁ = z ; elem₂ = x ; commute = eq } with case-f⟨$⟩z z  
           ... | inj₁ _  with copair-$-i₁ x z eq
           ... | _ , eq₁ , eq₂ , eq₃ = trans-X eq₁ (cong g (eq₂ , eq₃))
           copair-inject₁ record { elem₁ = z ; elem₂ = x ; commute = eq } | inj₂ (y , eq′) =
             conflict A B x y (trans-A⊎B (sym-A⊎B eq) eq′)

           copair-inject₂ : (z : FiberProduct f i₂) → [ X ][ copair-$ (FiberProduct.elem₁ z) ≈ h ⟨$⟩ z ]
           copair-inject₂ record { elem₁ = z ; elem₂ = y ; commute = eq } with case-f⟨$⟩z z  
           ... | inj₂ _  with copair-$-i₂ y z eq
           ... | _ , eq₁ , eq₂ , eq₃ = trans-X eq₁ (cong h (eq₂ , eq₃))
           copair-inject₂ record { elem₁ = z ; elem₂ = y ; commute = eq } | inj₁ (x , eq′) =
             conflict A B x y (trans-A⊎B (sym-A⊎B eq′) eq) 

           copair-unique : (u : C ⟶ X) (z : ∣ C ∣) →
             [ A′ ⇨ X ][ u ∘ p₁ (pullback ℓ ℓ f i₁) ≈ g ] →
             [ B′ ⇨ X ][ u ∘ p₁ (pullback ℓ ℓ f i₂) ≈ h ] →
             [ X ][ copair-$ z ≈ u ⟨$⟩ z ]
           copair-unique u z feq₁ feq₂ with case-f⟨$⟩z z 
           ... | inj₁ (x , eq) with copair-$-i₁ x z eq
           ... | z′ , eq₁ , eq₂ , _ = trans-X eq₁ (trans-X (sym-X (feq₁{z′} (refl-C , refl-A))) (cong u eq₂))
           copair-unique u z feq₁ feq₂ | inj₂ (y , eq) with copair-$-i₂ y z eq
           ... | z′ , eq₁ , eq₂ , _ = trans-X eq₁ (trans-X (sym-X (feq₂{z′} (refl-C , refl-B))) (cong u eq₂))

         open Diagram

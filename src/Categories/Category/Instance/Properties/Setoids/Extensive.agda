{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Properties.Setoids.Extensive where

open import Level using (Level)
open import Data.Empty.Polymorphic using (⊥-elim)
open import Data.Product using (_,_)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Relation.Binary.Pointwise using (inj₁; inj₂; _⊎ₛ_; drop-inj₁; drop-inj₂)
open import Data.Unit.Polymorphic using (tt)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Function.Construct.Composition using (function)
open import Function.Construct.Setoid using () renaming (setoid to _⇨_)
open import Relation.Binary using (Setoid)
import  Relation.Binary.Reasoning.Setoid as SetoidR

open import Categories.Category using (Category; _[_,_])
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Extensive using (Extensive)
open import Categories.Category.Cocartesian using (Cocartesian)
open import Categories.Diagram.Pullback using (Pullback)
open import Categories.Category.Instance.Properties.Setoids.Limits.Canonical using (pullback; FiberProduct)
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-Cocartesian)

open Pullback
open Func

-- Note the Setoids is extensive if the two levels coincide.  Whether it happens more generally
-- is unknown at this point.

Setoids-Extensive : (ℓ : Level) → Extensive (Setoids ℓ ℓ)
Setoids-Extensive ℓ = record
   { cocartesian = record { initial = initial ; coproducts = coproducts }
   ; pullback₁ = λ f → pullback ℓ ℓ f i₁
   ; pullback₂ = λ f → pullback ℓ ℓ f i₂
   ; pullback-of-cp-is-cp = λ f → record
        { [_,_] = λ g h → copair f g h
        ; inject₁ = λ {X g h z} → copair-inject₁ f g h z
        ; inject₂ = λ {X g h z} → copair-inject₂ f g h z
        ; unique = λ {X u g h} feq₁ feq₂ {z} → copair-unique f g h u z feq₁ feq₂
        }
   ; pullback₁-is-mono = λ _ _ eq → drop-inj₁ eq
   ; pullback₂-is-mono = λ _ _ eq → drop-inj₂ eq
   ; disjoint = λ {A B} → record
        { commute = λ { {()}}
        ; universal = λ {C f g} eq → record
           { to = λ z → conflict A B (eq {z})
           ; cong = λ {x} _ → conflict A B (eq {x})
           }
        ; p₁∘universal≈h₁ = λ {_ _ _ eq x} → conflict A B (eq {x})
        ; p₂∘universal≈h₂ = λ {_ _ _ eq y} → conflict A B (eq {y})
        ; unique-diagram = λ {X} {h} {i} eq₁ eq₂ {x} → ⊥-elim {ℓ} {ℓ} {λ ()} (h ⟨$⟩ x)
        }
   }
     where
       infixr 9 _∙_
       _∙_ : {a₁ a₂ b₁ b₂ c₁ c₂ : Level} {A : Setoid a₁ a₂} {B : Setoid b₁ b₂}
         {C : Setoid c₁ c₂} → Func B C → Func A B → Func A C
       f ∙ g = function g f

       open Cocartesian (Setoids-Cocartesian {ℓ} {ℓ})
       open Relation.Binary.IsEquivalence
       open Setoid renaming (_≈_ to [_][_≈_]; Carrier to ∣_∣) using (isEquivalence)

       -- must be in the standard library. Maybe it is?
       conflict : ∀ {ℓ ℓ' ℓ''} (X Y : Setoid ℓ ℓ') {Z : Set ℓ''}
         {x : ∣ X ∣} {y : ∣ Y ∣} → [ X ⊎ₛ Y ][ inj₁ x ≈ inj₂ y ] → Z
       conflict X Y ()

       module Diagram {A B C X : Setoid ℓ ℓ} (f : Func C (A ⊎ₛ B))
         (g : Func (P (pullback ℓ ℓ f i₁)) X) (h : Func (P (pullback ℓ ℓ f i₂)) X) where

         private
           module A = Setoid A
           module B = Setoid B
           module C = Setoid C
           module X = Setoid X
           A⊎B = A ⊎ₛ B
           module A⊎B = Setoid (A ⊎ₛ B)

           A′ = P (pullback ℓ ℓ f i₁)
           B′ = P (pullback ℓ ℓ f i₂)
           A⊎B′ = A′ ⊎ₛ B′
           module A⊎B′ = Setoid A⊎B′
           open SetoidR A⊎B′

         _⊎⟶_ : {o₁ o₂ o₃ ℓ₁ ℓ₂ ℓ₃ : Level} {X : Setoid o₁ ℓ₁} {Y : Setoid o₂ ℓ₂} {Z : Setoid o₃ ℓ₃} →
           (Func X Z) → (Func Y Z) → Func (X ⊎ₛ Y) Z
         f₁ ⊎⟶ f₂ = record
           { to = Sum.[ f₁ ⟨$⟩_ , f₂ ⟨$⟩_ ]
           ; cong = λ { (inj₁ x) → cong f₁ x ; (inj₂ x) → cong f₂ x}
           }

         to-⊎ₛ : (z : ∣ C ∣) → (w : ∣ A ⊎ₛ B ∣) → (eq : [ A⊎B ][ f ⟨$⟩ z ≈ w ]) → ∣ A′ ⊎ₛ B′ ∣
         to-⊎ₛ z (inj₁ x) eq = inj₁ (record { elem₁ = z ; elem₂ = x ; commute = eq })
         to-⊎ₛ z (inj₂ y) eq = inj₂ (record { elem₁ = z ; elem₂ = y ; commute = eq })

         to-⊎ₛ-cong : {z : ∣ C ∣} {w w′ : ∣ A ⊎ₛ B ∣ } → [ A⊎B ][ w ≈ w′ ] →
           {eq : [ A⊎B ][ f ⟨$⟩ z ≈ w ]} → {eq′ : [ A⊎B ][ f ⟨$⟩ z ≈ w′ ]} → [ A⊎B′ ][ to-⊎ₛ z w eq ≈ to-⊎ₛ z w′ eq′ ]
         to-⊎ₛ-cong (inj₁ x) = inj₁ (C.refl , x)
         to-⊎ₛ-cong (inj₂ x) = inj₂ (C.refl , x)

         f⟨$⟩→ : (z : ∣ C ∣) → ∣ A′ ⊎ₛ B′ ∣
         f⟨$⟩→ z = to-⊎ₛ z (f ⟨$⟩ z) A⊎B.refl

         f⟨$⟩-cong′ : {z z′ : ∣ C ∣} → (z≈z′ : [ C ][ z ≈ z′ ]) → (w w′ : ∣ A ⊎ₛ B ∣) →
           [ A⊎B ][ f ⟨$⟩ z ≈ w ] → [ A⊎B ][ f ⟨$⟩ z′ ≈ w′ ] → [ A′ ⊎ₛ B′ ][ f⟨$⟩→ z ≈ f⟨$⟩→ z′ ]
         f⟨$⟩-cong′ {z} {z′} z≈z′ (inj₁ x) (inj₁ x₁) fz≈w fz′≈w′ = begin
           f⟨$⟩→ z                       ≈⟨ A⊎B′.refl ⟩
           to-⊎ₛ z (f ⟨$⟩ z) A⊎B.refl   ≈⟨ to-⊎ₛ-cong fz≈w ⟩
           to-⊎ₛ z (inj₁ x) fz≈w       ≈⟨ inj₁ (z≈z′ , (drop-inj₁ (A⊎B.trans (A⊎B.sym fz≈w) (A⊎B.trans (cong f z≈z′) fz′≈w′)))) ⟩
           to-⊎ₛ z′ (inj₁ x₁) fz′≈w′   ≈⟨ to-⊎ₛ-cong (A⊎B.sym fz′≈w′) ⟩
           to-⊎ₛ z′ (f ⟨$⟩ z′) A⊎B.refl ≈⟨ A⊎B′.refl ⟩
           f⟨$⟩→ z′ ∎
         f⟨$⟩-cong′ z≈z′ (inj₁ x) (inj₂ y) fz≈w fz′≈w′ = conflict A B (A⊎B.trans (A⊎B.sym fz≈w) (A⊎B.trans (cong f z≈z′) fz′≈w′))
         f⟨$⟩-cong′ z≈z′ (inj₂ y) (inj₁ x) fz≈w fz′≈w′ = conflict A B (A⊎B.trans (A⊎B.sym fz′≈w′) (A⊎B.trans (cong f (C.sym z≈z′)) fz≈w))
         f⟨$⟩-cong′ {z} {z′} z≈z′ (inj₂ y) (inj₂ y₁) fz≈w fz′≈w′ = begin
           to-⊎ₛ z (f ⟨$⟩ z) A⊎B.refl   ≈⟨ to-⊎ₛ-cong fz≈w ⟩
           to-⊎ₛ z (inj₂ y) fz≈w       ≈⟨ inj₂ (z≈z′ , (drop-inj₂ (A⊎B.trans (A⊎B.sym fz≈w) (A⊎B.trans (cong f z≈z′) fz′≈w′)))) ⟩
           to-⊎ₛ z′ (inj₂ y₁) fz′≈w′   ≈⟨ to-⊎ₛ-cong (A⊎B.sym fz′≈w′) ⟩
           to-⊎ₛ z′ (f ⟨$⟩ z′) A⊎B.refl ∎

         f⟨$⟩-cong : {i j : ∣ C ∣} → i C.≈ j → [ A′ ⊎ₛ B′ ][ f⟨$⟩→ i ≈ f⟨$⟩→ j ]
         f⟨$⟩-cong {i} {j} i≈j = f⟨$⟩-cong′ i≈j (f ⟨$⟩ i) (f ⟨$⟩ j) A⊎B.refl A⊎B.refl

         f⟨$⟩ : Func C (A′ ⊎ₛ B′)
         f⟨$⟩ = record { to = f⟨$⟩→ ; cong = f⟨$⟩-cong }

         -- copairing of g : A′ → X and h : B′ → X, resulting in C → X
         copair : Func C X
         copair = (g ⊎⟶ h) ∙ f⟨$⟩

         copair-inject₁ : (z : FiberProduct f i₁) → [ X ][ copair ⟨$⟩ (FiberProduct.elem₁ z) ≈ g ⟨$⟩ z ]
         copair-inject₁ record { elem₁ = z ; elem₂ = x ; commute = eq } = cong (g ⊎⟶ h) (to-⊎ₛ-cong eq)

         copair-inject₂ : (z : FiberProduct f i₂) → [ X ][ copair ⟨$⟩ (FiberProduct.elem₁ z) ≈ h ⟨$⟩ z ]
         copair-inject₂ record { elem₁ = z ; elem₂ = y ; commute = eq } = cong (g ⊎⟶ h) (to-⊎ₛ-cong eq)

         copair-unique′ : (u : Func C X) (z : ∣ C ∣) →
           [ A′ ⇨ X ][ u ∙ p₁ (pullback ℓ ℓ f i₁) ≈ g ] →
           [ B′ ⇨ X ][ u ∙ p₁ (pullback ℓ ℓ f i₂) ≈ h ] →
           (w : ∣ A⊎B ∣) → [ A⊎B ][ f ⟨$⟩ z ≈ w ] →
           [ X ][ copair ⟨$⟩ z ≈ u ⟨$⟩ z ]
         copair-unique′ u z feq₁ feq₂ (inj₁ x) fz≈w = XR.begin
           copair ⟨$⟩ z                                XR.≈⟨ X.refl ⟩
           g ⊎⟶ h ⟨$⟩ (to-⊎ₛ z (f ⟨$⟩ z) A⊎B.refl)     XR.≈⟨ cong (g ⊎⟶ h) (to-⊎ₛ-cong fz≈w) ⟩
           g ⊎⟶ h ⟨$⟩ (to-⊎ₛ z (inj₁ x) fz≈w)         XR.≈⟨ X.refl ⟩
           g ⟨$⟩ fb                                    XR.≈⟨ X.sym (feq₁ {x = fb}) ⟩
           u ⟨$⟩ z                                     XR.∎

           where
             module XR = SetoidR X
             fb = record {elem₁ = z ; elem₂ = x; commute = fz≈w }
         copair-unique′ u z feq₁ feq₂ (inj₂ y) fz≈w = XR.begin
           copair ⟨$⟩ z                                XR.≈⟨ X.refl ⟩
           g ⊎⟶ h ⟨$⟩ (to-⊎ₛ z (f ⟨$⟩ z) A⊎B.refl)     XR.≈⟨ cong (g ⊎⟶ h) (to-⊎ₛ-cong fz≈w) ⟩
           g ⊎⟶ h ⟨$⟩ (to-⊎ₛ z (inj₂ y) fz≈w)         XR.≈⟨ X.refl ⟩
           h ⟨$⟩ fb                                    XR.≈⟨ X.sym feq₂ ⟩
           u ⟨$⟩ z                                     XR.∎
           where
             module XR = SetoidR X
             fb = record {elem₁ = z ; elem₂ = y; commute = fz≈w }

         copair-unique : (u : Func C X) (z : ∣ C ∣) →
           [ A′ ⇨ X ][ u ∙ p₁ (pullback ℓ ℓ f i₁) ≈ g ] →
           [ B′ ⇨ X ][ u ∙ p₁ (pullback ℓ ℓ f i₂) ≈ h ] →
           [ X ][ copair ⟨$⟩ z ≈ u ⟨$⟩ z ]
         copair-unique u z feq₁ feq₂ = copair-unique′ u z feq₁ feq₂ (f ⟨$⟩ z) A⊎B.refl

       open Diagram

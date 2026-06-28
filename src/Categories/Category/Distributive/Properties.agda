{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Category.Cocartesian using (Cocartesian)
open import Categories.Category.Distributive using (Distributive)

import Categories.Morphism as M
import Categories.Morphism.Reasoning as MR
import Categories.Morphism.Properties as MP

module Categories.Category.Distributive.Properties {o ℓ e} {𝒞 : Category o ℓ e} (distributive : Distributive 𝒞) where
open Category 𝒞
open M 𝒞
open MR 𝒞
open MP 𝒞
open HomReasoning
open Equiv

open Distributive distributive
open Cartesian cartesian
open Cocartesian cocartesian

-- distribution and injection
distributeˡ⁻¹-i₁ : ∀ {A B C} → distributeˡ⁻¹ {A} {B} {C} ∘ (id ×₁ i₁) ≈ i₁
distributeˡ⁻¹-i₁ = (refl⟩∘⟨ (sym inject₁)) ○ (cancelˡ (IsIso.isoˡ isIsoˡ))

distributeˡ⁻¹-i₂ : ∀ {A B C} → distributeˡ⁻¹ {A} {B} {C} ∘ (id ×₁ i₂) ≈ i₂
distributeˡ⁻¹-i₂ = (refl⟩∘⟨ (sym inject₂)) ○ (cancelˡ (IsIso.isoˡ isIsoˡ))

distributeʳ⁻¹-i₁ : ∀ {A B C} → distributeʳ⁻¹ {A} {B} {C} ∘ (i₁ ×₁ id) ≈ i₁
distributeʳ⁻¹-i₁ = (refl⟩∘⟨ (sym inject₁)) ○ (cancelˡ (IsIso.isoˡ isIsoʳ))

distributeʳ⁻¹-i₂ : ∀ {A B C} → distributeʳ⁻¹ {A} {B} {C} ∘ (i₂ ×₁ id) ≈ i₂
distributeʳ⁻¹-i₂ = (refl⟩∘⟨ (sym inject₂)) ○ (cancelˡ (IsIso.isoˡ isIsoʳ))

-- distribution and projection
distributeˡ⁻¹-π₁ : ∀ {A B C} → [ π₁ , π₁ ] ∘ distributeˡ⁻¹ {A} {B} {C} ≈ π₁
distributeˡ⁻¹-π₁ = sym (begin
  π₁                                                        ≈⟨ introʳ (IsIso.isoʳ isIsoˡ) ⟩
  π₁ ∘ distributeˡ ∘ distributeˡ⁻¹                          ≈⟨ pullˡ ∘[] ⟩
  ([ π₁ ∘ ((id ×₁ i₁)) , π₁ ∘ (id ×₁ i₂) ] ∘ distributeˡ⁻¹) ≈⟨ (([]-cong₂ (π₁∘×₁ ○ identityˡ) (π₁∘×₁ ○ identityˡ)) ⟩∘⟨refl) ⟩
  [ π₁ , π₁ ] ∘ distributeˡ⁻¹                               ∎)

distributeʳ⁻¹-π₁ : ∀ {A B C} → (π₁ +₁ π₁) ∘ distributeʳ⁻¹ {A} {B} {C} ≈ π₁
distributeʳ⁻¹-π₁ = sym (begin
  π₁                                                    ≈⟨ introʳ (IsIso.isoʳ isIsoʳ) ⟩
  π₁ ∘ distributeʳ ∘ distributeʳ⁻¹                      ≈⟨ pullˡ ∘[] ⟩
  [ π₁ ∘ (i₁ ×₁ id) , π₁ ∘ (i₂ ×₁ id) ] ∘ distributeʳ⁻¹ ≈⟨ (([]-cong₂ π₁∘×₁ π₁∘×₁) ⟩∘⟨refl) ⟩
  ((π₁ +₁ π₁) ∘ distributeʳ⁻¹)                          ∎)

distributeˡ⁻¹-π₂ : ∀ {A B C} → (π₂ +₁ π₂) ∘ distributeˡ⁻¹ {A} {B} {C} ≈ π₂
distributeˡ⁻¹-π₂ = sym (begin
  π₂                                                      ≈⟨ introʳ (IsIso.isoʳ isIsoˡ) ⟩
  π₂ ∘ distributeˡ ∘ distributeˡ⁻¹                        ≈⟨ pullˡ ∘[] ⟩
  [ π₂ ∘ ((id ×₁ i₁)) , π₂ ∘ (id ×₁ i₂) ] ∘ distributeˡ⁻¹ ≈⟨ ([]-cong₂ π₂∘×₁ π₂∘×₁) ⟩∘⟨refl ⟩
  (π₂ +₁ π₂) ∘ distributeˡ⁻¹                              ∎)

distributeʳ⁻¹-π₂ : ∀ {A B C} → [ π₂ , π₂ ] ∘ distributeʳ⁻¹ {A} {B} {C} ≈ π₂
distributeʳ⁻¹-π₂ = sym (begin
  π₂                                                        ≈⟨ introʳ (IsIso.isoʳ isIsoʳ) ⟩
  π₂ ∘ distributeʳ ∘ distributeʳ⁻¹                          ≈⟨ pullˡ ∘[] ⟩
  ([ π₂ ∘ ((i₁ ×₁ id)) , π₂ ∘ (i₂ ×₁ id) ] ∘ distributeʳ⁻¹) ≈⟨ (([]-cong₂ (π₂∘×₁ ○ identityˡ) (π₂∘×₁ ○ identityˡ)) ⟩∘⟨refl) ⟩
  [ π₂ , π₂ ] ∘ distributeʳ⁻¹                               ∎)

-- distribute over products
distributeˡ⁻¹-natural : ∀ {X Y Z U V W} (f : X ⇒ U) (g : Y ⇒ V) (h : Z ⇒ W) → ((f ×₁ g) +₁ (f ×₁ h)) ∘ distributeˡ⁻¹ ≈ distributeˡ⁻¹ ∘ (f ×₁ (g +₁ h))
distributeˡ⁻¹-natural f g h = begin
  ((f ×₁ g) +₁ (f ×₁ h)) ∘ distributeˡ⁻¹
    ≈⟨ introˡ (IsIso.isoˡ isIsoˡ) ⟩
  (distributeˡ⁻¹ ∘ distributeˡ) ∘ ((f ×₁ g) +₁ (f ×₁ h)) ∘ distributeˡ⁻¹
    ≈⟨ pullˡ (pullʳ []∘+₁) ⟩
  (distributeˡ⁻¹ ∘ [(id ×₁ i₁) ∘ (f ×₁ g) , (id ×₁ i₂) ∘ (f ×₁ h)]) ∘ distributeˡ⁻¹
    ≈⟨ (refl⟩∘⟨ ([]-cong₂ ×₁∘×₁ ×₁∘×₁)) ⟩∘⟨refl ⟩
  (distributeˡ⁻¹ ∘ [ id ∘ f ×₁ i₁ ∘ g , id ∘ f ×₁ i₂ ∘ h ]) ∘ distributeˡ⁻¹
    ≈˘⟨ (refl⟩∘⟨ ([]-cong₂ (×₁-cong₂ id-comm +₁∘i₁) (×₁-cong₂ id-comm +₁∘i₂))) ⟩∘⟨refl ⟩
  (distributeˡ⁻¹ ∘ [ f ∘ id ×₁ (g +₁ h) ∘ i₁ , f ∘ id ×₁ (g +₁ h) ∘ i₂ ]) ∘ distributeˡ⁻¹
    ≈˘⟨ (refl⟩∘⟨ ([]-cong₂ ×₁∘×₁ ×₁∘×₁)) ⟩∘⟨refl ⟩
  (distributeˡ⁻¹ ∘ [ ((f ×₁ (g +₁ h)) ∘ (id ×₁ i₁)) , ((f ×₁ (g +₁ h)) ∘ (id ×₁ i₂)) ]) ∘ distributeˡ⁻¹
    ≈˘⟨ pullˡ (pullʳ ∘[]) ⟩
  (distributeˡ⁻¹ ∘ (f ×₁ (g +₁ h))) ∘ distributeˡ ∘ distributeˡ⁻¹
    ≈˘⟨ introʳ (IsIso.isoʳ isIsoˡ) ⟩
  distributeˡ⁻¹ ∘ (f ×₁ (g +₁ h))                                                                    
    ∎

distributeʳ⁻¹-natural : ∀ {X Y Z U V W} (f : X ⇒ U) (g : Y ⇒ V) (h : Z ⇒ W) → ((g ×₁ f) +₁ (h ×₁ f)) ∘ distributeʳ⁻¹ ≈ distributeʳ⁻¹ ∘ ((g +₁ h) ×₁ f)
distributeʳ⁻¹-natural f g h = begin
  ((g ×₁ f) +₁ (h ×₁ f)) ∘ distributeʳ⁻¹
    ≈⟨ introˡ (IsIso.isoˡ isIsoʳ) ⟩
  (distributeʳ⁻¹ ∘ distributeʳ) ∘ (g ×₁ f +₁ h ×₁ f) ∘ distributeʳ⁻¹
    ≈⟨ pullˡ (pullʳ []∘+₁) ⟩
  (distributeʳ⁻¹ ∘ [ (i₁ ×₁ id) ∘ (g ×₁ f) , (i₂ ×₁ id) ∘ (h ×₁ f) ]) ∘ distributeʳ⁻¹
    ≈⟨ (refl⟩∘⟨ ([]-cong₂ ×₁∘×₁ ×₁∘×₁)) ⟩∘⟨refl ⟩
  (distributeʳ⁻¹ ∘ [ (i₁ ∘ g ×₁ id ∘ f) , (i₂ ∘ h ×₁ id ∘ f) ]) ∘ distributeʳ⁻¹
    ≈˘⟨ (refl⟩∘⟨ ([]-cong₂ (×₁-cong₂ +₁∘i₁ id-comm) (×₁-cong₂ +₁∘i₂ id-comm))) ⟩∘⟨refl ⟩
  (distributeʳ⁻¹ ∘ [ ((g +₁ h) ∘ i₁ ×₁ f ∘ id) , ((g +₁ h) ∘ i₂ ×₁ f ∘ id) ]) ∘ distributeʳ⁻¹
    ≈˘⟨ (refl⟩∘⟨ ([]-cong₂ ×₁∘×₁ ×₁∘×₁)) ⟩∘⟨refl ⟩
  (distributeʳ⁻¹ ∘ [ ((g +₁ h) ×₁ f) ∘ (i₁ ×₁ id) , ((g +₁ h) ×₁ f) ∘ (i₂ ×₁ id) ]) ∘ distributeʳ⁻¹
    ≈˘⟨ pullˡ (pullʳ ∘[]) ⟩
  (distributeʳ⁻¹ ∘ ((g +₁ h) ×₁ f)) ∘ distributeʳ ∘ distributeʳ⁻¹
    ≈˘⟨ introʳ (IsIso.isoʳ isIsoʳ) ⟩
  distributeʳ⁻¹ ∘ ((g +₁ h) ×₁ f)
    ∎

-- distribute and swap
distributeˡ⁻¹∘swap : ∀ {A B C : Obj} → distributeˡ⁻¹ ∘ swap ≈ (swap +₁ swap) ∘ distributeʳ⁻¹ {A} {B} {C}
distributeˡ⁻¹∘swap = Iso⇒Mono (IsIso.iso isIsoˡ) (distributeˡ⁻¹ ∘ swap) ((swap +₁ swap) ∘ distributeʳ⁻¹) (begin
  (distributeˡ ∘ distributeˡ⁻¹ ∘ swap)                      ≈⟨ cancelˡ (IsIso.isoʳ isIsoˡ) ⟩
  swap                                                      ≈˘⟨ cancelʳ (IsIso.isoʳ isIsoʳ) ⟩
  ((swap ∘ distributeʳ) ∘ distributeʳ⁻¹)                    ≈⟨ ∘[] ⟩∘⟨refl ⟩
  [ swap ∘ (i₁ ×₁ id) , swap ∘ (i₂ ×₁ id) ] ∘ distributeʳ⁻¹ ≈˘⟨ []-cong₂ (sym swap∘×₁) (sym swap∘×₁) ⟩∘⟨refl ⟩
  [ (id ×₁ i₁) ∘ swap , (id ×₁ i₂) ∘ swap ] ∘ distributeʳ⁻¹ ≈˘⟨ pullˡ []∘+₁ ⟩
  distributeˡ ∘ (swap +₁ swap) ∘ distributeʳ⁻¹              ∎)

distributeʳ⁻¹∘swap : ∀ {A B C : Obj} → distributeʳ⁻¹ ∘ swap ≈ (swap +₁ swap) ∘ distributeˡ⁻¹ {A} {B} {C}
distributeʳ⁻¹∘swap = Iso⇒Mono (IsIso.iso isIsoʳ) (distributeʳ⁻¹ ∘ swap) ((swap +₁ swap) ∘ distributeˡ⁻¹) (begin
  (distributeʳ ∘ distributeʳ⁻¹ ∘ swap)                      ≈⟨ cancelˡ (IsIso.isoʳ isIsoʳ) ⟩
  swap                                                      ≈˘⟨ cancelʳ (IsIso.isoʳ isIsoˡ) ⟩
  ((swap ∘ distributeˡ) ∘ distributeˡ⁻¹)                    ≈⟨ (∘[] ⟩∘⟨refl) ⟩
  [ swap ∘ (id ×₁ i₁) , swap ∘ (id ×₁ i₂) ] ∘ distributeˡ⁻¹ ≈˘⟨ ([]-cong₂ (sym swap∘×₁) (sym swap∘×₁)) ⟩∘⟨refl ⟩
  [ (i₁ ×₁ id) ∘ swap , (i₂ ×₁ id) ∘ swap ] ∘ distributeˡ⁻¹ ≈˘⟨ pullˡ []∘+₁ ⟩
  (distributeʳ ∘ (swap +₁ swap) ∘ distributeˡ⁻¹)            ∎)

{-# OPTIONS --without-K --safe #-}
module Categories.Strict.Category.Product.Properties where

-- properties of the product _※_ of Functors (so probably should be renamed?)

open import Level
open import Data.Product
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong₂; subst₂; cong)

open import Categories.Utils.Product
open import Categories.Utils.EqReasoning

open import Categories.Strict.Category
open import Categories.Strict.Functor renaming (id to idF)
-- open import Categories.NaturalTransformation using (NaturalTransformation) renaming (id to idNI)
-- open import Categories.NaturalTransformation.NaturalIsomorphism
open import Categories.Strict.Category.Product
open import Categories.Strict.Morphism

private
  variable
    o ℓ o′ ℓ′ o″ ℓ″ : Level

  ⟺ = sym

-- variables don't work quite right, use anonymous module instead
module _ {A : Category o ℓ} {B : Category o′ ℓ′} {C : Category o″ ℓ″}
         {i : Functor C A} {j : Functor C B} where

  project₁ : πˡ ∘F (i ※ j) ≡F i
  project₁ = λ f → refl , refl

  project₂ : πʳ ∘F (i ※ j) ≡F j
  project₂ = λ _ → refl , refl


  unique : {h : Functor C (Product A B)} →
        πˡ ∘F h ≡F i → πʳ ∘F h ≡F j → (i ※ j) ≡F h
  unique {h} πˡ→i πʳ→j f = pf₁ , pf₂
    where
    open Category
    open Functor
    prod : Obj A × Obj B → Obj A × Obj B → Set (ℓ ⊔ ℓ′)
    prod X Y = zipWith (_⇒_ A) (_⇒_ B) _×_ X Y
    pf₁ : {X : Category.Obj C} → Functor.F₀ h X ≡ (Functor.F₀ i X , Functor.F₀ j X)
    pf₁ {X} = cong₂ _,_ ( sym $ proj₁ (πˡ→i f) {X}) (sym $ proj₁ (πʳ→j f) {X})
    pf₂ : (F₁ i f , F₁ j f) ≡ subst₂ prod pf₁ pf₁ (F₁ h f)
    pf₂ = let open HomReasoning (Product A B) in
          let eq₁ = proj₁ (πˡ→i f) in
          let eq₂ = proj₁ (πʳ→j f) in (begin
      (F₁ i f , F₁ j f)                                       ≡˘⟨ subst₂-subst₂-sym prod pf₁ pf₁ ⟩
      subst₂ prod pf₁ pf₁ (subst₂ prod (sym pf₁) (sym pf₁) _) ≡⟨ cong (subst₂ prod pf₁ pf₁) (subst₂-prod (_⇒_ A) (_⇒_ B) eq₁ eq₁ eq₂ eq₂) ⟩
      subst₂ prod pf₁ pf₁ (subst₂ (_⇒_ A) eq₁ eq₁ (F₁ i f) ,
                           subst₂ (_⇒_ B) eq₂ eq₂ (F₁ j f)) ≡⟨ cong (subst₂ prod pf₁ pf₁) (sym (cong₂ _,_ (proj₂ $ πˡ→i f) (proj₂ $ πʳ→j f))) ⟩
      subst₂ prod pf₁ pf₁ (F₁ h f) ∎)
-- further properties of products
module _ (C : Category o ℓ) (D : Category o′ ℓ′) where

  private
    C×D : Category _ _
    C×D = Product C D
    module C×D = Category C×D
    module C = Category C
    module D = Category D

  -- TODO: write an "essentially-equal" combinator for cases such as these?
  πˡ※πʳ≃id : (πˡ ※ πʳ) ≡F idF {C = C×D}
  πˡ※πʳ≃id = λ f → refl , refl

  ※-distrib : {o₁ ℓ₁ o₂ ℓ₂ : Level} {A : Category o₁ ℓ₁} {B : Category o₂ ℓ₂}
    → (F : Functor B C) → (G : Functor B D) → (H : Functor A B)
    → ((F ∘F H) ※ (G ∘F H)) ≡F ((F ※ G) ∘F H)
  ※-distrib F G H = λ _ → refl , refl

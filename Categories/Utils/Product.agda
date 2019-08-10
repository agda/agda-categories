{-# OPTIONS --without-K --safe #-}
module Categories.Utils.Product where

open import Level
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality

-- "very dependent" versions of map and zipWith
map⁎ : ∀ {a b p q} {A : Set a} {B : A → Set b} {P : A → Set p} {Q : {x : A} → P x → B x → Set q} →
      (f : (x : A) → B x) → (∀ {x} → (y : P x) → Q y (f x)) → (v : Σ A P) → Σ (B (proj₁ v)) (Q (proj₂ v))
map⁎ f g (x , y) = (f x , g y)

map⁎′ : ∀ {a b p q} {A : Set a} {B : A → Set b} {P : Set p} {Q : P → Set q} → (f : (x : A) → B x) → ((x : P) → Q x) → (v : A × P) → B (proj₁ v) × Q (proj₂ v)
map⁎′ f g (x , y) = (f x , g y)

zipWith : ∀ {a b c p q r s} {A : Set a} {B : Set b} {C : Set c} {P : A → Set p} {Q : B → Set q} {R : C → Set r} {S : (x : C) → R x → Set s} (_∙_ : A → B → C) → (_∘_ : ∀ {x y} → P x → Q y → R (x ∙ y)) → (_*_ : (x : C) → (y : R x) → S x y) → (x : Σ A P) → (y : Σ B Q) → S (proj₁ x ∙ proj₁ y) (proj₂ x ∘ proj₂ y)
zipWith _∙_ _∘_ _*_ (a , p) (b , q) = (a ∙ b) * (p ∘ q)
syntax zipWith f g h = f -< h >- g

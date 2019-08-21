{-# OPTIONS --without-K --safe #-}

-- The category of Cats is Monoidal

module Categories.Category.Monoidal.Instance.StrictCats where

open import Level
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; uncurry)
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_; refl; cong₂; sym; module ≡-Reasoning; subst₂; cong)
open import Function using (_$_)
open import Data.Unit using (⊤; tt)

open import Categories.Category
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Category.Instance.StrictCats
open import Categories.Category.Instance.One using (One)
open import Categories.Category.Monoidal
open import Categories.Functor.Bifunctor
open import Categories.Functor.Construction.Constant
open import Categories.Category.Product
open import Categories.Category.Product.Properties
import Categories.Category.Cartesian as Cartesian
open import Categories.Object.Terminal
open import Categories.Utils.Product using (zipWith)
open import Categories.Utils.EqReasoning

-- (Strict) Cats is a (strict) Monoidal Category with Product as Bifunctor
module Product {o ℓ e : Level} where
  private
    C = Cats o ℓ e
    open Cartesian C

  Cats-has-all : BinaryProducts
  Cats-has-all = record { product = λ {A} {B} → record
    { A×B = Product A B
    ; π₁ = πˡ
    ; π₂ = πʳ
    ; ⟨_,_⟩ = _※_
    ; project₁ = (λ _ → ≡.refl) , λ _ → Equiv.refl A
    ; project₂ = (λ _ → ≡.refl) , λ _ → Equiv.refl B
    ; unique = λ {hA} {h} {i} {j} left right →
      let p₁ X = cong₂ _,_ (≡.sym $ proj₁ left X) (≡.sym $ proj₁ right X) in
      p₁ , λ {a} {b} f →
      let la = proj₁ left a in
      let ra = proj₁ right a in
      let lb = proj₁ left b in
      let rb = proj₁ right b in
      let Fi = Functor.F₁ i f in
      let Fj = Functor.F₁ j f in
      let Fh = Functor.F₁ h f in
      let sL X = subst₂ (_⇒_ A) la lb X in
      let sR X = subst₂ (_⇒_ B) ra rb X in
      let ssL X = subst₂ (_⇒_ A) (≡.sym la) (≡.sym lb) X in
      let ssR X = subst₂ (_⇒_ B) (≡.sym ra) (≡.sym rb) X in
      (let open HomReasoning A in begin
      proj₁ (subst₂ (zipWith (_⇒_ A) (_⇒_ B) _×_) (p₁ a) (p₁ b) (Fi , Fj))
          ≈⟨ ≡⇒≈ $ cong proj₁ $ subst₂-expand (_⇒_ A) (_⇒_ B) _ _ _ _ Fi Fj ⟩
      ssL Fi
          ≈˘⟨ subst₂≈ (proj₂ left f) _ _ ⟩
      ssL (sL $ proj₁ Fh)
          ≈⟨ ≡⇒≈ $ subst₂-sym-subst₂ (_⇒_ A) la lb ⟩
      proj₁ Fh ∎) ,
      let open HomReasoning B in begin
      proj₂ (subst₂ (zipWith (_⇒_ A) (_⇒_ B) _×_) (p₁ a) (p₁ b) (Fi , Fj))
          ≈⟨ ≡⇒≈ $ cong proj₂ $ subst₂-expand (_⇒_ A) (_⇒_ B) (≡.sym la) _ _ _ Fi Fj ⟩
      ssR Fj
          ≈˘⟨ subst₂≈ (proj₂ right f) _ _ ⟩
      ssR (sR $ proj₂ Fh)
          ≈⟨ ≡⇒≈ $ subst₂-sym-subst₂ (_⇒_ B) ra rb ⟩
      proj₂ Fh ∎
    } }
    where
    open Category

  private
    unique-One : {l : Level} (x : Lift l ⊤) → lift tt ≡ x
    unique-One (lift tt) = refl

  One-⊤ : Terminal C
  One-⊤ = record
    { ⊤ = One
    ; ! = const (lift tt)
    ; !-unique = λ f → (λ X → unique-One (Functor.F₀ f X)) , λ _ → lift tt
    }

  Cats-is : Cartesian
  Cats-is = record { terminal = One-⊤ ; products = Cats-has-all }

  private
    module Cart = Cartesian.Cartesian Cats-is

  Cats-Monoidal : Monoidal C
  Cats-Monoidal = Cart.monoidal

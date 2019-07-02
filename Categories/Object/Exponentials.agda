{-# OPTIONS --without-K --safe #-}
open import Categories.Category

module Categories.Object.Exponentials {o ℓ e} (𝒞 : Category o ℓ e) where

open Category 𝒞

open import Level
open import Data.Product using (Σ; _,_; uncurry)

open import Categories.Functor
open import Categories.Object.Product 𝒞
  hiding (repack; repack≡id; repack∘; repack-cancel; up-to-iso; transport-by-iso)
open import Categories.Object.Exponential 𝒞
open import Categories.Square 𝒞

open HomReasoning

private
  variable
    A B C : Obj
    f g   : A ⇒ B

record Exponentials : Set (o ⊔ ℓ ⊔ e) where
  infixl 7 _^_
  
  field
    exp : Exponential A B

  module exp {A B} = Exponential (exp {A} {B})

  _^_ : Obj → Obj → Obj
  B ^ A = exp.B^A {A} {B}

  product : ∀ B A → Product (B ^ A) A
  product B A = exp.product {A} {B}

  eval : Product.A×B (product B A) ⇒ B
  eval = exp.eval

  λg : Product.A×B (product C A) ⇒ B → C ^ A ⇒ B ^ A
  λg f = exp.λg exp.product f

  λ-cong : f ≈ g → λg f ≈ λg g
  λ-cong eq = exp.λ-cong exp.product eq

  _×id : (f : B ^ A ⇒ C ^ A) → [[ product B A ]] ⇒ [[ product C A ]]
  f ×id = [ exp.product ⇒ exp.product ] f ×id

  β : eval ∘ λg f ×id ≈ f
  β = exp.β exp.product

  -^-functor : Obj → Functor 𝒞 𝒞
  -^-functor A = record
    { F₀           = _^ A
    ; F₁           = λ f → λg (f ∘ eval)
    ; identity     = trans (λ-cong identityˡ) exp.η-id
    ; homomorphism = exp.λ-unique′ exp.product homoeq
    ; F-resp-≈     = λ eq → λ-cong (∘-resp-≈ˡ eq)
    }
    where homoeq : eval {A = A} ∘ (λg ((g ∘ f) ∘ eval) ×id) ≈ eval ∘ ((λg (g ∘ eval) ∘ λg (f ∘ eval)) ×id)
          homoeq {g = g} {f = f} = begin
            eval ∘ (λg ((g ∘ f) ∘ eval) ×id)               ≈⟨ β ⟩
            (g ∘ f) ∘ eval                                 ≈⟨ pullʳ (sym β) ⟩
            g ∘ eval ∘ λg (f ∘ eval) ×id                   ≈⟨ pullˡ (sym β) ⟩
            (eval ∘ λg (g ∘ eval) ×id) ∘ λg (f ∘ eval) ×id ≈⟨ pullʳ [ exp.product ⇒ exp.product ⇒ exp.product ]×id∘×id ⟩
            eval ∘ ((λg (g ∘ eval) ∘ λg (f ∘ eval)) ×id)   ∎

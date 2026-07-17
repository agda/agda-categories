{-# OPTIONS --without-K --safe #-}
open import Categories.Category

-- Exponential Object

-- NOTE: when working in a cartesian category, 
-- you probably want to use Categories.Object.Exponential.Canonical

module Categories.Object.Exponential {o ℓ e} (𝒞 : Category o ℓ e) where

open Category 𝒞

open import Level
open import Function using (_$_)

open import Categories.Morphism.Reasoning 𝒞
open import Categories.Object.Product 𝒞
  hiding (repack; repack≡id; repack∘; repack-cancel; up-to-iso; transport-by-iso)
open import Categories.Morphism 𝒞

open HomReasoning

private
  variable
    A B C D X Y : Obj

record Exponential (A B : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    B^A : Obj
    product : Product B^A A

  module product = Product product

  B^A×A : Obj
  B^A×A = product.A×B

  field
    eval     : B^A×A ⇒ B
    λg       : ∀ (X×A : Product X A) → (Product.A×B X×A ⇒ B) → (X ⇒ B^A)
    β        : ∀ (X×A : Product X A) {g : Product.A×B X×A ⇒ B} →
                 (eval ∘ [ X×A ⇒ product ] λg X×A g ×id ≈ g)
    λ-unique : ∀ (X×A : Product X A) {g : Product.A×B X×A ⇒ B} {h : X ⇒ B^A} →
                 (eval ∘ [ X×A ⇒ product ] h ×id ≈ g) → (h ≈ λg X×A g)

  η : ∀ (X×A : Product X A) {f : X ⇒ B^A } → λg X×A (eval ∘ [ X×A ⇒ product ] f ×id) ≈ f
  η X×A {f} = ⟺ (λ-unique X×A Equiv.refl)

  λ-cong : ∀ {X : Obj} (X×A : Product X A) {f g} →
             f ≈ g → λg X×A f ≈ λg X×A g
  λ-cong X×A {f = f} {g = g} f≡g = λ-unique X×A (β X×A ○ f≡g)

  λ-inj : ∀ {X : Obj} (X×A : Product X A) {f g} → λg X×A f ≈ λg X×A g → f ≈ g
  λ-inj X×A {f = f} {g = g} eq = begin
    f                                      ≈˘⟨ β X×A ⟩
    eval ∘ [ X×A ⇒ product ] λg X×A f ×id  ≈⟨ refl⟩∘⟨ [ X×A ⇒ product  ]×-cong₂ eq Equiv.refl ⟩
    eval ∘ [ X×A ⇒ product ] λg X×A g × id ≈⟨ β X×A ⟩
    g                                      ∎

  subst : ∀ (p₂ : Product C A) (p₃ : Product D A) {f g} →
            λg p₃ f ∘ g ≈ λg p₂ (f ∘ [ p₂ ⇒ p₃ ] g ×id)
  subst p₂ p₃ {f} {g} = λ-unique p₂ (begin
    eval ∘ [ p₂ ⇒ product ] λg p₃ f ∘ g ×id
                           ≈˘⟨ refl⟩∘⟨ [ p₂ ⇒ p₃ ⇒ product ]×id∘×id ⟩
    eval ∘ [ p₃ ⇒ product ] λg p₃ f ×id ∘ [ p₂ ⇒ p₃ ] g ×id
                           ≈⟨ pullˡ (β p₃) ⟩
    f ∘ [ p₂ ⇒ p₃ ] g ×id ∎)

  η-id : λg product eval ≈ id
  η-id = begin
    λg product eval                                  ≈˘⟨ identityʳ ⟩
    λg product eval ∘ id                             ≈⟨ subst _ _ ⟩
    λg product (eval ∘ [ product ⇒ product ] id ×id) ≈⟨ η product ⟩
    id                                               ∎

  λ-unique′ : ∀ (X×A : Product X A) {h i : X ⇒ B^A} →
                eval ∘ [ X×A ⇒ product ] h ×id ≈ eval ∘ [ X×A ⇒ product ] i ×id → h ≈ i
  λ-unique′ p eq = λ-unique p eq ○ (⟺ (λ-unique p Equiv.refl))

-- some aliases to make proof signatures less ugly
[_]eval : ∀{A B}(e₁ : Exponential A B) → Exponential.B^A×A e₁ ⇒ B
[ e₁ ]eval = Exponential.eval e₁

[_]λ : ∀{A B}(e₁ : Exponential A B)
  → {X : Obj} → (X×A : Product X A) → (Product.A×B X×A ⇒ B) → (X ⇒ Exponential.B^A e₁)
[ e₁ ]λ = Exponential.λg e₁

{-
   D×C --id × f--> D×A --g--> B

   D --λ (g ∘ id × f)--> B^C
    \                   ^
     \                 /
     λ g       λ (e ∘ id × f)
       \        /
        v      /
          B^A
-}
λ-distrib : ∀ (e₁ : Exponential C B) (e₂ : Exponential A B)
              (p₃ : Product D C) (p₄ : Product D A) (p₅ : Product (Exponential.B^A e₂) C)
              {f} {g : Product.A×B p₄ ⇒ B} →
              [ e₁ ]λ p₃ (g ∘ [ p₃ ⇒ p₄ ]id× f)
              ≈ [ e₁ ]λ p₅ ([ e₂ ]eval ∘ [ p₅ ⇒ Exponential.product e₂ ]id× f) ∘ [ e₂ ]λ p₄ g
λ-distrib e₁ e₂ p₃ p₄ p₅ {f} {g} = ⟺ $ e₁.λ-unique p₃ $ begin
  [ e₁ ]eval ∘ ([ p₃ ⇒ p₁ ] [ e₁ ]λ p₅ ([ e₂ ]eval ∘ [ p₅ ⇒ p₂ ]id× f) ∘ [ e₂ ]λ p₄ g ×id)
                       ≈˘⟨ refl⟩∘⟨ [ p₃ ⇒ p₅ ⇒ p₁ ]×id∘×id ⟩
  [ e₁ ]eval ∘ [ p₅ ⇒ p₁ ] [ e₁ ]λ p₅ ([ e₂ ]eval ∘ [ p₅ ⇒ p₂ ]id× f) ×id
             ∘ [ p₃ ⇒ p₅ ] [ e₂ ]λ p₄ g ×id
                       ≈⟨ pullˡ (e₁.β p₅) ⟩
  ([ e₂ ]eval ∘ [ p₅ ⇒ p₂ ]id× f)
              ∘ [ p₃ ⇒ p₅ ] [ e₂ ]λ p₄ g ×id
                       ≈⟨ assoc ⟩
  [ e₂ ]eval ∘ [ p₅ ⇒ p₂ ]id× f
             ∘ [ p₃ ⇒ p₅ ] [ e₂ ]λ p₄ g ×id
                       ≈˘⟨ refl⟩∘⟨ [ p₄ ⇒ p₂ , p₃ ⇒ p₅ ]first↔second ⟩
  [ e₂ ]eval ∘ [ p₄ ⇒ p₂ ] [ e₂ ]λ p₄ g ×id ∘ [ p₃ ⇒ p₄ ]id× f
                       ≈⟨ pullˡ (e₂.β p₄) ⟩
  g ∘ [ p₃ ⇒ p₄ ]id× f ∎
  where module e₁ = Exponential e₁
        module e₂ = Exponential e₂
        p₁        = e₁.product
        p₂        = e₂.product

repack : ∀{A B} (e₁ e₂ : Exponential A B) → Exponential.B^A e₁ ⇒ Exponential.B^A e₂
repack e₁ e₂ = e₂.λg e₁.product e₁.eval
  where
    module e₁ = Exponential e₁
    module e₂ = Exponential e₂

repack≡id : ∀{A B} (e : Exponential A B) → repack e e ≈ id
repack≡id = Exponential.η-id

repack∘ : ∀ (e₁ e₂ e₃ : Exponential A B) → repack e₂ e₃ ∘ repack e₁ e₂ ≈ repack e₁ e₃
repack∘ e₁ e₂ e₃ =
  let p₁ = product e₁ in
  let p₂ = product e₂ in
  begin
      [ e₃ ]λ p₂ [ e₂ ]eval
    ∘ [ e₂ ]λ p₁ [ e₁ ]eval
  ≈⟨ λ-cong e₃ p₂ (introʳ (second-id p₂)) ⟩∘⟨refl ⟩
      [ e₃ ]λ p₂ ([ e₂ ]eval ∘ [ p₂ ⇒ p₂ ]id× id)
    ∘ [ e₂ ]λ p₁ [ e₁ ]eval
  ≈˘⟨ λ-distrib e₃ e₂ p₁ p₁ p₂ ⟩
    [ e₃ ]λ p₁ ([ e₁ ]eval ∘ [ p₁ ⇒ p₁ ]id× id)
  ≈⟨ λ-cong e₃ p₁ (⟺ (introʳ (second-id (product e₁)))) ⟩
    [ e₃ ]λ p₁ [ e₁ ]eval
  ∎
  where open Exponential

repack-cancel : ∀{A B} (e₁ e₂ : Exponential A B) → repack e₁ e₂ ∘ repack e₂ e₁ ≈ id
repack-cancel e₁ e₂ = repack∘ e₂ e₁ e₂ ○ repack≡id e₂

up-to-iso : ∀{A B} (e₁ e₂ : Exponential A B) → Exponential.B^A e₁ ≅ Exponential.B^A e₂
up-to-iso e₁ e₂ = record
  { from = repack e₁ e₂
  ; to   = repack e₂ e₁
  ; iso  = record
    { isoˡ = repack-cancel e₂ e₁
    ; isoʳ = repack-cancel e₁ e₂
    }
  }

transport-by-iso : ∀ (e : Exponential A B) → Exponential.B^A e ≅ X → Exponential A B
transport-by-iso {X = X} e e≅X = record
  { B^A             = X
  ; product         = X×A
  ; eval            = e.eval
  ; λg              = λ Y×A Y×A⇒B → from ∘ (e.λg Y×A Y×A⇒B)
  ; β               = λ Y×A {h} → begin
    e.eval ∘ [ Y×A ⇒ X×A ] from ∘ e.λg Y×A h ×id ≈⟨ refl⟩∘⟨ e.product.⟨⟩-cong₂ (pullˡ (cancelˡ isoˡ))
                                                                              (elimˡ Equiv.refl) ⟩
    e.eval ∘ [ Y×A ⇒ e.product ] e.λg Y×A h ×id  ≈⟨ e.β Y×A ⟩
    h                                            ∎
  ; λ-unique        = λ Y×A {h} {i} eq →
    switch-tofromˡ e≅X $ e.λ-unique Y×A $ begin
      e.eval ∘ [ Y×A ⇒ e.product ] to ∘ i ×id    ≈⟨ refl⟩∘⟨ e.product.⟨⟩-cong₂ assoc (introˡ Equiv.refl) ⟩
      e.eval ∘ [ Y×A ⇒ X×A ] i ×id               ≈⟨ eq ⟩
      h                                          ∎
  }
  where module e = Exponential e
        X×A      = Mobile e.product e≅X ≅.refl
        open _≅_ e≅X

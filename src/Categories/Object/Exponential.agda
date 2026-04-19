{-# OPTIONS --without-K --safe #-}
open import Categories.Category

-- Exponential Object

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

record Exponential (A B : Obj) (products : ∀ C → Product C A) : Set (o ⊔ ℓ ⊔ e) where
  field
    B^A : Obj

  module product {X} = Product (products X)

  private 
    _×A : Obj → Obj
    X ×A = product.A×B {X}

    _⁂id : ∀ {X Y : Obj} (f : X ⇒ Y) → (X ×A) ⇒ (Y ×A)
    _⁂id {X} {Y} f = [ products X ⇒ products Y ] f × id 

  field
    eval     : B^A ×A ⇒ B
    λg       : (X ×A ⇒ B) → (X ⇒ B^A)
    β        : ∀ {g : X ×A ⇒ B} → eval ∘ (λg g ⁂id) ≈ g
    λ-unique : ∀ {g : X ×A ⇒ B} {h : X ⇒ B^A} →
                 (eval ∘ (h ⁂id) ≈ g) → (h ≈ λg g)

  η : ∀ {f : X ⇒ B^A } → λg (eval ∘ f ⁂id) ≈ f
  η {f} = ⟺ (λ-unique Equiv.refl)

  λ-cong : ∀ {X : Obj} {f g : X ×A ⇒ B} →
             f ≈ g → λg f ≈ λg g
  λ-cong {f = f} {g = g} f≡g = λ-unique (β ○ f≡g)

  λ-inj : ∀ {X : Obj} {f g : X ×A ⇒ B} → λg f ≈ λg g → f ≈ g
  λ-inj {X} {f = f} {g = g} eq = begin
    f                                      ≈˘⟨ β ⟩
    eval ∘ λg f ⁂id                        ≈⟨ refl⟩∘⟨ [ products X ⇒ products B^A  ]×-cong₂ eq Equiv.refl ⟩
    eval ∘ λg g ⁂id                        ≈⟨ β ⟩
    g                                      ∎

  subst : ∀ {Z} {f : B^A ×A ⇒ B} {g : Z ⇒ B^A} →
            λg f ∘ g ≈ λg (f ∘ (g ⁂id))
  subst {Z} {f} {g} = λ-unique (begin
    eval ∘ (λg f ∘ g) ⁂id
                           ≈˘⟨ refl⟩∘⟨ [ products Z ⇒ products B^A ⇒ products B^A ]×id∘×id ⟩
    eval ∘ λg f ⁂id ∘ g ⁂id
                           ≈⟨ pullˡ β ⟩
    f ∘ g ⁂id ∎)

  η-id : λg eval ≈ id
  η-id = begin
    λg eval            ≈˘⟨ identityʳ ⟩
    λg eval ∘ id       ≈⟨ subst ⟩
    λg (eval ∘ id ⁂id) ≈⟨ η ⟩
    id                 ∎

  λ-unique′ : ∀ {h i : X ⇒ B^A} →
                eval ∘ h ⁂id ≈ eval ∘ i ⁂id → h ≈ i
  λ-unique′ eq = λ-unique eq ○ (⟺ (λ-unique Equiv.refl))

-- -- some aliases to make proof signatures less ugly
-- [_]eval : ∀{A B}(e₁ : Exponential A B) → ? ⇒ B
-- [ e₁ ]eval = Exponential.eval e₁

-- [_]λ : ∀{A B}(e₁ : Exponential A B)
--   → {X : Obj} → (X×A : Product X A) → (Product.A×B X×A ⇒ B) → (X ⇒ Exponential.B^A e₁)
-- [ e₁ ]λ = Exponential.λg e₁

-- {-
--    D×C --id × f--> D×A --g--> B

--    D --λ (g ∘ id × f)--> B^C
--     \                   ^
--      \                 /
--      λ g       λ (e ∘ id × f)
--        \        /
--         v      /
--           B^A
-- -}
-- λ-distrib : ∀ (e₁ : Exponential C B) (e₂ : Exponential A B)
--               (p₃ : Product D C) (p₄ : Product D A) (p₅ : Product (Exponential.B^A e₂) C)
--               {f} {g : Product.A×B p₄ ⇒ B} →
--               [ e₁ ]λ p₃ (g ∘ [ p₃ ⇒ p₄ ]id× f)
--               ≈ [ e₁ ]λ p₅ ([ e₂ ]eval ∘ [ p₅ ⇒ Exponential.product e₂ ]id× f) ∘ [ e₂ ]λ p₄ g
-- λ-distrib e₁ e₂ p₃ p₄ p₅ {f} {g} = ⟺ $ e₁.λ-unique p₃ $ begin
--   [ e₁ ]eval ∘ ([ p₃ ⇒ p₁ ] [ e₁ ]λ p₅ ([ e₂ ]eval ∘ [ p₅ ⇒ p₂ ]id× f) ∘ [ e₂ ]λ p₄ g ×id)
--                        ≈˘⟨ refl⟩∘⟨ [ p₃ ⇒ p₅ ⇒ p₁ ]×id∘×id ⟩
--   [ e₁ ]eval ∘ [ p₅ ⇒ p₁ ] [ e₁ ]λ p₅ ([ e₂ ]eval ∘ [ p₅ ⇒ p₂ ]id× f) ×id
--              ∘ [ p₃ ⇒ p₅ ] [ e₂ ]λ p₄ g ×id
--                        ≈⟨ pullˡ (e₁.β p₅) ⟩
--   ([ e₂ ]eval ∘ [ p₅ ⇒ p₂ ]id× f)
--               ∘ [ p₃ ⇒ p₅ ] [ e₂ ]λ p₄ g ×id
--                        ≈⟨ assoc ⟩
--   [ e₂ ]eval ∘ [ p₅ ⇒ p₂ ]id× f
--              ∘ [ p₃ ⇒ p₅ ] [ e₂ ]λ p₄ g ×id
--                        ≈˘⟨ refl⟩∘⟨ [ p₄ ⇒ p₂ , p₃ ⇒ p₅ ]first↔second ⟩
--   [ e₂ ]eval ∘ [ p₄ ⇒ p₂ ] [ e₂ ]λ p₄ g ×id ∘ [ p₃ ⇒ p₄ ]id× f
--                        ≈⟨ pullˡ (e₂.β p₄) ⟩
--   g ∘ [ p₃ ⇒ p₄ ]id× f ∎
--   where module e₁ = Exponential e₁
--         module e₂ = Exponential e₂
--         p₁        = e₁.product
--         p₂        = e₂.product

-- repack : ∀{A B} (e₁ e₂ : Exponential A B) → Exponential.B^A e₁ ⇒ Exponential.B^A e₂
-- repack e₁ e₂ = e₂.λg e₁.product e₁.eval
--   where
--     module e₁ = Exponential e₁
--     module e₂ = Exponential e₂

-- repack≡id : ∀{A B} (e : Exponential A B) → repack e e ≈ id
-- repack≡id = Exponential.η-id

-- repack∘ : ∀ (e₁ e₂ e₃ : Exponential A B) → repack e₂ e₃ ∘ repack e₁ e₂ ≈ repack e₁ e₃
-- repack∘ e₁ e₂ e₃ =
--   let p₁ = product e₁ in
--   let p₂ = product e₂ in
--   begin
--       [ e₃ ]λ p₂ [ e₂ ]eval
--     ∘ [ e₂ ]λ p₁ [ e₁ ]eval
--   ≈⟨ λ-cong e₃ p₂ (introʳ (second-id p₂)) ⟩∘⟨refl ⟩
--       [ e₃ ]λ p₂ ([ e₂ ]eval ∘ [ p₂ ⇒ p₂ ]id× id)
--     ∘ [ e₂ ]λ p₁ [ e₁ ]eval
--   ≈˘⟨ λ-distrib e₃ e₂ p₁ p₁ p₂ ⟩
--     [ e₃ ]λ p₁ ([ e₁ ]eval ∘ [ p₁ ⇒ p₁ ]id× id)
--   ≈⟨ λ-cong e₃ p₁ (⟺ (introʳ (second-id (product e₁)))) ⟩
--     [ e₃ ]λ p₁ [ e₁ ]eval
--   ∎
--   where open Exponential

-- repack-cancel : ∀{A B} (e₁ e₂ : Exponential A B) → repack e₁ e₂ ∘ repack e₂ e₁ ≈ id
-- repack-cancel e₁ e₂ = repack∘ e₂ e₁ e₂ ○ repack≡id e₂

-- up-to-iso : ∀{A B} (e₁ e₂ : Exponential A B) → Exponential.B^A e₁ ≅ Exponential.B^A e₂
-- up-to-iso e₁ e₂ = record
--   { from = repack e₁ e₂
--   ; to   = repack e₂ e₁
--   ; iso  = record
--     { isoˡ = repack-cancel e₂ e₁
--     ; isoʳ = repack-cancel e₁ e₂
--     }
--   }

-- transport-by-iso : ∀ (e : Exponential A B) → Exponential.B^A e ≅ X → Exponential A B
-- transport-by-iso {X = X} e e≅X = record
--   { B^A             = X
--   ; product         = X×A
--   ; eval            = e.eval
--   ; λg              = λ Y×A Y×A⇒B → from ∘ (e.λg Y×A Y×A⇒B)
--   ; β               = λ Y×A {h} → begin
--     e.eval ∘ [ Y×A ⇒ X×A ] from ∘ e.λg Y×A h ×id ≈⟨ refl⟩∘⟨ e.product.⟨⟩-cong₂ (pullˡ (cancelˡ isoˡ))
--                                                                               (elimˡ Equiv.refl) ⟩
--     e.eval ∘ [ Y×A ⇒ e.product ] e.λg Y×A h ×id  ≈⟨ e.β Y×A ⟩
--     h                                            ∎
--   ; λ-unique        = λ Y×A {h} {i} eq →
--     switch-tofromˡ e≅X $ e.λ-unique Y×A $ begin
--       e.eval ∘ [ Y×A ⇒ e.product ] to ∘ i ×id    ≈⟨ refl⟩∘⟨ e.product.⟨⟩-cong₂ assoc (introˡ Equiv.refl) ⟩
--       e.eval ∘ [ Y×A ⇒ X×A ] i ×id               ≈⟨ eq ⟩
--       h                                          ∎
--   }
--   where module e = Exponential e
--         X×A      = Mobile e.product e≅X ≅.refl
--         open _≅_ e≅X

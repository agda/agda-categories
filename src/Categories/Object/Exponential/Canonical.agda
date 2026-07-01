{-# OPTIONS --without-K --safe #-}
open import Categories.Category.Core
open import Categories.Category.Cartesian using (Cartesian)

-- Exponential Objects in a Cartesian Category

module Categories.Object.Exponential.Canonical {o ℓ e} {𝒞 : Category o ℓ e} (cartesian : Cartesian 𝒞) where

open Category 𝒞
open Cartesian cartesian using (_×_; _×₁_; ×₁-cong₂; ×₁∘×₁; first↔second; unique; ⟨⟩-cong₂; ⟨_,_⟩; π₁; π₂; id×₁id)

open import Level

open import Categories.Morphism.Reasoning 𝒞
open import Categories.Morphism 𝒞

open HomReasoning
open Equiv

private
  variable
    A B C D X Y : Obj

record Exponential (A B : Obj) : Set (o ⊔ ℓ ⊔ e) where
  field
    B^A : Obj

  field
    eval     : B^A × A ⇒ B
    λg       : (X × A ⇒ B) → (X ⇒ B^A)
    β        : {g : X × A ⇒ B} →
                 (eval ∘ (λg g ×₁ id) ≈ g)
    λ-unique : ∀ {g : X × A ⇒ B} {h : X ⇒ B^A} →
                 (eval ∘ (h ×₁ id) ≈ g) → (h ≈ λg g)

  η : ∀ {f : X ⇒ B^A} → λg (eval ∘ (f ×₁ id)) ≈ f
  η = ⟺ (λ-unique refl)

  λ-cong : ∀ {f g : X × A ⇒ B} → f ≈ g → λg f ≈ λg g
  λ-cong {f = f} {g = g} f≡g = λ-unique (β ○ f≡g)

  λ-inj : ∀ {f g : X × A ⇒ B} → λg f ≈ λg g → f ≈ g
  λ-inj {f = f} {g = g} eq = begin
    f                   ≈˘⟨ β ⟩
    eval ∘ (λg f ×₁ id) ≈⟨ refl⟩∘⟨ ×₁-cong₂ eq refl ⟩
    eval ∘ (λg g ×₁ id) ≈⟨ β ⟩
    g                   ∎

  subst : {f : X × A ⇒ B} {g : Y ⇒ X} → λg f ∘ g ≈ λg (f ∘ (g ×₁ id))
  subst {f = f} {g = g} = λ-unique (begin
    eval ∘ (λg f ∘ g ×₁ id)         ≈˘⟨ refl⟩∘⟨ (×₁∘×₁ ○ ×₁-cong₂ refl identityʳ) ⟩
    eval ∘ (λg f ×₁ id) ∘ (g ×₁ id) ≈⟨ pullˡ β ⟩
    f ∘ (g ×₁ id)                   ∎)

  η-id : λg eval ≈ id
  η-id = begin
    λg eval                ≈˘⟨ identityʳ ⟩
    λg eval ∘ id           ≈⟨ subst ⟩
    λg (eval ∘ (id ×₁ id)) ≈⟨ η ⟩
    id                     ∎

  λ-unique′ : ∀ {h i : X ⇒ B^A} →
                eval ∘ (h ×₁ id) ≈ eval ∘ (i ×₁ id) → h ≈ i
  λ-unique′ eq = λ-unique eq ○ (⟺ (λ-unique refl))

-- aliases for working with multiple exponentials
[_]eval : ∀{A B} (e₁ : Exponential A B) → Exponential.B^A e₁ × A ⇒ B
[ e₁ ]eval = Exponential.eval e₁

[_]λ : ∀{A B} (e₁ : Exponential A B)
  → {X : Obj} → (X × A ⇒ B) → (X ⇒ Exponential.B^A e₁)
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
              {f} {g : D × A ⇒ B} →
              [ e₁ ]λ  (g ∘ (id ×₁ f))
              ≈ [ e₁ ]λ ([ e₂ ]eval ∘ (id ×₁ f)) ∘ [ e₂ ]λ g
λ-distrib e₁ e₂ {f} {g} = ⟺ (e₁.λ-unique (begin 
  e₁.eval ∘ (e₁.λg (e₂.eval ∘ (id ×₁ f)) ∘ e₂.λg g ×₁ id)         ≈˘⟨ refl⟩∘⟨ (×₁∘×₁ ○ ×₁-cong₂ refl identity²) ⟩ 
  e₁.eval ∘ (e₁.λg (e₂.eval ∘ (id ×₁ f)) ×₁ id) ∘ (e₂.λg g ×₁ id) ≈⟨ pullˡ e₁.β ⟩ 
  (e₂.eval ∘ (id ×₁ f)) ∘ (e₂.λg g ×₁ id)                         ≈⟨ assoc ⟩ 
  e₂.eval ∘ (id ×₁ f) ∘ (e₂.λg g ×₁ id)                           ≈˘⟨ refl⟩∘⟨ first↔second ⟩ 
  e₂.eval ∘ (e₂.λg g ×₁ id) ∘ (id ×₁ f)                           ≈⟨ pullˡ e₂.β ⟩ 
  g ∘ (id ×₁ f)                                                   ∎))
  where module e₁ = Exponential e₁
        module e₂ = Exponential e₂

repack : ∀ {A B} (e₁ e₂ : Exponential A B) → Exponential.B^A e₁ ⇒ Exponential.B^A e₂
repack e₁ e₂ = e₂.λg e₁.eval
  where
    module e₁ = Exponential e₁
    module e₂ = Exponential e₂

repack≡id : ∀{A B} (e : Exponential A B) → repack e e ≈ id
repack≡id = Exponential.η-id

repack∘ : ∀ (e₁ e₂ e₃ : Exponential A B) → repack e₂ e₃ ∘ repack e₁ e₂ ≈ repack e₁ e₃
repack∘ e₁ e₂ e₃ =
  begin
      [ e₃ ]λ [ e₂ ]eval
    ∘ [ e₂ ]λ [ e₁ ]eval
  ≈⟨ λ-cong e₃ (introʳ (id×₁id)) ⟩∘⟨refl ⟩
      [ e₃ ]λ ([ e₂ ]eval ∘ (id ×₁ id))
    ∘ [ e₂ ]λ [ e₁ ]eval
  ≈˘⟨ λ-distrib e₃ e₂ ⟩
    [ e₃ ]λ  ([ e₁ ]eval ∘ (id ×₁ id))
  ≈⟨ λ-cong e₃ (⟺ (introʳ (id×₁id))) ⟩
    [ e₃ ]λ [ e₁ ]eval
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
  ; eval            = e.eval ∘ (to ×₁ id)
  ; λg              = λ g → from ∘ e.λg g
  ; β               = λ {g = g} → begin  
    (e.eval ∘ (to ×₁ id)) ∘ (from ∘ e.λg g ×₁ id) ≈⟨ pullʳ (×₁∘×₁ ○ ×₁-cong₂ (cancelˡ isoˡ) identity²) ⟩
    e.eval ∘ (e.λg g ×₁ id)                       ≈⟨ e.β ⟩ 
    g                                             ∎
  ; λ-unique        = λ {g = g} {h = h} eq → switch-tofromˡ e≅X (e.λ-unique (begin 
    e.eval ∘ (to ∘ h ×₁ id)           ≈˘⟨ pullʳ (×₁∘×₁ ○ ×₁-cong₂ refl identity²) ⟩ 
    (e.eval ∘ (to ×₁ id)) ∘ (h ×₁ id) ≈⟨ eq ⟩
    g                                 ∎))
  }
  where module e = Exponential e
        open _≅_ e≅X

{-# OPTIONS --without-K --safe #-}
-- Various operations and proofs on morphisms between products

-- Perhaps a bit of overkill? There is so much here that it's impossible to remember
-- it all
open import Categories.Category

module Categories.Object.Product.Morphisms {o ℓ e} (𝒞 : Category o ℓ e) where

open import Function using (flip)
open import Level

open import Categories.Object.Product.Core 𝒞

open Category 𝒞
open HomReasoning

private
  variable
    A B C D E F : Obj
    f f′ g g′ h i : A ⇒ B

infix 10 [_]⟨_,_⟩ [_⇒_]_×_
infix 12 [[_]] [_]π₁ [_]π₂

[[_]] : Product A B → Obj
[[ p ]] = Product.A×B p

[_]⟨_,_⟩ : ∀ (p : Product B C) → A ⇒ B → A ⇒ C → A ⇒ [[ p ]]
[ p ]⟨ f , g ⟩ = Product.⟨_,_⟩ p f g

[_]π₁ : ∀ (p : Product A B) → [[ p ]] ⇒ A
[_]π₁ = Product.π₁

[_]π₂ : ∀ (p : Product A B) → [[ p ]] ⇒ B
[_]π₂ = Product.π₂

[_⇒_]_×_ : ∀ (p₁ : Product A C) (p₂ : Product B D) →
             (A ⇒ B) → (C ⇒ D) → ([[ p₁ ]] ⇒ [[ p₂ ]])
[ p₁ ⇒ p₂ ] f × g  = [ p₂ ]⟨ f ∘ p₁.π₁ , g ∘ p₁.π₂ ⟩
  where module p₁ = Product p₁
        module p₂ = Product p₂

id×id : ∀ (p : Product A B) → [ p ⇒ p ] id × id ≈ id
id×id p = begin
  ⟨ id ∘ π₁ , id ∘ π₂ ⟩ ≈⟨ ⟨⟩-cong₂ identityˡ identityˡ ⟩
  ⟨ π₁ , π₂ ⟩           ≈⟨ η ⟩
  id                    ∎
  where open Product p

repack≡id×id : ∀ (p₁ p₂ : Product A B) → repack p₁ p₂ ≈ [ p₁ ⇒ p₂ ] id × id
repack≡id×id p₁ p₂ = ⟺ (Product.⟨⟩-cong₂ p₂ identityˡ identityˡ)

[_⇒_]π₁∘× : ∀ (p₁ : Product A C)(p₂ : Product B D) →
              Product.π₁ p₂ ∘ [ p₁ ⇒ p₂ ] f × g ≈ f ∘ Product.π₁ p₁
[_⇒_]π₁∘× _ p₂ = Product.project₁ p₂

[_⇒_]π₂∘× : ∀ (p₁ : Product A C) (p₂ : Product B D) →
              Product.π₂ p₂ ∘ [ p₁ ⇒ p₂ ] f × g ≈ g ∘ Product.π₂ p₁
[_⇒_]π₂∘× _ p₂ = Product.project₂ p₂

[_⇒_]×-cong₂ : ∀ (p₁ : Product A B) (p₂ : Product C D) →
                 f ≈ g → h ≈ i →
                 [ p₁ ⇒ p₂ ] f × h ≈ [ p₁ ⇒ p₂ ] g × i
[_⇒_]×-cong₂ p₁ p₂ f≈g h≈i =
    Product.⟨⟩-cong₂ p₂ (∘-resp-≈ f≈g Equiv.refl) (∘-resp-≈ h≈i Equiv.refl)

[_⇒_]×∘⟨⟩ : ∀ (p₁ : Product A B) (p₂ : Product C D) →
              ([ p₁ ⇒ p₂ ] f × g) ∘ [ p₁ ]⟨ f′ , g′ ⟩ ≈ [ p₂ ]⟨ f ∘ f′ , g ∘ g′ ⟩
[_⇒_]×∘⟨⟩ {f = f} {g = g} {f′ = f′} {g′ = g′} p₁ p₂ = begin
  [ p₂ ]⟨ f ∘ p₁.π₁ , g ∘ p₁.π₂ ⟩ ∘ [ p₁ ]⟨ f′ , g′ ⟩ ≈⟨ p₂.∘-distribʳ-⟨⟩ ⟩
  [ p₂ ]⟨ (f ∘ p₁.π₁) ∘ p₁.⟨_,_⟩ f′ g′
        , (g ∘ p₁.π₂) ∘ p₁.⟨_,_⟩ f′ g′ ⟩              ≈⟨ p₂.⟨⟩-cong₂ assoc assoc ⟩
  [ p₂ ]⟨ f ∘ p₁.π₁ ∘ p₁.⟨_,_⟩ f′ g′
        , g ∘ p₁.π₂ ∘ p₁.⟨_,_⟩ f′ g′ ⟩                ≈⟨ p₂.⟨⟩-cong₂ (∘-resp-≈ Equiv.refl p₁.project₁) (∘-resp-≈ Equiv.refl p₁.project₂) ⟩
  [ p₂ ]⟨ f ∘ f′ , g ∘ g′ ⟩                           ∎
  where module p₁ = Product p₁
        module p₂ = Product p₂

[_]⟨⟩∘ : ∀ (p : Product A B) → [ p ]⟨ f , g ⟩ ∘ h ≈ [ p ]⟨ f ∘ h , g ∘ h ⟩
[ p ]⟨⟩∘ = ⟺ (unique (sym-assoc ○ ∘-resp-≈ˡ project₁) (sym-assoc ○ ∘-resp-≈ˡ project₂))
  where open Product p

repack∘repack≈id : ∀ (p₁ p₂ : Product A B) → repack p₁ p₂ ∘ repack p₂ p₁ ≈ id
repack∘repack≈id p₁ p₂ = [ p₂ ]⟨⟩∘ ○ p₂.⟨⟩-cong₂ p₁.project₁ p₁.project₂ ○ p₂.η
  where module p₁ = Product p₁
        module p₂ = Product p₂

[_⇒_⇒_]×∘× : ∀ (p₁ : Product A B) (p₂ : Product C D) (p₃ : Product E F) →
               ([ p₂ ⇒ p₃ ] g × i) ∘ ([ p₁ ⇒ p₂ ] f × h) ≈ [ p₁ ⇒ p₃ ] (g ∘ f) × (i ∘ h)
[_⇒_⇒_]×∘× {g = g} {i = i} {f = f} {h = h} p₁ p₂ p₃ = begin
  [ p₃ ]⟨ g ∘ p₂.π₁ , i ∘ p₂.π₂ ⟩ ∘ [ p₂ ]⟨ f ∘ p₁.π₁ , h ∘ p₁.π₂ ⟩ ≈⟨ [ p₂ ⇒ p₃ ]×∘⟨⟩ ⟩
  [ p₃ ]⟨ g ∘ f ∘ p₁.π₁ , i ∘ h ∘ p₁.π₂ ⟩                           ≈⟨ p₃.⟨⟩-cong₂ sym-assoc sym-assoc ⟩
  [ p₃ ]⟨ (g ∘ f) ∘ p₁.π₁ , (i ∘ h) ∘ p₁.π₂ ⟩                       ∎
  where module p₁ = Product p₁
        module p₂ = Product p₂
        module p₃ = Product p₃

[_⇒_⇒_]repack∘× : ∀ (p₁ : Product A B) (p₂ : Product C D) (p₃ : Product C D) →
                    repack p₂ p₃ ∘ [ p₁ ⇒ p₂ ] f × g ≈ [ p₁ ⇒ p₃ ] f × g
[_⇒_⇒_]repack∘× {f = f} {g = g} p₁ p₂ p₃ = begin
  repack p₂ p₃ ∘ [ p₁ ⇒ p₂ ] f × g            ≈⟨ repack≡id×id p₂ p₃ ⟩∘⟨refl ⟩
  ([ p₂ ⇒ p₃ ] id × id) ∘ ([ p₁ ⇒ p₂ ] f × g) ≈⟨ [ p₁ ⇒ p₂ ⇒ p₃ ]×∘× ⟩
  [ p₁ ⇒ p₃ ] (id ∘ f) × (id ∘ g)             ≈⟨ [ p₁ ⇒ p₃ ]×-cong₂ identityˡ identityˡ ⟩
  [ p₁ ⇒ p₃ ] f × g                           ∎

[_⇒_⇒_]repack∘repack : ∀ (p₁ p₂ p₃ : Product A B) → repack p₂ p₃ ∘ repack p₁ p₂ ≈ repack p₁ p₃
[_⇒_⇒_]repack∘repack = repack∘

[_⇒_]_×id : ∀ (p₁ : Product A C) (p₂ : Product B C) → A ⇒ B → [[ p₁ ]] ⇒ [[ p₂ ]]
[ p₁ ⇒ p₂ ] f ×id = [ p₁ ⇒ p₂ ] f × id

[_⇒_]id× : ∀ (p₁ : Product A B) (p₂ : Product A C) → B ⇒ C → [[ p₁ ]] ⇒ [[ p₂ ]]
[ p₁ ⇒ p₂ ]id× g = [ p₁ ⇒ p₂ ] id × g

first-id : ∀ (p : Product A B) → [ p ⇒ p ] id ×id ≈ id
first-id = id×id

second-id : ∀ (p : Product A B) → [ p ⇒ p ]id× id ≈ id
second-id = id×id

[_⇒_]×id∘⟨⟩ : ∀ (p₁ : Product B D) (p₂ : Product C D) →
                  [ p₁ ⇒ p₂ ] f ×id ∘ [ p₁ ]⟨ f′ , g′ ⟩ ≈ [ p₂ ]⟨ f ∘ f′ , g′ ⟩
[_⇒_]×id∘⟨⟩ {f = f} {f′ = f′} {g′ = g′} p₁ p₂ = begin
  [ p₁ ⇒ p₂ ] f ×id ∘ [ p₁ ]⟨ f′ , g′ ⟩ ≈⟨ [ p₁ ⇒ p₂ ]×∘⟨⟩ ⟩
  [ p₂ ]⟨ f ∘ f′ , id ∘ g′ ⟩            ≈⟨ p₂.⟨⟩-cong₂ Equiv.refl identityˡ ⟩
  [ p₂ ]⟨ f ∘ f′ , g′ ⟩                 ∎
  where module p₂ = Product p₂

[_⇒_]id×∘⟨⟩ : ∀ (p₁ : Product B D) (p₂ : Product B E) →
                   [ p₁ ⇒ p₂ ]id× g ∘ [ p₁ ]⟨ f′ , g′ ⟩ ≈ [ p₂ ]⟨ f′ , g ∘ g′ ⟩
[_⇒_]id×∘⟨⟩ {g = g} {f′ = f′} {g′ = g′} p₁ p₂ = begin
  [ p₁ ⇒ p₂ ]id× g ∘ [ p₁ ]⟨ f′ , g′ ⟩ ≈⟨ [ p₁ ⇒ p₂ ]×∘⟨⟩ ⟩
  [ p₂ ]⟨ id ∘ f′ , g ∘ g′ ⟩              ≈⟨ p₂.⟨⟩-cong₂ identityˡ Equiv.refl ⟩
  [ p₂ ]⟨ f′ , g ∘ g′ ⟩                   ∎
  where module p₂ = Product p₂

[_⇒_⇒_]×id∘×id : ∀ (p₁ : Product A D) (p₂ : Product B D) (p₃ : Product C D) →
                       [ p₂ ⇒ p₃ ] f ×id ∘ [ p₁ ⇒ p₂ ] g ×id ≈ [ p₁ ⇒ p₃ ] f ∘ g ×id
[_⇒_⇒_]×id∘×id {f = f} {g = g} p₁ p₂ p₃ = begin
  [ p₂ ⇒ p₃ ] f ×id ∘ [ p₁ ⇒ p₂ ] g ×id ≈⟨ [ p₁ ⇒ p₂ ⇒ p₃ ]×∘× ⟩
  [ p₁ ⇒ p₃ ] (f ∘ g) × (id ∘ id)       ≈⟨ [ p₁ ⇒ p₃ ]×-cong₂ Equiv.refl identityˡ ⟩
  [ p₁ ⇒ p₃ ] f ∘ g ×id                 ∎

[_⇒_⇒_]id×∘id× : ∀ (p₁ : Product A B) (p₂ : Product A C) (p₃ : Product A D) →
                         [ p₂ ⇒ p₃ ]id× f ∘ [ p₁ ⇒ p₂ ]id× g ≈ [ p₁ ⇒ p₃ ]id×(f ∘ g)
[_⇒_⇒_]id×∘id× {f = f} {g = g} p₁ p₂ p₃ = begin
  [ p₂ ⇒ p₃ ]id× f ∘ [ p₁ ⇒ p₂ ]id× g ≈⟨ [ p₁ ⇒ p₂ ⇒ p₃ ]×∘× ⟩
  [ p₁ ⇒ p₃ ] (id ∘ id) × (f ∘ g)     ≈⟨ [ p₁ ⇒ p₃ ]×-cong₂ identityˡ Equiv.refl ⟩
  [ p₁ ⇒ p₃ ]id× (f ∘ g)              ∎

[_⇒_,_⇒_]first↔second : ∀ (p₁ : Product A D) (p₂ : Product B D)
                          (p₃ : Product A C) (p₄ : Product B C) →
                          [ p₁ ⇒ p₂ ] f ×id ∘ [ p₃ ⇒ p₁ ]id× g ≈ [ p₄ ⇒ p₂ ]id× g ∘ [ p₃ ⇒ p₄ ] f ×id
[_⇒_,_⇒_]first↔second {f = f} {g = g} p₁ p₂ p₃ p₄ = begin
  [ p₁ ⇒ p₂ ] f ×id ∘ [ p₃ ⇒ p₁ ]id× g ≈⟨ [ p₃ ⇒ p₁ ⇒ p₂ ]×∘× ⟩
  [ p₃ ⇒ p₂ ] (f ∘ id) × (id ∘ g)      ≈⟨ [ p₃ ⇒ p₂ ]×-cong₂ identityʳ identityˡ ⟩
  [ p₃ ⇒ p₂ ] f × g                    ≈˘⟨ [ p₃ ⇒ p₂ ]×-cong₂ identityˡ identityʳ ⟩
  [ p₃ ⇒ p₂ ] (id ∘ f) × (g ∘ id)      ≈˘⟨ [ p₃ ⇒ p₄ ⇒ p₂ ]×∘× ⟩
  [ p₄ ⇒ p₂ ]id× g ∘ [ p₃ ⇒ p₄ ] f ×id ∎

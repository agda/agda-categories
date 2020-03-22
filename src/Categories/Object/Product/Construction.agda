{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Object.Terminal

-- Various constructors of Product Objects

module Categories.Object.Product.Construction {o ℓ e} (C : Category o ℓ e) (T : Terminal C) where

open import Categories.Object.Exponential C hiding (repack)
open import Categories.Object.Product C
open Category C
open Terminal T
open HomReasoning

-- we can get some products
[⊤×⊤]-product : Product ⊤ ⊤
[⊤×⊤]-product = record
  { A×B       = ⊤
  ; π₁        = !
  ; π₂        = !
  ; ⟨_,_⟩     = λ _ _ → !
  ; project₁  = !-unique₂
  ; project₂  = !-unique₂
  ; unique = λ _ _ → !-unique _
  }

[⊤×_]-product : (X : Obj) → Product ⊤ X
[⊤×_]-product X = record
  { A×B = X
  ; π₁ = !
  ; π₂ = id
  ; ⟨_,_⟩ = λ _ y → y
  ; project₁ = !-unique₂
  ; project₂ = identityˡ
  ; unique = λ _ id∘h≈j → ⟺ id∘h≈j ○ identityˡ
  }

[_×⊤]-product : (X : Obj) → Product X ⊤
[_×⊤]-product X = Reversible [⊤× X ]-product

-- and some exponentials too
[_↑⊤]-exponential : (B : Obj) → Exponential ⊤ B
[ B ↑⊤]-exponential = record
  { B^A = B
  ; product = [ B ×⊤]-product
  ; eval = id
  ; λg = λ {X} X×⊤ X⇒B → X⇒B ∘ repack [ X ×⊤]-product X×⊤
  ; β = λ p {g} → begin
    id ∘ (g ∘ [ p ]⟨ id , ! ⟩) ∘ [ p ]π₁    ≈⟨ identityˡ ○ assoc ⟩
    g ∘ [ p ]⟨ id , ! ⟩ ∘ [ p ]π₁           ≈⟨ refl⟩∘⟨ [ p ]⟨⟩∘ ⟩
    g ∘ [ p ]⟨ id ∘ [ p ]π₁ , ! ∘ [ p ]π₁ ⟩ ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ p identityˡ !-unique₂ ⟩
    g ∘ [ p ]⟨ [ p ]π₁ , [ p ]π₂ ⟩          ≈⟨ refl⟩∘⟨ η p ○ identityʳ ⟩
    g                                      ∎
  ; λ-unique = λ {X} p {g} {h} h-comm → begin
    h                                    ≈˘⟨ identityʳ ⟩
    h ∘ id                               ≈˘⟨  refl⟩∘⟨ project₁ p ⟩
    h ∘ [ p ]π₁ ∘ [ p ]⟨ id , ! ⟩        ≈⟨ sym-assoc ⟩
    (h ∘ [ p ]π₁) ∘ [ p ]⟨ id , ! ⟩      ≈˘⟨ identityˡ ⟩∘⟨refl ⟩
    (id ∘ h ∘ [ p ]π₁) ∘ [ p ]⟨ id , ! ⟩ ≈⟨ h-comm ⟩∘⟨refl ⟩
    g ∘ repack [ X ×⊤]-product p         ∎
  }
  where open Product

[⊤↑_]-exponential : (A : Obj) → Exponential A ⊤
[⊤↑ A ]-exponential = record
  { B^A       = ⊤
  ; product   = [⊤× A ]-product
  ; eval      = !
  ; λg        = λ _ _ → !
  ; β         = λ _   → !-unique₂
  ; λ-unique  = λ _ _ → !-unique₂
  }

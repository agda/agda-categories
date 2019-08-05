{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Diagram.Pullback.Properties {o ℓ e} (C : Category o ℓ e) where

open import Categories.Diagram.Pullback C
open import Categories.Object.Product C
open import Categories.Object.Terminal C

private
  open Category C
  variable
    X Y Z : Obj
    f g h i : X ⇒ Y
open HomReasoning

-- pullback from a terminal object is the same as a product
module _ (t : Terminal) where
  open Terminal t

  pullback-⊤⇒product : Pullback (! {X}) (! {Y}) → Product X Y
  pullback-⊤⇒product p = record
    { A×B      = P
    ; π₁       = p₁
    ; π₂       = p₂
    ; ⟨_,_⟩    = λ f g → universal (!-unique₂ {f = ! ∘ f} {g = ! ∘ g})
    ; project₁ = p₁∘universal≈h₁
    ; project₂ = p₂∘universal≈h₂
    ; unique   = λ eq eq′ → ⟺ (unique eq eq′)
    }
    where open Pullback p

  product⇒pullback-⊤ : Product X Y → Pullback (! {X}) (! {Y})
  product⇒pullback-⊤ p = record
    { p₁              = π₁
    ; p₂              = π₂
    ; commute         = !-unique₂
    ; universal       = λ {_ f g} _ → ⟨ f , g ⟩
    ; unique          = λ eq eq′ → ⟺ (unique eq eq′)
    ; p₁∘universal≈h₁ = project₁
    ; p₂∘universal≈h₂ = project₂
    }
    where open Product p

-- pullbacks respect _≈_
module _ (p : Pullback f g) where
  open Pullback p

  pullback-resp-≈ : f ≈ h → g ≈ i → Pullback h i
  pullback-resp-≈ eq eq′ = record
    { p₁              = p₁
    ; p₂              = p₂
    ; commute         = ∘-resp-≈ˡ (⟺ eq) ○ commute ○ ∘-resp-≈ˡ eq′
    ; universal       = λ eq″ → universal (∘-resp-≈ˡ eq ○ eq″ ○ ∘-resp-≈ˡ (⟺ eq′))
    ; unique          = unique
    ; p₁∘universal≈h₁ = p₁∘universal≈h₁
    ; p₂∘universal≈h₂ = p₂∘universal≈h₂
    }

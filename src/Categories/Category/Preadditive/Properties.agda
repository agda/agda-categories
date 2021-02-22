{-# OPTIONS --without-K --safe #-}

module Categories.Category.Preadditive.Properties where

open import Categories.Category
open import Categories.Category.Preadditive

open import Categories.Object.Initial
open import Categories.Object.Terminal
open import Categories.Object.Biproduct
open import Categories.Object.Coproduct
open import Categories.Object.Product
open import Categories.Object.Zero

import Categories.Morphism.Reasoning as MR

module _ {o ℓ e} {𝒞 : Category o ℓ e} (preadditive : Preadditive 𝒞) where
  open Category 𝒞
  open HomReasoning
  open Preadditive preadditive

  open MR 𝒞

  Initial⇒Zero : Initial 𝒞 → Zero 𝒞
  Initial⇒Zero initial = record
    { zero = ⊥
    ; ! = ! 
    ; ¡ = 0H
    ; !-unique = !-unique
    ; ¡-unique = λ f → begin
      0H     ≈˘⟨ 0-resp-∘ˡ ⟩
      0H ∘ f ≈⟨ !-unique₂ 0H id ⟩∘⟨refl ⟩
      id ∘ f ≈⟨ identityˡ ⟩
      f ∎
    }
    where
      open Initial initial

  Terminal⇒Zero : Terminal 𝒞 → Zero 𝒞
  Terminal⇒Zero terminal = record
    { zero = ⊤
    ; ! = 0H
    ; ¡ = !
    ; !-unique = λ f → begin
      0H     ≈˘⟨ 0-resp-∘ʳ ⟩
      f ∘ 0H ≈⟨ refl⟩∘⟨ !-unique₂ ⟩
      f ∘ id ≈⟨ identityʳ ⟩
      f ∎
    ; ¡-unique = !-unique
    }
    where
      open Terminal terminal

  Product⇒Biproduct : ∀ {A B} → Product 𝒞 A B → Biproduct 𝒞 A B
  Product⇒Biproduct product = record
    { A⊕B = A×B
    ; π₁ = π₁
    ; π₂ = π₂
    ; ⟨_,_⟩ = ⟨_,_⟩
    ; project₁ = project₁
    ; project₂ = project₂
    ; ⟨⟩-unique = unique
    ; i₁ = ⟨ id , 0H ⟩
    ; i₂ = ⟨ 0H , id ⟩
    ; [_,_] = λ f g → (f ∘ π₁) + (g ∘ π₂)
    ; inject₁ = λ {C} {f} {g} → begin
      (f ∘ π₁ + g ∘ π₂) ∘ ⟨ id , 0H ⟩                     ≈⟨ +-resp-∘ʳ ⟩
      ((f ∘ π₁) ∘ ⟨ id , 0H ⟩) + ((g ∘ π₂) ∘ ⟨ id , 0H ⟩) ≈⟨ +-cong (cancelʳ project₁) (pullʳ project₂) ⟩
      f + (g ∘ 0H)                                        ≈⟨ +-elimʳ 0-resp-∘ʳ ⟩
      f                                                   ∎
    ; inject₂ = λ {C} {f} {g} → begin
      (f ∘ π₁ + g ∘ π₂) ∘ ⟨ 0H , id ⟩                     ≈⟨ +-resp-∘ʳ ⟩
      ((f ∘ π₁) ∘ ⟨ 0H , id ⟩) + ((g ∘ π₂) ∘ ⟨ 0H , id ⟩) ≈⟨ +-cong (pullʳ project₁) (cancelʳ project₂) ⟩
      (f ∘ 0H) + g                                        ≈⟨ +-elimˡ 0-resp-∘ʳ ⟩
      g                                                   ∎
    ; []-unique = λ {X} {h} {f} {g} eq₁ eq₂ → begin
      (f ∘ π₁) + (g ∘ π₂)                                 ≈⟨ +-cong (pushˡ (⟺ eq₁)) (pushˡ (⟺ eq₂)) ⟩
      (h ∘ ⟨ id , 0H ⟩ ∘ π₁) + (h ∘ ⟨ 0H , id ⟩ ∘ π₂)     ≈˘⟨ +-resp-∘ˡ ⟩
      h ∘ (⟨ id , 0H ⟩ ∘ π₁ + ⟨ 0H , id ⟩ ∘ π₂)           ≈⟨ refl⟩∘⟨ +-cong ∘-distribʳ-⟨⟩ ∘-distribʳ-⟨⟩ ⟩
      h ∘ (⟨ id ∘ π₁ , 0H ∘ π₁ ⟩ + ⟨ 0H ∘ π₂ , id ∘ π₂ ⟩) ≈⟨ refl⟩∘⟨ +-cong (⟨⟩-cong₂ identityˡ 0-resp-∘ˡ) (⟨⟩-cong₂ 0-resp-∘ˡ identityˡ) ⟩
      h ∘ (⟨ π₁ , 0H ⟩ + ⟨ 0H , π₂ ⟩)                     ≈⟨ elimʳ (⟺ (unique′ π₁-lemma π₂-lemma)) ⟩
      h                                                   ∎
    ; π₁∘i₁≈id = project₁
    ; π₂∘i₂≈id = project₂
    ; permute = begin
      ⟨ id , 0H ⟩ ∘ π₁ ∘ ⟨ 0H , id ⟩ ∘ π₂ ≈⟨ pull-center project₁ ⟩
      ⟨ id , 0H ⟩ ∘ 0H ∘ π₂               ≈⟨ pullˡ 0-resp-∘ʳ ⟩
      0H ∘ π₂                             ≈⟨ 0-resp-∘ˡ ⟩
      0H                                  ≈˘⟨ 0-resp-∘ˡ ⟩
      0H ∘ π₁                             ≈⟨ pushˡ (⟺ 0-resp-∘ʳ) ⟩
      ⟨ 0H , id ⟩ ∘ 0H ∘ π₁               ≈⟨ push-center project₂ ⟩
      ⟨ 0H , id ⟩ ∘ π₂ ∘ ⟨ id , 0H ⟩ ∘ π₁ ∎
    }
    where
      open Product 𝒞 product

      π₁-lemma : π₁ ∘ id ≈ π₁ ∘ (⟨ π₁ , 0H ⟩ + ⟨ 0H , π₂ ⟩)
      π₁-lemma = begin
        π₁ ∘ id                                 ≈⟨ identityʳ ⟩
        π₁                                      ≈˘⟨ +-identityʳ π₁ ⟩
        π₁ + 0H                                 ≈⟨ +-cong (⟺ project₁) (⟺ project₁) ⟩
        (π₁ ∘ ⟨ π₁ , 0H ⟩) + (π₁ ∘ ⟨ 0H , π₂ ⟩) ≈˘⟨ +-resp-∘ˡ ⟩
        π₁ ∘ (⟨ π₁ , 0H ⟩ + ⟨ 0H , π₂ ⟩)        ∎

      π₂-lemma : π₂ ∘ id ≈ π₂ ∘ (⟨ π₁ , 0H ⟩ + ⟨ 0H , π₂ ⟩)
      π₂-lemma = begin
        π₂ ∘ id                                 ≈⟨ identityʳ ⟩
        π₂                                      ≈˘⟨ +-identityˡ π₂ ⟩
        0H + π₂                                 ≈⟨ +-cong (⟺ project₂) (⟺ project₂) ⟩
        (π₂ ∘ ⟨ π₁ , 0H ⟩) + (π₂ ∘ ⟨ 0H , π₂ ⟩) ≈˘⟨ +-resp-∘ˡ ⟩
        π₂ ∘ (⟨ π₁ , 0H ⟩ + ⟨ 0H , π₂ ⟩)        ∎

  Coproduct⇒Biproduct : ∀ {A B} → Coproduct 𝒞 A B → Biproduct 𝒞 A B
  Coproduct⇒Biproduct coproduct = record
    { A⊕B = A+B
    ; π₁ = [ id , 0H ]
    ; π₂ = [ 0H , id ]
    ; ⟨_,_⟩ = λ f g → (i₁ ∘ f) + (i₂ ∘ g)
    ; project₁ = λ {C} {f} {g} → begin
      [ id , 0H ] ∘ (i₁ ∘ f + i₂ ∘ g)                 ≈⟨ +-resp-∘ˡ ⟩
      ([ id , 0H ] ∘ i₁ ∘ f) + ([ id , 0H ] ∘ i₂ ∘ g) ≈⟨ +-cong (cancelˡ inject₁) (pullˡ inject₂) ⟩
      f + (0H ∘ g)                                    ≈⟨ +-elimʳ 0-resp-∘ˡ ⟩
      f                                               ∎
    ; project₂ = λ {C} {f} {g} → begin
      [ 0H , id ] ∘ (i₁ ∘ f + i₂ ∘ g)                 ≈⟨ +-resp-∘ˡ ⟩
      ([ 0H , id ] ∘ i₁ ∘ f) + ([ 0H , id ] ∘ i₂ ∘ g) ≈⟨ +-cong (pullˡ inject₁) (cancelˡ inject₂) ⟩
      (0H ∘ f) + g                                    ≈⟨ +-elimˡ 0-resp-∘ˡ ⟩
      g                                               ∎
    ; ⟨⟩-unique = λ {X} {h} {f} {g} eq₁ eq₂ → begin
      (i₁ ∘ f) + (i₂ ∘ g)                                 ≈⟨ +-cong (pushʳ (⟺ eq₁)) (pushʳ (⟺ eq₂)) ⟩
      (i₁ ∘ [ id , 0H ]) ∘ h + (i₂ ∘ [ 0H , id ]) ∘ h     ≈˘⟨ +-resp-∘ʳ ⟩
      (i₁ ∘ [ id , 0H ] + i₂ ∘ [ 0H , id ]) ∘ h           ≈⟨ +-cong ∘-distribˡ-[] ∘-distribˡ-[] ⟩∘⟨refl ⟩
      ([ i₁ ∘ id , i₁ ∘ 0H ] + [ i₂ ∘ 0H , i₂ ∘ id ]) ∘ h ≈⟨ +-cong ([]-cong₂ identityʳ 0-resp-∘ʳ) ([]-cong₂ 0-resp-∘ʳ identityʳ) ⟩∘⟨refl ⟩
      ([ i₁ , 0H ] + [ 0H , i₂ ]) ∘ h                     ≈⟨ elimˡ (⟺ (unique′ i₁-lemma i₂-lemma)) ⟩
      h                                                   ∎
    ; i₁ = i₁
    ; i₂ = i₂
    ; [_,_] = [_,_]
    ; inject₁ = inject₁
    ; inject₂ = inject₂
    ; []-unique = unique
    ; π₁∘i₁≈id = inject₁
    ; π₂∘i₂≈id = inject₂
    ; permute = begin
      i₁ ∘ [ id , 0H ] ∘ i₂ ∘ [ 0H , id ] ≈⟨ pull-center inject₂ ⟩
      i₁ ∘ 0H ∘ [ 0H , id ]               ≈⟨ pullˡ 0-resp-∘ʳ ⟩
      0H ∘ [ 0H , id ]                    ≈⟨ 0-resp-∘ˡ ⟩
      0H                                  ≈˘⟨ 0-resp-∘ˡ ⟩
      0H ∘ [ id , 0H ]                    ≈⟨ pushˡ (⟺ 0-resp-∘ʳ) ⟩
      i₂ ∘ 0H ∘ [ id , 0H ]               ≈⟨ push-center inject₁ ⟩
      i₂ ∘ [ 0H , id ] ∘ i₁ ∘ [ id , 0H ] ∎
    }
    where
      open Coproduct coproduct

      i₁-lemma : id ∘ i₁ ≈ ([ i₁ , 0H ] + [ 0H , i₂ ]) ∘ i₁
      i₁-lemma = begin
        id ∘ i₁                             ≈⟨ identityˡ ⟩
        i₁                                  ≈˘⟨ +-identityʳ i₁ ⟩
        i₁ + 0H                             ≈⟨ +-cong (⟺ inject₁) (⟺ inject₁) ⟩
        [ i₁ , 0H ] ∘ i₁ + [ 0H , i₂ ] ∘ i₁ ≈˘⟨ +-resp-∘ʳ ⟩
        ([ i₁ , 0H ] + [ 0H , i₂ ]) ∘ i₁    ∎

      i₂-lemma : id ∘ i₂ ≈ ([ i₁ , 0H ] + [ 0H , i₂ ]) ∘ i₂
      i₂-lemma = begin
        id ∘ i₂                             ≈⟨ identityˡ ⟩
        i₂                                  ≈˘⟨ +-identityˡ i₂ ⟩
        0H + i₂                             ≈⟨ +-cong (⟺ inject₂) (⟺ inject₂) ⟩
        [ i₁ , 0H ] ∘ i₂ + [ 0H , i₂ ] ∘ i₂ ≈˘⟨ +-resp-∘ʳ ⟩
        ([ i₁ , 0H ] + [ 0H , i₂ ]) ∘ i₂    ∎

  -- FIXME: Show the other direction, and bundle up all of this junk into a record
  -- Our version of biproducts coincide with those found in Maclane's "Categories For the Working Mathematician", VIII.2,
  -- and Borceux's "Handbook of Categorical Algebra, Volume 2", 1.2.4
  Biproduct⇒Preadditive : ∀ {A B X} {p₁ : X ⇒ A} {p₂ : X ⇒ B} {i₁ : A ⇒ X} {i₂ : B ⇒ X}
                          → p₁ ∘ i₁ ≈ id
                          → p₂ ∘ i₂ ≈ id
                          → (i₁ ∘ p₁) + (i₂ ∘ p₂) ≈ id
                          → Biproduct 𝒞 A B
  Biproduct⇒Preadditive {A} {B} {X} {p₁} {p₂} {i₁} {i₂} p₁∘i₁≈id p₂∘i₂≈id +-eq = record
    { A⊕B = X
    ; π₁ = p₁
    ; π₂ = p₂
    ; ⟨_,_⟩ = λ f g → (i₁ ∘ f) + (i₂ ∘ g)
    ; project₁ = λ {C} {f} {g} →  begin
      p₁ ∘ (i₁ ∘ f + i₂ ∘ g)        ≈⟨ +-resp-∘ˡ ⟩
      (p₁ ∘ i₁ ∘ f) + (p₁ ∘ i₂ ∘ g) ≈⟨ +-cong (cancelˡ p₁∘i₁≈id) (pullˡ p₁∘i₂≈0) ⟩
      f + (0H ∘ g)                  ≈⟨ +-elimʳ 0-resp-∘ˡ ⟩
      f                             ∎
    ; project₂ = λ {C} {f} {g} → begin
      p₂ ∘ (i₁ ∘ f + i₂ ∘ g)        ≈⟨ +-resp-∘ˡ ⟩
      (p₂ ∘ i₁ ∘ f) + (p₂ ∘ i₂ ∘ g) ≈⟨ +-cong (pullˡ p₂∘i₁≈0) (cancelˡ p₂∘i₂≈id) ⟩
      (0H ∘ f) + g                  ≈⟨ +-elimˡ 0-resp-∘ˡ ⟩
      g                             ∎
    ; ⟨⟩-unique = λ {X} {h} {f} {g} eq₁ eq₂ → begin
      (i₁ ∘ f) + (i₂ ∘ g)               ≈⟨ +-cong (pushʳ (⟺ eq₁)) (pushʳ (⟺ eq₂)) ⟩
      ((i₁ ∘ p₁) ∘ h) + ((i₂ ∘ p₂) ∘ h) ≈˘⟨ +-resp-∘ʳ ⟩
      (i₁ ∘ p₁ + i₂ ∘ p₂) ∘ h           ≈⟨ elimˡ +-eq ⟩
      h ∎
    ; i₁ = i₁
    ; i₂ = i₂
    ; [_,_] = λ f g → (f ∘ p₁) + (g ∘ p₂)
    ; inject₁ = λ {C} {f} {g} → begin
      (f ∘ p₁ + g ∘ p₂) ∘ i₁            ≈⟨ +-resp-∘ʳ ⟩
      ((f ∘ p₁) ∘ i₁) + ((g ∘ p₂) ∘ i₁) ≈⟨ +-cong (cancelʳ p₁∘i₁≈id) (pullʳ p₂∘i₁≈0) ⟩
      f + (g ∘ 0H)                      ≈⟨ +-elimʳ 0-resp-∘ʳ ⟩
      f                                 ∎
    ; inject₂ = λ {C} {f} {g} → begin
      (f ∘ p₁ + g ∘ p₂) ∘ i₂            ≈⟨ +-resp-∘ʳ ⟩
      ((f ∘ p₁) ∘ i₂) + ((g ∘ p₂) ∘ i₂) ≈⟨ +-cong (pullʳ p₁∘i₂≈0) (cancelʳ p₂∘i₂≈id) ⟩
      (f ∘ 0H) + g                      ≈⟨ +-elimˡ 0-resp-∘ʳ ⟩
      g                                 ∎
    ; []-unique = λ {X} {h} {f} {g} eq₁ eq₂ → begin
      (f ∘ p₁) + (g ∘ p₂)           ≈⟨ +-cong (pushˡ (⟺ eq₁)) (pushˡ (⟺ eq₂)) ⟩
      (h ∘ i₁ ∘ p₁) + (h ∘ i₂ ∘ p₂) ≈˘⟨ +-resp-∘ˡ ⟩
      h ∘ (i₁ ∘ p₁ + i₂ ∘ p₂)       ≈⟨ elimʳ +-eq ⟩
      h                             ∎
    ; π₁∘i₁≈id = p₁∘i₁≈id
    ; π₂∘i₂≈id = p₂∘i₂≈id
    ; permute = begin
      i₁ ∘ p₁ ∘ i₂ ∘ p₂ ≈⟨ pull-center p₁∘i₂≈0 ⟩
      i₁ ∘ 0H ∘ p₂      ≈⟨ pullˡ 0-resp-∘ʳ ⟩
      0H ∘ p₂           ≈⟨ 0-resp-∘ˡ ⟩
      0H                ≈˘⟨ 0-resp-∘ˡ ⟩
      0H ∘ p₁           ≈⟨ pushˡ (⟺ (0-resp-∘ʳ)) ⟩
      i₂ ∘ 0H ∘ p₁      ≈⟨ push-center p₂∘i₁≈0 ⟩
      i₂ ∘ p₂ ∘ i₁ ∘ p₁ ∎
    }
    where
      p₁∘i₂≈0 : p₁ ∘ i₂ ≈ 0H
      p₁∘i₂≈0 = begin
        p₁ ∘ i₂                                                   ≈˘⟨ +-identityʳ (p₁ ∘ i₂) ⟩
        p₁ ∘ i₂ + 0H                                              ≈˘⟨ +-congˡ (-‿inverseʳ (p₁ ∘ i₂)) ⟩
        p₁ ∘ i₂ + (p₁ ∘ i₂ - p₁ ∘ i₂)                             ≈˘⟨ +-assoc (p₁ ∘ i₂) (p₁ ∘ i₂) (neg (p₁ ∘ i₂)) ⟩
        (p₁ ∘ i₂) + (p₁ ∘ i₂) - p₁ ∘ i₂                           ≈⟨ +-congʳ (+-cong (intro-first p₁∘i₁≈id) (intro-last p₂∘i₂≈id)) ⟩
        (p₁ ∘ (i₁ ∘ p₁) ∘ i₂) + (p₁ ∘ (i₂ ∘ p₂) ∘ i₂) - (p₁ ∘ i₂) ≈˘⟨ +-congʳ +-resp-∘ ⟩
        (p₁ ∘ (i₁ ∘ p₁ + i₂ ∘ p₂) ∘ i₂) - (p₁ ∘ i₂)               ≈⟨ +-congʳ (elim-center +-eq) ⟩
        (p₁ ∘ i₂) - (p₁ ∘ i₂)                                     ≈⟨ -‿inverseʳ (p₁ ∘ i₂) ⟩
        0H                                                        ∎

      p₂∘i₁≈0 : p₂ ∘ i₁ ≈ 0H
      p₂∘i₁≈0 = begin
        (p₂ ∘ i₁)                                                 ≈˘⟨ +-identityʳ (p₂ ∘ i₁) ⟩
        p₂ ∘ i₁ + 0H                                              ≈˘⟨ +-congˡ (-‿inverseʳ (p₂ ∘ i₁)) ⟩
        (p₂ ∘ i₁) + (p₂ ∘ i₁ - p₂ ∘ i₁)                           ≈˘⟨ +-assoc (p₂ ∘ i₁) (p₂ ∘ i₁) (neg (p₂ ∘ i₁)) ⟩
        (p₂ ∘ i₁) + (p₂ ∘ i₁) - (p₂ ∘ i₁)                         ≈⟨ +-congʳ (+-cong (intro-last p₁∘i₁≈id) (intro-first p₂∘i₂≈id)) ⟩
        (p₂ ∘ (i₁ ∘ p₁) ∘ i₁) + (p₂ ∘ (i₂ ∘ p₂) ∘ i₁) - (p₂ ∘ i₁) ≈˘⟨ +-congʳ +-resp-∘ ⟩
        (p₂ ∘ (i₁ ∘ p₁ + i₂ ∘ p₂) ∘ i₁) - (p₂ ∘ i₁)               ≈⟨ +-congʳ (elim-center +-eq) ⟩
        (p₂ ∘ i₁) - (p₂ ∘ i₁)                                     ≈⟨ -‿inverseʳ (p₂ ∘ i₁) ⟩
        0H                                                        ∎

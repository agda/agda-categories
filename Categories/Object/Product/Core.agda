{-# OPTIONS --without-K --safe #-}
open import Categories.Category

module Categories.Object.Product.Core {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level
open import Function using (flip)

open import Categories.Square 𝒞
open import Categories.Morphisms 𝒞

open Category 𝒞
open HomReasoning

private
  variable
    A B C D X Y Z : Obj
    h i j : A ⇒ B

-- Borrowed from Dan Doel's definition of products
record Product (A B : Obj) : Set (o ⊔ ℓ ⊔ e) where

  infix 10 ⟨_,_⟩

  field
    A×B   : Obj
    π₁    : A×B ⇒ A
    π₂    : A×B ⇒ B
    ⟨_,_⟩ : C ⇒ A → C ⇒ B → C ⇒ A×B

    commute₁  : π₁ ∘ ⟨ h , i ⟩ ≈ h
    commute₂  : π₂ ∘ ⟨ h , i ⟩ ≈ i
    universal : π₁ ∘ h ≈ i → π₂ ∘ h ≈ j → ⟨ i , j ⟩ ≈ h

  g-η : ⟨ π₁ ∘ h , π₂ ∘ h ⟩ ≈ h
  g-η = universal refl refl

  η : ⟨ π₁ , π₂ ⟩ ≈ id
  η = universal identityʳ identityʳ

  ⟨⟩-cong₂ : ∀ {f f′ : C ⇒ A} {g g′ : C ⇒ B} → f ≈ f′ → g ≈ g′ → ⟨ f , g ⟩ ≈ ⟨ f′ , g′ ⟩
  ⟨⟩-cong₂ f≡f′ g≡g′ = 
    universal (trans commute₁ (sym f≡f′)) (trans commute₂ (sym g≡g′))

  ∘-distribʳ-⟨⟩ : ∀ {f : C ⇒ A} {g : C ⇒ B} {q : D ⇒ C} → ⟨ f , g ⟩ ∘ q ≈ ⟨ f ∘ q , g ∘ q ⟩
  ∘-distribʳ-⟨⟩ = sym (universal (pullˡ commute₁) (pullˡ commute₂))

module _ {A B : Obj} where
  open Product {A} {B} renaming (⟨_,_⟩ to _⟨_,_⟩)

  repack : ∀ (p₁ p₂ : Product A B) → A×B p₁ ⇒ A×B p₂
  repack p₁ p₂ = p₂ ⟨ π₁ p₁ , π₂ p₁ ⟩

  repack∘ : (p₁ p₂ p₃ : Product A B) → repack p₂ p₃ ∘ repack p₁ p₂ ≈ repack p₁ p₃
  repack∘ p₁ p₂ p₃ = sym (universal p₃ 
    (glueTrianglesʳ (commute₁ p₃) (commute₁ p₂))
    (glueTrianglesʳ (commute₂ p₃) (commute₂ p₂)))

  repack≡id : (p : Product A B) → repack p p ≈ id
  repack≡id p = η p

  repack-cancel : (p₁ p₂ : Product A B) → repack p₁ p₂ ∘ repack p₂ p₁ ≈ id
  repack-cancel p₁ p₂ = trans (repack∘ p₂ p₁ p₂) (repack≡id p₂)

up-to-iso : ∀ (p₁ p₂ : Product A B) → Product.A×B p₁ ≅ Product.A×B p₂
up-to-iso p₁ p₂ = record
  { f = repack p₁ p₂
  ; g = repack p₂ p₁
  ; iso = record
    { isoˡ = repack-cancel p₂ p₁
    ; isoʳ = repack-cancel p₁ p₂
    }
  }

transport-by-iso : ∀ (p : Product A B) → ∀ {X} → Product.A×B p ≅ X → Product A B
transport-by-iso p {X} p≅X = record
  { A×B = X
  ; π₁ = π₁ ∘ g
  ; π₂ = π₂ ∘ g
  ; ⟨_,_⟩ = λ h₁ h₂ → f ∘ ⟨ h₁ , h₂ ⟩
  ; commute₁ = trans (cancelInner isoˡ) commute₁
  ; commute₂ = trans (cancelInner isoˡ) commute₂
  ; universal = λ {_ i l r} pf₁ pf₂ → begin
    f ∘ ⟨ l , r ⟩                       ≈⟨ refl ⟩∘⟨ ⟨⟩-cong₂ (sym pf₁) (sym pf₂) ⟩
    f ∘ ⟨ (π₁ ∘ g) ∘ i , (π₂ ∘ g) ∘ i ⟩ ≈⟨ refl ⟩∘⟨ universal (sym assoc) (sym assoc) ⟩
    f ∘ g ∘ i                           ≈⟨ cancelLeft isoʳ ⟩
    i                                   ∎
  }
  where open Product p
        open _≅_ p≅X

Reversible : ∀ (p : Product A B) → Product B A
Reversible p = record
  { A×B       = A×B
  ; π₁        = π₂
  ; π₂        = π₁
  ; ⟨_,_⟩     = flip ⟨_,_⟩
  ; commute₁  = commute₂
  ; commute₂  = commute₁
  ; universal = flip universal
  }
  where open Product p

Commutative : ∀ (p₁ : Product A B) (p₂ : Product B A) → Product.A×B p₁ ≅ Product.A×B p₂
Commutative p₁ p₂ = up-to-iso p₁ (Reversible p₂)

Associable : ∀ (p₁ : Product X Y) (p₂ : Product Y Z) (p₃ : Product X (Product.A×B p₂)) → Product (Product.A×B p₁) Z
Associable p₁ p₂ p₃ = record
  { A×B       = A×B p₃
  ; π₁        = p₁ ⟨ π₁ p₃ , π₁ p₂ ∘ π₂ p₃ ⟩
  ; π₂        = π₂ p₂ ∘ π₂ p₃
  ; ⟨_,_⟩     = λ f g → p₃ ⟨ π₁ p₁ ∘ f , p₂ ⟨ π₂ p₁ ∘ f , g ⟩ ⟩
  ; commute₁  = λ {_ f g} → begin
    p₁ ⟨ π₁ p₃ , π₁ p₂ ∘ π₂ p₃ ⟩ ∘ p₃ ⟨ π₁ p₁ ∘ f , p₂ ⟨ π₂ p₁ ∘ f , g ⟩ ⟩ ≈⟨ ∘-distribʳ-⟨⟩ p₁ ⟩
    p₁ ⟨ π₁ p₃ ∘ p₃ ⟨ π₁ p₁ ∘ f , p₂ ⟨ π₂ p₁ ∘ f , g ⟩ ⟩
       , (π₁ p₂ ∘ π₂ p₃) ∘ p₃ ⟨ π₁ p₁ ∘ f , p₂ ⟨ π₂ p₁ ∘ f , g ⟩ ⟩ ⟩       ≈⟨ ⟨⟩-cong₂ p₁ (commute₁ p₃) (glueTrianglesˡ (commute₁ p₂) (commute₂ p₃)) ⟩
    p₁ ⟨ π₁ p₁ ∘ f , π₂ p₁ ∘ f ⟩                                           ≈⟨ g-η p₁ ⟩
    f                                                                      ∎
  ; commute₂  = λ {_ f g} → glueTrianglesˡ (commute₂ p₂) (commute₂ p₃)
  ; universal = λ {_ i f g} pf₁ pf₂ → begin
    p₃ ⟨ π₁ p₁ ∘ f , p₂ ⟨ π₂ p₁ ∘ f , g ⟩ ⟩             ≈⟨ ⟨⟩-cong₂ p₃ (∘-resp-≈ʳ (sym pf₁))
                                                          (⟨⟩-cong₂ p₂ (∘-resp-≈ʳ (sym pf₁)) (sym pf₂)) ⟩
    p₃ ⟨ π₁ p₁ ∘ p₁ ⟨ π₁ p₃ , π₁ p₂ ∘ π₂ p₃ ⟩ ∘ i
       , p₂ ⟨ π₂ p₁ ∘ p₁ ⟨ π₁ p₃ , π₁ p₂ ∘ π₂ p₃ ⟩ ∘ i
            , (π₂ p₂ ∘ π₂ p₃) ∘ i ⟩ ⟩                   ≈⟨ ⟨⟩-cong₂ p₃ (pullˡ (commute₁ p₁))
                                                          (⟨⟩-cong₂ p₂ (trans (pullˡ (commute₂ p₁)) assoc)
                                                                       assoc) ⟩
    p₃ ⟨ π₁ p₃ ∘ i
       , p₂ ⟨ π₁ p₂ ∘ π₂ p₃ ∘ i , π₂ p₂ ∘ π₂ p₃ ∘ i ⟩ ⟩ ≈⟨ ⟨⟩-cong₂ p₃ refl (g-η p₂) ⟩
    p₃ ⟨ π₁ p₃ ∘ i , π₂ p₃ ∘ i ⟩                        ≈⟨ g-η p₃ ⟩
    i                                                   ∎
  }
  where open Product renaming (⟨_,_⟩ to _⟨_,_⟩)

Associative : ∀ (p₁ : Product X Y) (p₂ : Product Y Z)
                (p₃ : Product X (Product.A×B p₂)) (p₄ : Product (Product.A×B p₁) Z) →
                (Product.A×B p₃) ≅ (Product.A×B p₄)
Associative p₁ p₂ p₃ p₄ = up-to-iso (Associable p₁ p₂ p₃) p₄

Mobile : ∀ {A₁ B₁ A₂ B₂} (p : Product A₁ B₁) → A₁ ≅ A₂ → B₁ ≅ B₂ → Product A₂ B₂
Mobile p A₁≅A₂ B₁≅B₂ = record
  { A×B              = A×B
  ; π₁               = f A₁≅A₂ ∘ π₁
  ; π₂               = f B₁≅B₂ ∘ π₂
  ; ⟨_,_⟩            = λ h k → ⟨ g A₁≅A₂ ∘ h , g B₁≅B₂ ∘ k ⟩
  ; commute₁         = begin
    (f A₁≅A₂ ∘ π₁) ∘ ⟨ g A₁≅A₂ ∘ _ , g B₁≅B₂ ∘ _ ⟩ ≈⟨ pullʳ commute₁ ⟩
    f A₁≅A₂ ∘ (g A₁≅A₂ ∘ _)                        ≈⟨ cancelLeft (isoʳ A₁≅A₂) ⟩
    _                                              ∎
  ; commute₂         = begin
    (f B₁≅B₂ ∘ π₂) ∘ ⟨ g A₁≅A₂ ∘ _ , g B₁≅B₂ ∘ _ ⟩ ≈⟨ pullʳ commute₂ ⟩
    f B₁≅B₂ ∘ (g B₁≅B₂ ∘ _)                        ≈⟨ cancelLeft (isoʳ B₁≅B₂) ⟩
    _                                              ∎
  ; universal        = λ pfˡ pfʳ → universal (switch-fgˡ A₁≅A₂ (trans (sym assoc) pfˡ))
                                             (switch-fgˡ B₁≅B₂ (trans (sym assoc) pfʳ))
  }
  where open Product p
        open _≅_

{-# OPTIONS --without-K --safe #-}
open import Categories.Category

module Categories.Object.Product.Core {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level
open import Function using (flip; _$_)

open import Categories.Morphism 𝒞
open import Categories.Morphism.Reasoning 𝒞

open Category 𝒞
open HomReasoning

private
  variable
    A B C D X Y Z : Obj
    h i j : A ⇒ B

-- Borrowed from Dan Doel's definition of products
record Product (A B : Obj) : Set (o ⊔ ℓ ⊔ e) where

  field
    A×B   : Obj
    π₁    : A×B ⇒ A
    π₂    : A×B ⇒ B
    ⟨_,_⟩ : C ⇒ A → C ⇒ B → C ⇒ A×B

    project₁ : π₁ ∘ ⟨ h , i ⟩ ≈ h
    project₂ : π₂ ∘ ⟨ h , i ⟩ ≈ i
    unique   : π₁ ∘ h ≈ i → π₂ ∘ h ≈ j → ⟨ i , j ⟩ ≈ h

  open Equiv

  g-η : ⟨ π₁ ∘ h , π₂ ∘ h ⟩ ≈ h
  g-η = unique refl refl

  η : ⟨ π₁ , π₂ ⟩ ≈ id
  η = unique identityʳ identityʳ

  ⟨⟩-cong₂ : ∀ {f f′ : C ⇒ A} {g g′ : C ⇒ B} → f ≈ f′ → g ≈ g′ → ⟨ f , g ⟩ ≈ ⟨ f′ , g′ ⟩
  ⟨⟩-cong₂ f≡f′ g≡g′ = unique (project₁ ○ ⟺ f≡f′) (project₂ ○ ⟺ g≡g′)

  ∘-distribʳ-⟨⟩ : ∀ {f : C ⇒ A} {g : C ⇒ B} {q : D ⇒ C} → ⟨ f , g ⟩ ∘ q ≈ ⟨ f ∘ q , g ∘ q ⟩
  ∘-distribʳ-⟨⟩ = ⟺ $ unique (pullˡ project₁) (pullˡ project₂)

  unique′ : π₁ ∘ h ≈ π₁ ∘ i → π₂ ∘ h ≈ π₂ ∘ i → h ≈ i
  unique′ eq₁ eq₂ = trans (sym (unique eq₁ eq₂)) g-η

record IsProduct {A B P} (π₁ : P ⇒ A) (π₂ : P ⇒ B) : Set (o ⊔ ℓ ⊔ e) where

  field
    ⟨_,_⟩ : C ⇒ A → C ⇒ B → C ⇒ P

    project₁ : π₁ ∘ ⟨ h , i ⟩ ≈ h
    project₂ : π₂ ∘ ⟨ h , i ⟩ ≈ i
    unique   : π₁ ∘ h ≈ i → π₂ ∘ h ≈ j → ⟨ i , j ⟩ ≈ h

Product⇒IsProduct : (p : Product A B) → IsProduct (Product.π₁ p) (Product.π₂ p)
Product⇒IsProduct p = record
  { ⟨_,_⟩    = ⟨_,_⟩
  ; project₁ = project₁
  ; project₂ = project₂
  ; unique   = unique
  }
  where open Product p

IsProduct⇒Product : ∀ {P} {π₁ : P ⇒ A} {π₂ : P ⇒ B} → IsProduct π₁ π₂ → Product A B
IsProduct⇒Product p = record
  { ⟨_,_⟩    = ⟨_,_⟩
  ; project₁ = project₁
  ; project₂ = project₂
  ; unique   = unique
  }
  where open IsProduct p

module _ {A B : Obj} where
  open Product {A} {B} renaming (⟨_,_⟩ to _⟨_,_⟩)

  repack : (p₁ p₂ : Product A B) → A×B p₁ ⇒ A×B p₂
  repack p₁ p₂ = p₂ ⟨ π₁ p₁ , π₂ p₁ ⟩

  repack∘ : (p₁ p₂ p₃ : Product A B) → repack p₂ p₃ ∘ repack p₁ p₂ ≈ repack p₁ p₃
  repack∘ p₁ p₂ p₃ = ⟺ $ unique p₃
    (glueTrianglesʳ (project₁ p₃) (project₁ p₂))
    (glueTrianglesʳ (project₂ p₃) (project₂ p₂))

  repack≡id : (p : Product A B) → repack p p ≈ id
  repack≡id = η

  repack-cancel : (p₁ p₂ : Product A B) → repack p₁ p₂ ∘ repack p₂ p₁ ≈ id
  repack-cancel p₁ p₂ = repack∘ p₂ p₁ p₂ ○ repack≡id p₂

up-to-iso : ∀ (p₁ p₂ : Product A B) → Product.A×B p₁ ≅ Product.A×B p₂
up-to-iso p₁ p₂ = record
  { from = repack p₁ p₂
  ; to   = repack p₂ p₁
  ; iso  = record
    { isoˡ = repack-cancel p₂ p₁
    ; isoʳ = repack-cancel p₁ p₂
    }
  }

transport-by-iso : ∀ (p : Product A B) → ∀ {X} → Product.A×B p ≅ X → Product A B
transport-by-iso p {X} p≅X = record
  { A×B = X
  ; π₁ = π₁ ∘ to
  ; π₂ = π₂ ∘ to
  ; ⟨_,_⟩ = λ h₁ h₂ → from ∘ ⟨ h₁ , h₂ ⟩
  ; project₁ = cancelInner isoˡ ○ project₁
  ; project₂ = cancelInner isoˡ ○ project₂
  ; unique = λ {_ i l r} pf₁ pf₂ → begin
    from ∘ ⟨ l , r ⟩                         ≈˘⟨ refl⟩∘⟨ ⟨⟩-cong₂ pf₁ pf₂ ⟩
    from ∘ ⟨ (π₁ ∘ to) ∘ i , (π₂ ∘ to) ∘ i ⟩ ≈⟨ refl⟩∘⟨ unique sym-assoc sym-assoc ⟩
    from ∘ to ∘ i                            ≈⟨ cancelˡ isoʳ ⟩
    i                                        ∎
  }
  where open Product p
        open _≅_ p≅X

Reversible : (p : Product A B) → Product B A
Reversible p = record
  { A×B       = A×B
  ; π₁        = π₂
  ; π₂        = π₁
  ; ⟨_,_⟩     = flip ⟨_,_⟩
  ; project₁  = project₂
  ; project₂  = project₁
  ; unique = flip unique
  }
  where open Product p

Commutative : (p₁ : Product A B) (p₂ : Product B A) → Product.A×B p₁ ≅ Product.A×B p₂
Commutative p₁ p₂ = up-to-iso p₁ (Reversible p₂)

Associable : ∀ (p₁ : Product X Y) (p₂ : Product Y Z) (p₃ : Product X (Product.A×B p₂)) → Product (Product.A×B p₁) Z
Associable p₁ p₂ p₃ = record
  { A×B       = A×B p₃
  ; π₁        = p₁ ⟨ π₁ p₃ , π₁ p₂ ∘ π₂ p₃ ⟩
  ; π₂        = π₂ p₂ ∘ π₂ p₃
  ; ⟨_,_⟩     = λ f g → p₃ ⟨ π₁ p₁ ∘ f , p₂ ⟨ π₂ p₁ ∘ f , g ⟩ ⟩
  ; project₁  = λ {_ f g} → begin
    p₁ ⟨ π₁ p₃ , π₁ p₂ ∘ π₂ p₃ ⟩ ∘ p₃ ⟨ π₁ p₁ ∘ f , p₂ ⟨ π₂ p₁ ∘ f , g ⟩ ⟩ ≈⟨ ∘-distribʳ-⟨⟩ p₁ ⟩
    p₁ ⟨ π₁ p₃ ∘ p₃ ⟨ π₁ p₁ ∘ f , p₂ ⟨ π₂ p₁ ∘ f , g ⟩ ⟩
       , (π₁ p₂ ∘ π₂ p₃) ∘ p₃ ⟨ π₁ p₁ ∘ f , p₂ ⟨ π₂ p₁ ∘ f , g ⟩ ⟩ ⟩       ≈⟨ ⟨⟩-cong₂ p₁ (project₁ p₃) (glueTrianglesˡ (project₁ p₂) (project₂ p₃)) ⟩
    p₁ ⟨ π₁ p₁ ∘ f , π₂ p₁ ∘ f ⟩                                           ≈⟨ g-η p₁ ⟩
    f                                                                      ∎
  ; project₂  = λ {_ f g} → glueTrianglesˡ (project₂ p₂) (project₂ p₃)
  ; unique = λ {_ i f g} pf₁ pf₂ → begin
    p₃ ⟨ π₁ p₁ ∘ f , p₂ ⟨ π₂ p₁ ∘ f , g ⟩ ⟩             ≈⟨ ⟨⟩-cong₂ p₃ (∘-resp-≈ʳ (sym pf₁))
                                                          (⟨⟩-cong₂ p₂ (∘-resp-≈ʳ (sym pf₁)) (sym pf₂)) ⟩
    p₃ ⟨ π₁ p₁ ∘ p₁ ⟨ π₁ p₃ , π₁ p₂ ∘ π₂ p₃ ⟩ ∘ i
       , p₂ ⟨ π₂ p₁ ∘ p₁ ⟨ π₁ p₃ , π₁ p₂ ∘ π₂ p₃ ⟩ ∘ i
            , (π₂ p₂ ∘ π₂ p₃) ∘ i ⟩ ⟩                   ≈⟨ ⟨⟩-cong₂ p₃ (pullˡ (project₁ p₁))
                                                          (⟨⟩-cong₂ p₂ (trans (pullˡ (project₂ p₁)) assoc)
                                                                       assoc) ⟩
    p₃ ⟨ π₁ p₃ ∘ i
       , p₂ ⟨ π₁ p₂ ∘ π₂ p₃ ∘ i , π₂ p₂ ∘ π₂ p₃ ∘ i ⟩ ⟩ ≈⟨ ⟨⟩-cong₂ p₃ refl (g-η p₂) ⟩
    p₃ ⟨ π₁ p₃ ∘ i , π₂ p₃ ∘ i ⟩                        ≈⟨ g-η p₃ ⟩
    i                                                   ∎
  }
  where
  open Product renaming (⟨_,_⟩ to _⟨_,_⟩)
  open Equiv

Associative : ∀ (p₁ : Product X Y) (p₂ : Product Y Z)
                (p₃ : Product X (Product.A×B p₂)) (p₄ : Product (Product.A×B p₁) Z) →
                (Product.A×B p₃) ≅ (Product.A×B p₄)
Associative p₁ p₂ p₃ p₄ = up-to-iso (Associable p₁ p₂ p₃) p₄

Mobile : ∀ {A₁ B₁ A₂ B₂} (p : Product A₁ B₁) → A₁ ≅ A₂ → B₁ ≅ B₂ → Product A₂ B₂
Mobile p A₁≅A₂ B₁≅B₂ = record
  { A×B              = A×B
  ; π₁               = from A₁≅A₂ ∘ π₁
  ; π₂               = from B₁≅B₂ ∘ π₂
  ; ⟨_,_⟩            = λ h k → ⟨ to A₁≅A₂ ∘ h , to B₁≅B₂ ∘ k ⟩
  ; project₁         = begin
    (from A₁≅A₂ ∘ π₁) ∘ ⟨ to A₁≅A₂ ∘ _ , to B₁≅B₂ ∘ _ ⟩ ≈⟨ pullʳ project₁ ⟩
    from A₁≅A₂ ∘ (to A₁≅A₂ ∘ _)                         ≈⟨ cancelˡ (isoʳ A₁≅A₂) ⟩
    _                                                   ∎
  ; project₂         = begin
    (from B₁≅B₂ ∘ π₂) ∘ ⟨ to A₁≅A₂ ∘ _ , to B₁≅B₂ ∘ _ ⟩ ≈⟨ pullʳ project₂ ⟩
    from B₁≅B₂ ∘ (to B₁≅B₂ ∘ _)                         ≈⟨ cancelˡ (isoʳ B₁≅B₂) ⟩
    _                                                   ∎
  ; unique        = λ pfˡ pfʳ → unique (switch-fromtoˡ A₁≅A₂ (sym-assoc ○ pfˡ))
                                       (switch-fromtoˡ B₁≅B₂ (sym-assoc ○ pfʳ))
  }
  where open Product p
        open _≅_

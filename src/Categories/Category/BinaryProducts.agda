{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)

-- Defines BinaryProducts -- for when a Category has all Binary Products

module Categories.Category.BinaryProducts {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level hiding (suc)
open import Data.Product using (uncurry)

open Category 𝒞
open HomReasoning

open import Categories.Object.Product 𝒞
open import Categories.Morphism 𝒞 using (_≅_; module Iso; Mono; Epi)
open import Categories.Morphism.Reasoning 𝒞 using (pullʳ; pullˡ; elimʳ; cancelˡ; cancelʳ; introˡ; introʳ)
open import Categories.Category.Monoidal.Core using (Monoidal)

open import Categories.Functor using (Functor) renaming (id to idF)
open import Categories.Functor.Bifunctor using (Bifunctor; appʳ; appˡ)

private
  variable
    A B C D X Y Z : Obj
    f f′ g g′ h i : A ⇒ B

record BinaryProducts : Set (levelOfTerm 𝒞) where

  infixr 7 _×_
  infixr 8 _⁂_
  infix 11 ⟨_,_⟩

  field
    product : ∀ {A B} → Product A B

  private
    module product {A} {B} = Product (product {A} {B})

  _×_ : Obj → Obj → Obj
  A × B = Product.A×B (product {A} {B})

  ×-comm : A × B ≅ B × A
  ×-comm = Commutative product product

  ×-assoc : X × Y × Z ≅ (X × Y) × Z
  ×-assoc = Associative product product product product

  open product hiding (⟨_,_⟩; ∘-distribʳ-⟨⟩) public

  -- define it like this instead of reexporting to redefine fixity
  ⟨_,_⟩ : X ⇒ A → X ⇒ B → X ⇒ A × B
  ⟨_,_⟩ = Product.⟨_,_⟩ product

  _⁂_ : A ⇒ B → C ⇒ D → A × C ⇒ B × D
  f ⁂ g = [ product ⇒ product ] f × g

  assocˡ : (A × B) × C ⇒ A × B × C
  assocˡ = _≅_.to ×-assoc

  assocʳ : A × B × C ⇒ (A × B) × C
  assocʳ = _≅_.from ×-assoc

  assocʳ∘assocˡ : assocʳ {A}{B}{C} ∘ assocˡ {A}{B}{C} ≈ id
  assocʳ∘assocˡ = Iso.isoʳ (_≅_.iso ×-assoc)

  assocˡ∘assocʳ : assocˡ {A}{B}{C} ∘ assocʳ {A}{B}{C} ≈ id
  assocˡ∘assocʳ = Iso.isoˡ (_≅_.iso ×-assoc)

  ⟨⟩-congʳ : f ≈ f′ → ⟨ f , g ⟩ ≈ ⟨ f′ , g ⟩
  ⟨⟩-congʳ pf = ⟨⟩-cong₂ pf Equiv.refl

  ⟨⟩-congˡ : g ≈ g′ → ⟨ f , g ⟩ ≈ ⟨ f , g′ ⟩
  ⟨⟩-congˡ pf = ⟨⟩-cong₂ Equiv.refl pf

  swap : A × B ⇒ B × A
  swap = ⟨ π₂ , π₁ ⟩

  -- TODO: this is probably harder to use than necessary because of this definition. Maybe make a version
  -- that doesn't have an explicit id in it, too?
  first : A ⇒ B → A × C ⇒ B × C
  first f = f ⁂ id

  second : C ⇒ D → A × C ⇒ A × D
  second g = id ⁂ g

  first-cong : f ≈ g → first {C = C} f ≈ first g
  first-cong f≈g = ⟨⟩-congʳ (∘-resp-≈ˡ f≈g)

  second-cong : f ≈ g → second {A = A} f ≈ second g
  second-cong f≈g = ⟨⟩-congˡ (∘-resp-≈ˡ f≈g)

  -- Just to make this more obvious
  π₁∘⁂ : π₁ ∘ (f ⁂ g) ≈ f ∘ π₁
  π₁∘⁂ {f = f} {g} = project₁

  π₂∘⁂ : π₂ ∘ (f ⁂ g) ≈ g ∘ π₂
  π₂∘⁂ {f = f} {g} = project₂

  π₂∘fist : π₂ ∘ first f ≈ π₂ {_}{C}
  π₂∘fist = π₂∘⁂ ○ identityˡ

  π₁∘second : π₁ ∘ second f ≈ π₁ {C}
  π₁∘second = π₁∘⁂ ○ identityˡ

  ⁂-cong₂ : f ≈ g → h ≈ i → f ⁂ h ≈ g ⁂ i
  ⁂-cong₂ = [ product ⇒ product ]×-cong₂

  ⁂∘⟨⟩ : (f ⁂ g) ∘ ⟨ f′ , g′ ⟩ ≈ ⟨ f ∘ f′ , g ∘ g′ ⟩
  ⁂∘⟨⟩ = [ product ⇒ product ]×∘⟨⟩

  first∘⟨⟩ : first f ∘ ⟨ f′ , g′ ⟩ ≈ ⟨ f ∘ f′ , g′ ⟩
  first∘⟨⟩ = [ product ⇒ product ]×id∘⟨⟩

  second∘⟨⟩ : second g ∘ ⟨ f′ , g′ ⟩ ≈ ⟨ f′ , g ∘ g′ ⟩
  second∘⟨⟩ = [ product ⇒ product ]id×∘⟨⟩

  ⁂∘⁂ : (f ⁂ g) ∘ (f′ ⁂ g′) ≈ (f ∘ f′) ⁂ (g ∘ g′)
  ⁂∘⁂ = [ product ⇒ product ⇒ product ]×∘×

  first∘⁂ : first f ∘ (f′ ⁂ g′) ≈ (f ∘ f′ ⁂ g′)
  first∘⁂ = ⁂∘⁂ ○ ⁂-cong₂ Equiv.refl identityˡ

  second∘⁂ : second g ∘ (f′ ⁂ g′) ≈ (f′ ⁂ g ∘ g′)
  second∘⁂ = ⁂∘⁂ ○ ⁂-cong₂ identityˡ Equiv.refl

  ⟨⟩∘ : ⟨ f , g ⟩ ∘ h ≈ ⟨ f ∘ h , g ∘ h ⟩
  ⟨⟩∘ = [ product ]⟨⟩∘

  first∘first : ∀ {C} → first {C = C} f ∘ first g ≈ first (f ∘ g)
  first∘first = [ product ⇒ product ⇒ product ]×id∘×id

  second∘second : ∀ {A} → second {A = A} f ∘ second g ≈ second (f ∘ g)
  second∘second = [ product ⇒ product ⇒ product ]id×∘id×

  first∘second : first f ∘ second g ≈ f ⁂ g
  first∘second {f = f} {g = g} = begin
    first f ∘ second g       ≈⟨ first∘⟨⟩ ⟩
    ⟨ f ∘ id ∘ π₁ , g ∘ π₂ ⟩ ≈⟨ ⟨⟩-congʳ (∘-resp-≈ʳ identityˡ) ⟩
    f ⁂ g                    ∎

  second∘first : second f ∘ first g ≈ g ⁂ f
  second∘first {f = f} {g = g} = begin
    second f ∘ first g ≈⟨ second∘⟨⟩ ⟩
    ⟨ g ∘ π₁ , f ∘ id ∘ π₂ ⟩ ≈⟨ ⟨⟩-congˡ (∘-resp-≈ʳ identityˡ) ⟩
    g ⁂ f ∎

  first↔second : first f ∘ second g ≈ second g ∘ first f
  first↔second = [ product ⇒ product , product ⇒ product ]first↔second

  firstid : ∀ {f : A ⇒ A} (g : A ⇒ C) → first {C = C} f ≈ id → f ≈ id
  firstid {f = f} g eq = begin
    f                    ≈˘⟨ elimʳ project₁ ⟩
    f ∘ π₁ ∘ ⟨ id , g ⟩  ≈⟨ pullˡ fπ₁≈π₁ ⟩
    π₁ ∘ ⟨ id , g ⟩      ≈⟨ project₁ ⟩
    id                   ∎
    where fπ₁≈π₁ = begin
            f ∘ π₁       ≈˘⟨ project₁ ⟩
            π₁ ∘ first f ≈⟨ refl⟩∘⟨ eq ⟩
            π₁ ∘ id      ≈⟨ identityʳ ⟩
            π₁           ∎

  swap∘⟨⟩ : swap ∘ ⟨ f , g ⟩ ≈ ⟨ g , f ⟩
  swap∘⟨⟩ {f = f} {g = g} = begin
    ⟨ π₂ , π₁ ⟩ ∘ ⟨ f , g ⟩             ≈⟨ ⟨⟩∘ ⟩
    ⟨ π₂ ∘ ⟨ f , g ⟩ , π₁ ∘ ⟨ f , g ⟩ ⟩ ≈⟨ ⟨⟩-cong₂ project₂ project₁ ⟩
    ⟨ g , f ⟩                           ∎

  swap∘⁂ : swap ∘ (f ⁂ g) ≈ (g ⁂ f) ∘ swap
  swap∘⁂ {f = f} {g = g} = begin
    swap ∘ (f ⁂ g)      ≈⟨ swap∘⟨⟩ ⟩
    ⟨ g ∘ π₂ , f ∘ π₁ ⟩  ≈˘⟨ ⁂∘⟨⟩ ⟩
    (g ⁂ f) ∘ swap      ∎

  swap∘swap : (swap {A}{B}) ∘ (swap {B}{A}) ≈ id
  swap∘swap = Equiv.trans swap∘⟨⟩ η

  swap-epi : Epi (swap {A} {B})
  swap-epi f g eq = (introʳ swap∘swap) ○ (pullˡ eq) ○ (cancelʳ swap∘swap)

  swap-mono : Mono (swap {A} {B})
  swap-mono f g eq = (introˡ swap∘swap) ○ (pullʳ eq) ○ (cancelˡ swap∘swap)

  assocʳ∘⟨⟩ : assocʳ ∘ ⟨ f , ⟨ g , h ⟩ ⟩ ≈ ⟨ ⟨ f , g ⟩ , h ⟩
  assocʳ∘⟨⟩ {f = f} {g = g} {h = h} = begin
    assocʳ ∘ ⟨ f , ⟨ g , h ⟩ ⟩ ≈⟨ ⟨⟩∘ ⟩
    ⟨ ⟨ π₁ , π₁ ∘ π₂ ⟩ ∘ ⟨ f , ⟨ g , h ⟩ ⟩
    , (π₂ ∘ π₂) ∘ ⟨ f , ⟨ g , h ⟩ ⟩
    ⟩                          ≈⟨ ⟨⟩-cong₂ ⟨⟩∘ (pullʳ project₂) ⟩
    ⟨ ⟨ π₁        ∘ ⟨ f , ⟨ g , h ⟩ ⟩
      , (π₁ ∘ π₂) ∘ ⟨ f , ⟨ g , h ⟩ ⟩
      ⟩
    , π₂ ∘ ⟨ g , h ⟩
    ⟩                          ≈⟨ ⟨⟩-cong₂ (⟨⟩-cong₂ project₁
                                                     (pullʳ project₂ ○ project₁))
                                           project₂ ⟩
    ⟨ ⟨ f , g ⟩ , h ⟩          ∎

  assocˡ∘⟨⟩ : assocˡ ∘ ⟨ ⟨ f , g ⟩ , h ⟩ ≈ ⟨ f , ⟨ g , h ⟩ ⟩
  assocˡ∘⟨⟩ {f = f} {g = g} {h = h} = begin
    assocˡ ∘ ⟨ ⟨ f , g ⟩ , h ⟩          ≈˘⟨ refl⟩∘⟨ assocʳ∘⟨⟩ ⟩
    assocˡ ∘ assocʳ ∘ ⟨ f , ⟨ g , h ⟩ ⟩ ≈⟨ cancelˡ assocˡ∘assocʳ ⟩
    ⟨ f , ⟨ g , h ⟩ ⟩                   ∎

  assocʳ∘⁂ : assocʳ ∘ (f ⁂ (g ⁂ h)) ≈ ((f ⁂ g) ⁂ h) ∘ assocʳ
  assocʳ∘⁂ {f = f} {g = g} {h = h} =
    begin
      assocʳ ∘ (f ⁂ (g ⁂ h))
    ≈⟨ refl⟩∘⟨ ⟨⟩-congˡ ⟨⟩∘ ⟩
      assocʳ ∘ ⟨ f ∘ π₁ , ⟨ (g ∘ π₁) ∘ π₂ , (h ∘ π₂) ∘ π₂ ⟩ ⟩
    ≈⟨ assocʳ∘⟨⟩ ⟩
      ⟨ ⟨ f ∘ π₁ , (g ∘ π₁) ∘ π₂ ⟩ , (h ∘ π₂) ∘ π₂ ⟩
    ≈⟨ ⟨⟩-cong₂ (⟨⟩-congˡ assoc) assoc ⟩
      ⟨ ⟨ f ∘ π₁ , g ∘ π₁ ∘ π₂ ⟩ , h ∘ π₂ ∘ π₂ ⟩
    ≈˘⟨ ⟨⟩-congʳ ⁂∘⟨⟩ ⟩
      ⟨ (f ⁂ g) ∘ ⟨ π₁ , π₁ ∘ π₂ ⟩ , h ∘ π₂ ∘ π₂ ⟩
    ≈˘⟨ ⁂∘⟨⟩ ⟩
      ((f ⁂ g) ⁂ h) ∘ assocʳ
    ∎

  assocˡ∘⁂ : assocˡ ∘ ((f ⁂ g) ⁂ h) ≈ (f ⁂ (g ⁂ h)) ∘ assocˡ
  assocˡ∘⁂ {f = f} {g = g} {h = h} =
    begin
      assocˡ ∘ ((f ⁂ g) ⁂ h)
    ≈⟨ refl⟩∘⟨ ⟨⟩-congʳ ⟨⟩∘ ⟩
      assocˡ ∘ ⟨ ⟨ (f ∘ π₁) ∘ π₁ , (g ∘ π₂) ∘ π₁ ⟩ , h ∘ π₂ ⟩
    ≈⟨ assocˡ∘⟨⟩ ⟩
      ⟨ (f ∘ π₁) ∘ π₁ , ⟨ (g ∘ π₂) ∘ π₁ , h ∘ π₂ ⟩ ⟩
    ≈⟨ ⟨⟩-cong₂ assoc (⟨⟩-congʳ assoc) ⟩
      ⟨ f ∘ π₁ ∘ π₁ , ⟨ g ∘ π₂ ∘ π₁ , h ∘ π₂ ⟩ ⟩
    ≈˘⟨ ⟨⟩-congˡ ⁂∘⟨⟩ ⟩
      ⟨ f ∘ π₁ ∘ π₁ , (g ⁂ h) ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
    ≈˘⟨ ⁂∘⟨⟩ ⟩
      (f ⁂ (g ⁂ h)) ∘ assocˡ
    ∎

  Δ : ∀ {C} → C ⇒ C × C
  Δ {C} = ⟨ id {C} , id ⟩

  Δ∘ : Δ ∘ f ≈ ⟨ f , f ⟩
  Δ∘ {f = f} = begin
    Δ ∘ f               ≈⟨ ⟨⟩∘ ⟩
    ⟨ id ∘ f , id ∘ f ⟩ ≈⟨ ⟨⟩-cong₂ identityˡ identityˡ ⟩
    ⟨ f , f ⟩           ∎

  ⁂∘Δ : (f ⁂ g) ∘ Δ ≈ ⟨ f , g ⟩
  ⁂∘Δ {f = f} {g = g} = begin
    (f ⁂ g) ∘ Δ         ≈⟨ ⁂∘⟨⟩ ⟩
    ⟨ f ∘ id , g ∘ id ⟩ ≈⟨ ⟨⟩-cong₂ identityʳ identityʳ ⟩
    ⟨ f , g ⟩           ∎

  -×- : Bifunctor 𝒞 𝒞 𝒞
  -×- = record
    { F₀           = uncurry _×_
    ; F₁           = uncurry _⁂_
    ; identity     = id×id product
    ; homomorphism = ⟺ ⁂∘⁂
    ; F-resp-≈     = uncurry [ product ⇒ product ]×-cong₂
    }

  -×_ : Obj → Functor 𝒞 𝒞
  -×_ = appʳ -×-

  _×- : Obj → Functor 𝒞 𝒞
  _×- = appˡ -×-

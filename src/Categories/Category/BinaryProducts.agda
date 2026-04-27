{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)

-- Defines BinaryProducts -- for when a Category has all Binary Products

module Categories.Category.BinaryProducts {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level using (levelOfTerm)
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
  infixr 8 _×₁_

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

  open product renaming (⟨_,_⟩ to infix 11 ⟨_,_⟩) public

  _×₁_ : A ⇒ B → C ⇒ D → A × C ⇒ B × D
  f ×₁ g = [ product ⇒ product ] f × g

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
  first f = f ×₁ id

  second : C ⇒ D → A × C ⇒ A × D
  second g = id ×₁ g

  -- Just to make this more obvious
  π₁∘×₁ : π₁ ∘ (f ×₁ g) ≈ f ∘ π₁
  π₁∘×₁ {f = f} {g} = project₁

  π₂∘×₁ : π₂ ∘ (f ×₁ g) ≈ g ∘ π₂
  π₂∘×₁ {f = f} {g} = project₂

  ×₁-cong₂ : f ≈ g → h ≈ i → f ×₁ h ≈ g ×₁ i
  ×₁-cong₂ = [ product ⇒ product ]×-cong₂

  ×₁∘⟨⟩ : (f ×₁ g) ∘ ⟨ f′ , g′ ⟩ ≈ ⟨ f ∘ f′ , g ∘ g′ ⟩
  ×₁∘⟨⟩ = [ product ⇒ product ]×∘⟨⟩

  first∘⟨⟩ : first f ∘ ⟨ f′ , g′ ⟩ ≈ ⟨ f ∘ f′ , g′ ⟩
  first∘⟨⟩ = [ product ⇒ product ]×id∘⟨⟩

  second∘⟨⟩ : second g ∘ ⟨ f′ , g′ ⟩ ≈ ⟨ f′ , g ∘ g′ ⟩
  second∘⟨⟩ = [ product ⇒ product ]id×∘⟨⟩

  ×₁∘×₁ : (f ×₁ g) ∘ (f′ ×₁ g′) ≈ (f ∘ f′) ×₁ (g ∘ g′)
  ×₁∘×₁ = [ product ⇒ product ⇒ product ]×∘×

  ⟨⟩∘ : ⟨ f , g ⟩ ∘ h ≈ ⟨ f ∘ h , g ∘ h ⟩
  ⟨⟩∘ = [ product ]⟨⟩∘

  first∘first : ∀ {C} → first {C = C} f ∘ first g ≈ first (f ∘ g)
  first∘first = [ product ⇒ product ⇒ product ]×id∘×id

  second∘second : ∀ {A} → second {A = A} f ∘ second g ≈ second (f ∘ g)
  second∘second = [ product ⇒ product ⇒ product ]id×∘id×

  first∘second : first f ∘ second g ≈ f ×₁ g
  first∘second {f = f} {g = g} = begin
    first f ∘ second g       ≈⟨ first∘⟨⟩ ⟩
    ⟨ f ∘ id ∘ π₁ , g ∘ π₂ ⟩ ≈⟨ ⟨⟩-congʳ (∘-resp-≈ʳ identityˡ) ⟩
    f ×₁ g                   ∎

  second∘first : second f ∘ first g ≈ g ×₁ f
  second∘first {f = f} {g = g} = begin
    second f ∘ first g       ≈⟨ second∘⟨⟩ ⟩
    ⟨ g ∘ π₁ , f ∘ id ∘ π₂ ⟩ ≈⟨ ⟨⟩-congˡ (∘-resp-≈ʳ identityˡ) ⟩
    g ×₁ f                   ∎

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

  swap∘×₁ : swap ∘ (f ×₁ g) ≈ (g ×₁ f) ∘ swap
  swap∘×₁ {f = f} {g = g} = begin
    swap ∘ (f ×₁ g)      ≈⟨ swap∘⟨⟩ ⟩
    ⟨ g ∘ π₂ , f ∘ π₁ ⟩  ≈˘⟨ ×₁∘⟨⟩ ⟩
    (g ×₁ f) ∘ swap      ∎

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

  assocʳ∘×₁ : assocʳ ∘ (f ×₁ (g ×₁ h)) ≈ ((f ×₁ g) ×₁ h) ∘ assocʳ
  assocʳ∘×₁ {f = f} {g = g} {h = h} =
    begin
      assocʳ ∘ (f ×₁ (g ×₁ h))
    ≈⟨ refl⟩∘⟨ ⟨⟩-congˡ ⟨⟩∘ ⟩
      assocʳ ∘ ⟨ f ∘ π₁ , ⟨ (g ∘ π₁) ∘ π₂ , (h ∘ π₂) ∘ π₂ ⟩ ⟩
    ≈⟨ assocʳ∘⟨⟩ ⟩
      ⟨ ⟨ f ∘ π₁ , (g ∘ π₁) ∘ π₂ ⟩ , (h ∘ π₂) ∘ π₂ ⟩
    ≈⟨ ⟨⟩-cong₂ (⟨⟩-congˡ assoc) assoc ⟩
      ⟨ ⟨ f ∘ π₁ , g ∘ π₁ ∘ π₂ ⟩ , h ∘ π₂ ∘ π₂ ⟩
    ≈˘⟨ ⟨⟩-congʳ ×₁∘⟨⟩ ⟩
      ⟨ (f ×₁ g) ∘ ⟨ π₁ , π₁ ∘ π₂ ⟩ , h ∘ π₂ ∘ π₂ ⟩
    ≈˘⟨ ×₁∘⟨⟩ ⟩
      ((f ×₁ g) ×₁ h) ∘ assocʳ
    ∎

  assocˡ∘×₁ : assocˡ ∘ ((f ×₁ g) ×₁ h) ≈ (f ×₁ (g ×₁ h)) ∘ assocˡ
  assocˡ∘×₁ {f = f} {g = g} {h = h} =
    begin
      assocˡ ∘ ((f ×₁ g) ×₁ h)
    ≈⟨ refl⟩∘⟨ ⟨⟩-congʳ ⟨⟩∘ ⟩
      assocˡ ∘ ⟨ ⟨ (f ∘ π₁) ∘ π₁ , (g ∘ π₂) ∘ π₁ ⟩ , h ∘ π₂ ⟩
    ≈⟨ assocˡ∘⟨⟩ ⟩
      ⟨ (f ∘ π₁) ∘ π₁ , ⟨ (g ∘ π₂) ∘ π₁ , h ∘ π₂ ⟩ ⟩
    ≈⟨ ⟨⟩-cong₂ assoc (⟨⟩-congʳ assoc) ⟩
      ⟨ f ∘ π₁ ∘ π₁ , ⟨ g ∘ π₂ ∘ π₁ , h ∘ π₂ ⟩ ⟩
    ≈˘⟨ ⟨⟩-congˡ ×₁∘⟨⟩ ⟩
      ⟨ f ∘ π₁ ∘ π₁ , (g ×₁ h) ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
    ≈˘⟨ ×₁∘⟨⟩ ⟩
      (f ×₁ (g ×₁ h)) ∘ assocˡ
    ∎

  Δ : ∀ {C} → C ⇒ C × C
  Δ {C} = ⟨ id {C} , id ⟩

  Δ∘ : Δ ∘ f ≈ ⟨ f , f ⟩
  Δ∘ {f = f} = begin
    Δ ∘ f               ≈⟨ ⟨⟩∘ ⟩
    ⟨ id ∘ f , id ∘ f ⟩ ≈⟨ ⟨⟩-cong₂ identityˡ identityˡ ⟩
    ⟨ f , f ⟩           ∎

  ×₁∘Δ : (f ×₁ g) ∘ Δ ≈ ⟨ f , g ⟩
  ×₁∘Δ {f = f} {g = g} = begin
    (f ×₁ g) ∘ Δ        ≈⟨ ×₁∘⟨⟩ ⟩
    ⟨ f ∘ id , g ∘ id ⟩ ≈⟨ ⟨⟩-cong₂ identityʳ identityʳ ⟩
    ⟨ f , g ⟩           ∎

  -×- : Bifunctor 𝒞 𝒞 𝒞
  -×- = record
    { F₀           = uncurry _×_
    ; F₁           = uncurry _×₁_
    ; identity     = id×id product
    ; homomorphism = ⟺ ×₁∘×₁
    ; F-resp-≈     = uncurry [ product ⇒ product ]×-cong₂
    }

  -×_ : Obj → Functor 𝒞 𝒞
  -×_ = appʳ -×-

  _×- : Obj → Functor 𝒞 𝒞
  _×- = appˡ -×-

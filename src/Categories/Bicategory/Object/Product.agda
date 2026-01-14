{-# OPTIONS --without-K --safe #-}
open import Categories.Bicategory using (Bicategory)

module Categories.Bicategory.Object.Product {o ℓ e t} (𝒞 : Bicategory o ℓ e t) where

open import Level
open import Data.Product using (_,_; uncurry; uncurry′)

open import Categories.Bicategory.Extras 𝒞
open import Categories.Category using (_[_,_])
open import Categories.Category.Equivalence using (StrongEquivalence)
open import Categories.Category.Product using (_※_; _※ⁿⁱ_; πˡ; πʳ) renaming (Product to CatProduct)
open import Categories.Functor using (_∘F_) renaming (id to idF)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.Morphism using (_≅_)
open import Categories.Morphism.HeterogeneousEquality
open import Categories.Morphism.Notation using (_[_≅_])
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_; sym)
open import Categories.NaturalTransformation.NaturalIsomorphism.Properties using (pointwise-iso)

import Categories.Morphism.Reasoning as MR

open hom.HomReasoning

private
  module MR′ {X Y} = MR (hom X Y)

record Product (A B : Obj) : Set (o ⊔ ℓ ⊔ e ⊔ t) where
  infix 10 ⟨_,_⟩₁ ⟨_,_⟩₂
  field
    A×B : Obj
    πa : A×B ⇒₁ A
    πb : A×B ⇒₁ B
    ⟨_,_⟩₁ : ∀ {Γ} → Γ ⇒₁ A → Γ ⇒₁ B → Γ ⇒₁ A×B
    ⟨_,_⟩₂ : ∀ {Γ}{fa ga : Γ ⇒₁ A}{fb gb : Γ ⇒₁ B}
           → fa ⇒₂ ga → fb ⇒₂ gb → ⟨ fa , fb ⟩₁ ⇒₂ ⟨ ga , gb ⟩₁
    ⟨⟩-resp-≈ : ∀ {Γ}{fa ga : Γ ⇒₁ A}{fb gb : Γ ⇒₁ B}{αa βa : fa ⇒₂ ga}{αb βb : fb ⇒₂ gb}
              → αa ≈ βa → αb ≈ βb → ⟨ αa , αb ⟩₂ ≈ ⟨ βa , βb ⟩₂

    β₁a : ∀ {Γ} f g → hom Γ A [ πa ∘₁ ⟨ f , g ⟩₁  ≅ f ]
    β₁b : ∀ {Γ} f g → hom Γ B [ πb ∘₁ ⟨ f , g ⟩₁  ≅ g ]
    β₂a : ∀ {Γ}{fa ga fb gb}(αa : hom Γ A [ fa , ga ])(αb : hom Γ B [ fb , gb ])
        → Along β₁a _ _ , β₁a _ _ [ πa ▷ ⟨ αa , αb ⟩₂ ≈ αa ]
    β₂b : ∀ {Γ}{fa ga fb gb}(αa : hom Γ A [ fa , ga ])(αb : hom Γ B [ fb , gb ])
        → Along β₁b _ _ , β₁b _ _ [ πb ▷ ⟨ αa , αb ⟩₂ ≈ αb ]

    η₁ : ∀ {Γ} p → hom Γ A×B [ p ≅ ⟨ πa ∘₁ p , πb ∘₁ p ⟩₁ ]
    η₂ : ∀ {Γ}{p p'}(ϕ : hom Γ A×B [ p , p' ])
       → Along (η₁ _) , (η₁ _) [ ϕ ≈ ⟨ πa ▷ ϕ , πb ▷ ϕ ⟩₂ ]

  module β₁a {Γ} f g = _≅_ (β₁a {Γ} f g)
  module β₁b {Γ} f g = _≅_ (β₁b {Γ} f g)
  module η₁ {Γ} p = _≅_ (η₁ {Γ} p)

  unique₂ : ∀ {Γ}{p p'}{ϕ ψ : hom Γ A×B [ p , p' ]} → πa ▷ ϕ ≈ πa ▷ ψ → πb ▷ ϕ ≈ πb ▷ ψ → ϕ ≈ ψ
  unique₂ {ϕ = ϕ}{ψ} ϕa≈ψa ϕb≈ψb = begin
    ϕ                                             ≈⟨ MR′.switch-fromtoˡ (η₁ _) (η₂ ϕ) ⟩
    η₁.to _ ∘ᵥ ⟨ πa ▷ ϕ , πb ▷ ϕ ⟩₂ ∘ᵥ η₁.from _  ≈⟨ refl⟩∘⟨ ⟨⟩-resp-≈ ϕa≈ψa ϕb≈ψb ⟩∘⟨refl ⟩
    η₁.to _ ∘ᵥ ⟨ πa ▷ ψ , πb ▷ ψ ⟩₂ ∘ᵥ η₁.from _  ≈⟨ ⟺ (MR′.switch-fromtoˡ (η₁ _) (η₂ ψ)) ⟩
    ψ                                             ∎

  ⟨-,-⟩ : ∀ {Γ} → Bifunctor (hom Γ A) (hom Γ B) (hom Γ A×B)
  ⟨-,-⟩ = record
    { F₀ = uncurry′ ⟨_,_⟩₁
    ; F₁ = uncurry′ ⟨_,_⟩₂
    ; identity = unique₂ (MR′.switch-fromtoˡ (β₁a _ _) (β₂a id₂ id₂) ○ hom.∘-resp-≈ʳ identity₂ˡ
                           ○ β₁a.isoˡ _ _ ○ ⟺ ⊚.identity)
                         (MR′.switch-fromtoˡ (β₁b _ _) (β₂b id₂ id₂) ○ hom.∘-resp-≈ʳ identity₂ˡ
                           ○ β₁b.isoˡ _ _ ○ ⟺ ⊚.identity)
    ; homomorphism = λ{_ _ _ (αa , αb) (βa , βb)}
                   → unique₂ (MR′.switch-fromtoˡ (β₁a _ _) (β₂a (βa ∘ᵥ αa) (βb ∘ᵥ αb))
                                ○ MR′.pushʳ (MR′.extendˡ (MR′.insertˡ (β₁a.isoʳ _ _)))
                                ○ ⟺ (MR′.switch-fromtoˡ (β₁a _ _) (β₂a βa βb)
                                        ⟩∘⟨ MR′.switch-fromtoˡ (β₁a _ _) (β₂a αa αb))
                                ○ ∘ᵥ-distr-▷)
                             (MR′.switch-fromtoˡ (β₁b _ _) (β₂b (βa ∘ᵥ αa) (βb ∘ᵥ αb))
                                ○ MR′.pushʳ (MR′.extendˡ (MR′.insertˡ (β₁b.isoʳ _ _)))
                                ○ ⟺ (MR′.switch-fromtoˡ (β₁b _ _) (β₂b βa βb)
                                        ⟩∘⟨ MR′.switch-fromtoˡ (β₁b _ _) (β₂b αa αb))
                                ○ ∘ᵥ-distr-▷)
    ; F-resp-≈ = uncurry′ ⟨⟩-resp-≈
    }

  βa : ∀ {Γ} → πa ⊚- ∘F ⟨-,-⟩ {Γ} ≃ πˡ
  βa = pointwise-iso (uncurry β₁a) (uncurry β₂a)

  βb : ∀ {Γ} → πb ⊚- ∘F ⟨-,-⟩ {Γ} ≃ πʳ
  βb = pointwise-iso (uncurry β₁b) (uncurry β₂b)

  β : ∀ {Γ} → (πa ⊚- ※ πb ⊚-) ∘F ⟨-,-⟩ {Γ} ≃ idF
  β = βa ※ⁿⁱ βb

  η : ∀ {Γ} → idF ≃ ⟨-,-⟩ {Γ} ∘F (πa ⊚- ※ πb ⊚-)
  η = pointwise-iso η₁ η₂

  𝒞[Γ,A×B]≅𝒞[Γ,A]×𝒞[Γ,B] : ∀ {Γ} → StrongEquivalence (hom Γ A×B) (CatProduct (hom Γ A) (hom Γ B))
  𝒞[Γ,A×B]≅𝒞[Γ,A]×𝒞[Γ,B] = record { F = πa ⊚- ※ πb ⊚- ; G = ⟨-,-⟩
                                  ; weak-inverse = record { F∘G≈id = β ; G∘F≈id = sym η } }

{-# OPTIONS --without-K --safe #-}
module Categories.Category.CartesianClosed.Properties where

open import Level
open import Data.Product using (Σ; _,_; Σ-syntax; proj₁; proj₂)

open import Categories.Category
open import Categories.Category.CartesianClosed


module _ {o ℓ e} {𝒞 : Category o ℓ e} (𝓥 : CartesianClosed 𝒞) where
  open Category 𝒞
  open CartesianClosed 𝓥
  open HomReasoning

  PointSurjective : ∀ {A X Y : Obj} → (X ⇒ Y ^ A) → Set (ℓ ⊔ e)
  PointSurjective {A = A} {X = X} {Y = Y} ϕ =
    ∀ (f : A ⇒ Y) → Σ[ x ∈ ⊤ ⇒ X ] (∀ (a : ⊤ ⇒ A) → eval′ ∘ first ϕ ∘ ⟨ x , a ⟩  ≈ f ∘ a)

  lawvere-fixed-point : ∀ {A B : Obj} → (ϕ : A ⇒ B ^ A) → PointSurjective ϕ → (f : B ⇒ B) → Σ[ s ∈ ⊤ ⇒ B ] f ∘ s ≈ s
  lawvere-fixed-point {A = A} {B = B} ϕ surjective f = g ∘ x , g-fixed-point
    where
      g : A ⇒ B
      g = f ∘ eval′ ∘ ⟨ ϕ , id ⟩

      x : ⊤ ⇒ A
      x = proj₁ (surjective  g)

      g-surjective : eval′ ∘ first ϕ ∘ ⟨ x , x ⟩ ≈ g ∘ x
      g-surjective = proj₂ (surjective g) x

      lemma : ∀ {A B C D} → (f : B ⇒ C) → (g : B ⇒ D) → (h : A ⇒ B) → (f ⁂ g) ∘ ⟨ h , h ⟩ ≈ ⟨ f , g ⟩ ∘ h
      lemma f g h = begin
        (f ⁂ g) ∘ ⟨ h , h ⟩ ≈⟨  ⁂∘⟨⟩ ⟩
        ⟨ f ∘ h , g ∘ h ⟩ ≈⟨ sym ⟨⟩∘ ⟩
        ⟨ f , g ⟩ ∘ h ∎

      g-fixed-point : f ∘ (g ∘ x) ≈ g ∘ x
      g-fixed-point = begin
        f ∘ g ∘ x ≈⟨  refl⟩∘⟨ sym g-surjective ⟩
        f ∘ eval′ ∘ first ϕ ∘ ⟨ x , x ⟩  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ lemma ϕ id x ⟩
        f ∘ eval′ ∘ ⟨ ϕ , id ⟩ ∘ x ≈⟨ sym assoc ○ sym assoc ○ ∘-resp-≈ˡ assoc ⟩
        (f ∘ eval′ ∘ ⟨ ϕ , id ⟩) ∘ x ≈⟨  refl ⟩∘⟨refl ⟩
        g ∘ x ∎


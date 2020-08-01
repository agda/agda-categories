{-# OPTIONS --without-K --safe #-}

module Categories.Category.Equivalence.Properties where

open import Level

open import Categories.Adjoint.Equivalence using (⊣Equivalence)
open import Categories.Adjoint.TwoSided using (_⊣⊢_; withZig)
open import Categories.Category.Core
open import Categories.Category.Equivalence using (WeakInverse; StrongEquivalence)
import Categories.Morphism.Reasoning as MR
import Categories.Morphism.Properties as MP
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Properties using ([_]-resp-Iso)
open import Categories.NaturalTransformation using (ntHelper; _∘ᵥ_; _∘ˡ_; _∘ʳ_)
open import Categories.NaturalTransformation.NaturalIsomorphism as ≃
  using (NaturalIsomorphism ; unitorˡ; unitorʳ; associator; _ⓘᵥ_; _ⓘˡ_; _ⓘʳ_)

private
  variable
    o ℓ e : Level
    C D E : Category o ℓ e

module _ {F : Functor C D} {G : Functor D C} (W : WeakInverse F G) where
  open WeakInverse W

  private
    module C = Category C
    module D = Category D
    module F = Functor F
    module G = Functor G

  -- adjoint equivalence
  F⊣⊢G : F ⊣⊢ G
  F⊣⊢G = withZig record
    { unit   = ≃.sym G∘F≈id
    ; counit =
      let open D
          open HomReasoning
          open MR D
          open MP D
      in record
        { F⇒G = ntHelper record
          { η       = λ X → F∘G≈id.⇒.η X ∘ F.F₁ (G∘F≈id.⇒.η (G.F₀ X)) ∘ F∘G≈id.⇐.η (F.F₀ (G.F₀ X))
          ; commute = λ {X Y} f → begin
            (F∘G≈id.⇒.η Y ∘ F.F₁ (G∘F≈id.⇒.η (G.F₀ Y)) ∘ F∘G≈id.⇐.η (F.F₀ (G.F₀ Y))) ∘ F.F₁ (G.F₁ f)
              ≈⟨ pull-last (F∘G≈id.⇐.commute (F.F₁ (G.F₁ f))) ⟩
            F∘G≈id.⇒.η Y ∘ F.F₁ (G∘F≈id.⇒.η (G.F₀ Y)) ∘ (F.F₁ (G.F₁ (F.F₁ (G.F₁ f))) ∘ F∘G≈id.⇐.η (F.F₀ (G.F₀ X)))
              ≈˘⟨ refl⟩∘⟨ pushˡ F.homomorphism ⟩
            F∘G≈id.⇒.η Y ∘ F.F₁ (G∘F≈id.⇒.η (G.F₀ Y) C.∘ G.F₁ (F.F₁ (G.F₁ f))) ∘ F∘G≈id.⇐.η (F.F₀ (G.F₀ X))
              ≈⟨ refl⟩∘⟨ F.F-resp-≈ (G∘F≈id.⇒.commute (G.F₁ f)) ⟩∘⟨refl ⟩
            F∘G≈id.⇒.η Y ∘ F.F₁ (G.F₁ f C.∘ G∘F≈id.⇒.η (G.F₀ X)) ∘ F∘G≈id.⇐.η (F.F₀ (G.F₀ X))
              ≈⟨ refl⟩∘⟨ F.homomorphism ⟩∘⟨refl ⟩
            F∘G≈id.⇒.η Y ∘ (F.F₁ (G.F₁ f) ∘ F.F₁ (G∘F≈id.⇒.η (G.F₀ X))) ∘ F∘G≈id.⇐.η (F.F₀ (G.F₀ X))
              ≈⟨ center⁻¹ (F∘G≈id.⇒.commute f) Equiv.refl ⟩
            (f ∘ F∘G≈id.⇒.η X) ∘ F.F₁ (G∘F≈id.⇒.η (G.F₀ X)) ∘ F∘G≈id.⇐.η (F.F₀ (G.F₀ X))
              ≈⟨ assoc ⟩
            f ∘ F∘G≈id.⇒.η X ∘ F.F₁ (G∘F≈id.⇒.η (G.F₀ X)) ∘ F∘G≈id.⇐.η (F.F₀ (G.F₀ X))
              ∎
          }
        ; F⇐G = ntHelper record
          { η       = λ X → (F∘G≈id.⇒.η (F.F₀ (G.F₀ X)) ∘ F.F₁ (G∘F≈id.⇐.η (G.F₀ X))) ∘ F∘G≈id.⇐.η X
          ; commute = λ {X Y} f → begin
            ((F∘G≈id.⇒.η (F.F₀ (G.F₀ Y)) ∘ F.F₁ (G∘F≈id.⇐.η (G.F₀ Y))) ∘ F∘G≈id.⇐.η Y) ∘ f
              ≈⟨ pullʳ (F∘G≈id.⇐.commute f) ⟩
            (F∘G≈id.⇒.η (F.F₀ (G.F₀ Y)) ∘ F.F₁ (G∘F≈id.⇐.η (G.F₀ Y))) ∘ F.F₁ (G.F₁ f) ∘ F∘G≈id.⇐.η X
              ≈⟨ center (⟺ F.homomorphism) ⟩
            F∘G≈id.⇒.η (F.F₀ (G.F₀ Y)) ∘ F.F₁ (G∘F≈id.⇐.η (G.F₀ Y) C.∘ G.F₁ f) ∘ F∘G≈id.⇐.η X
              ≈⟨ refl⟩∘⟨ F.F-resp-≈ (G∘F≈id.⇐.commute (G.F₁ f)) ⟩∘⟨refl ⟩
            F∘G≈id.⇒.η (F.F₀ (G.F₀ Y)) ∘ F.F₁ (G.F₁ (F.F₁ (G.F₁ f)) C.∘ G∘F≈id.⇐.η (G.F₀ X)) ∘ F∘G≈id.⇐.η X
              ≈⟨ refl⟩∘⟨ F.homomorphism ⟩∘⟨refl ⟩
            F∘G≈id.⇒.η (F.F₀ (G.F₀ Y)) ∘ (F.F₁ (G.F₁ (F.F₁ (G.F₁ f))) ∘ F.F₁ (G∘F≈id.⇐.η (G.F₀ X))) ∘ F∘G≈id.⇐.η X
              ≈⟨ center⁻¹ (F∘G≈id.⇒.commute _) Equiv.refl ⟩
            (F.F₁ (G.F₁ f) ∘ F∘G≈id.⇒.η (F.F₀ (G.F₀ X))) ∘ F.F₁ (G∘F≈id.⇐.η (G.F₀ X)) ∘ F∘G≈id.⇐.η X
              ≈⟨ center Equiv.refl ⟩
            F.F₁ (G.F₁ f) ∘ (F∘G≈id.⇒.η (F.F₀ (G.F₀ X)) ∘ F.F₁ (G∘F≈id.⇐.η (G.F₀ X))) ∘ F∘G≈id.⇐.η X
              ∎
          }
        ; iso = λ X → Iso-∘ (Iso-∘ (Iso-swap (F∘G≈id.iso _)) ([ F ]-resp-Iso (G∘F≈id.iso _)))
                            (F∘G≈id.iso X)
        }
    ; zig    = λ {A} →
      let open D
          open HomReasoning
          open MR D
      in begin
      (F∘G≈id.⇒.η (F.F₀ A) ∘ F.F₁ (G∘F≈id.⇒.η (G.F₀ (F.F₀ A))) ∘ F∘G≈id.⇐.η (F.F₀ (G.F₀ (F.F₀ A))))
        ∘ F.F₁ (G∘F≈id.⇐.η A)
        ≈⟨ pull-last (F∘G≈id.⇐.commute (F.F₁ (G∘F≈id.⇐.η A))) ⟩
      F∘G≈id.⇒.η (F.F₀ A) ∘ F.F₁ (G∘F≈id.⇒.η (G.F₀ (F.F₀ A))) ∘
        F.F₁ (G.F₁ (F.F₁ (G∘F≈id.⇐.η A))) ∘ F∘G≈id.⇐.η (F.F₀ A)
        ≈˘⟨ refl⟩∘⟨ pushˡ F.homomorphism ⟩
      F∘G≈id.⇒.η (F.F₀ A) ∘ F.F₁ (G∘F≈id.⇒.η (G.F₀ (F.F₀ A)) C.∘ G.F₁ (F.F₁ (G∘F≈id.⇐.η A))) ∘ F∘G≈id.⇐.η (F.F₀ A)
        ≈⟨ refl⟩∘⟨ F.F-resp-≈ (G∘F≈id.⇒.commute (G∘F≈id.⇐.η A)) ⟩∘⟨refl ⟩
      F∘G≈id.⇒.η (F.F₀ A) ∘ F.F₁ (G∘F≈id.⇐.η A C.∘ G∘F≈id.⇒.η A) ∘ F∘G≈id.⇐.η (F.F₀ A)
        ≈⟨ refl⟩∘⟨ elimˡ ((F.F-resp-≈ (G∘F≈id.iso.isoˡ _)) ○ F.identity) ⟩
      F∘G≈id.⇒.η (F.F₀ A) ∘ F∘G≈id.⇐.η (F.F₀ A)
        ≈⟨ F∘G≈id.iso.isoʳ _ ⟩
      id
        ∎
    }

  module F⊣⊢G = _⊣⊢_ F⊣⊢G

module _ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′} (SE : StrongEquivalence C D) where
  open StrongEquivalence SE

  C≅D : ⊣Equivalence C D
  C≅D = record
    { L    = F
    ; R    = G
    ; L⊣⊢R = F⊣⊢G weak-inverse
    }

  module C≅D = ⊣Equivalence C≅D

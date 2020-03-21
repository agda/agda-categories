{-# OPTIONS --without-K --safe #-}

module Categories.Category.Equivalence where

-- Strong equivalence of categories.  Same as ordinary equivalence in Cat.
-- May not include everything we'd like to think of as equivalences, namely
-- the full, faithful functors that are essentially surjective on objects.

open import Level
open import Relation.Binary using (IsEquivalence; Setoid)

open import Categories.Adjoint.Equivalence using (_⊣⊢_; ⊣Equivalence; withZig)
open import Categories.Category
import Categories.Morphism.Reasoning as MR
import Categories.Morphism.Properties as MP
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Properties
open import Categories.NaturalTransformation using (ntHelper; _∘ᵥ_; _∘ˡ_; _∘ʳ_)
open import Categories.NaturalTransformation.NaturalIsomorphism as ≃
  using (NaturalIsomorphism ; unitorˡ; unitorʳ; associator; _ⓘᵥ_; _ⓘˡ_; _ⓘʳ_)
open import Categories.NaturalTransformation.NaturalIsomorphism.Properties

private
  variable
    o ℓ e : Level
    C D E : Category o ℓ e

record WeakInverse (F : Functor C D) (G : Functor D C) : Set (levelOfTerm F ⊔ levelOfTerm G) where
  field
    F∘G≈id : NaturalIsomorphism (F ∘F G) idF
    G∘F≈id : NaturalIsomorphism (G ∘F F) idF

  module F∘G≈id = NaturalIsomorphism F∘G≈id
  module G∘F≈id = NaturalIsomorphism G∘F≈id

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
              ≈⟨ refl ⟩∘⟨ F.F-resp-≈ (G∘F≈id.⇒.commute (G.F₁ f)) ⟩∘⟨ refl ⟩
            F∘G≈id.⇒.η Y ∘ F.F₁ (G.F₁ f C.∘ G∘F≈id.⇒.η (G.F₀ X)) ∘ F∘G≈id.⇐.η (F.F₀ (G.F₀ X))
              ≈⟨ refl ⟩∘⟨ F.homomorphism ⟩∘⟨ refl ⟩
            F∘G≈id.⇒.η Y ∘ (F.F₁ (G.F₁ f) ∘ F.F₁ (G∘F≈id.⇒.η (G.F₀ X))) ∘ F∘G≈id.⇐.η (F.F₀ (G.F₀ X))
              ≈⟨ center⁻¹ (F∘G≈id.⇒.commute f) refl ⟩
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
              ≈⟨ refl ⟩∘⟨ F.F-resp-≈ (G∘F≈id.⇐.commute (G.F₁ f)) ⟩∘⟨ refl ⟩
            F∘G≈id.⇒.η (F.F₀ (G.F₀ Y)) ∘ F.F₁ (G.F₁ (F.F₁ (G.F₁ f)) C.∘ G∘F≈id.⇐.η (G.F₀ X)) ∘ F∘G≈id.⇐.η X
              ≈⟨ refl ⟩∘⟨ F.homomorphism ⟩∘⟨ refl ⟩
            F∘G≈id.⇒.η (F.F₀ (G.F₀ Y)) ∘ (F.F₁ (G.F₁ (F.F₁ (G.F₁ f))) ∘ F.F₁ (G∘F≈id.⇐.η (G.F₀ X))) ∘ F∘G≈id.⇐.η X
              ≈⟨ center⁻¹ (F∘G≈id.⇒.commute _) refl ⟩
            (F.F₁ (G.F₁ f) ∘ F∘G≈id.⇒.η (F.F₀ (G.F₀ X))) ∘ F.F₁ (G∘F≈id.⇐.η (G.F₀ X)) ∘ F∘G≈id.⇐.η X
              ≈⟨ center refl ⟩
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
        ≈⟨ refl ⟩∘⟨ F.F-resp-≈ (G∘F≈id.⇒.commute (G∘F≈id.⇐.η A)) ⟩∘⟨ refl ⟩
      F∘G≈id.⇒.η (F.F₀ A) ∘ F.F₁ (G∘F≈id.⇐.η A C.∘ G∘F≈id.⇒.η A) ∘ F∘G≈id.⇐.η (F.F₀ A)
        ≈⟨ refl ⟩∘⟨ elimˡ ((F.F-resp-≈ (G∘F≈id.iso.isoˡ _)) ○ F.identity) ⟩
      F∘G≈id.⇒.η (F.F₀ A) ∘ F∘G≈id.⇐.η (F.F₀ A)
        ≈⟨ F∘G≈id.iso.isoʳ _ ⟩
      id
        ∎
    }

  module F⊣⊢G = _⊣⊢_ F⊣⊢G

record StrongEquivalence {o ℓ e o′ ℓ′ e′} (C : Category o ℓ e) (D : Category o′ ℓ′ e′) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  field
    F            : Functor C D
    G            : Functor D C
    weak-inverse : WeakInverse F G

  open WeakInverse weak-inverse public

  C≅D : ⊣Equivalence C D
  C≅D = record
    { L    = F
    ; R    = G
    ; L⊣⊢R = F⊣⊢G
    }

  module C≅D = ⊣Equivalence C≅D

refl : StrongEquivalence C C
refl = record
  { F            = idF
  ; G            = idF
  ; weak-inverse = record
    { F∘G≈id = unitorˡ
    ; G∘F≈id = unitorˡ
    }
  }

sym : StrongEquivalence C D → StrongEquivalence D C
sym e = record
  { F            = G
  ; G            = F
  ; weak-inverse = record
    { F∘G≈id     = G∘F≈id
    ; G∘F≈id     = F∘G≈id
    }
  }
  where open StrongEquivalence e

trans : StrongEquivalence C D → StrongEquivalence D E → StrongEquivalence C E
trans {C = C} {D = D} {E = E} e e′ = record
  { F            = e′.F ∘F e.F
  ; G            = e.G ∘F e′.G
  ; weak-inverse = record
    { F∘G≈id = let module S = Setoid (≃.Functor-NI-setoid E E)
               in S.trans (S.trans (associator (e.G ∘F e′.G) e.F e′.F)
                                   (e′.F ⓘˡ (unitorˡ ⓘᵥ (e.F∘G≈id ⓘʳ e′.G) ⓘᵥ ≃.sym (associator e′.G e.G e.F))))
                          e′.F∘G≈id
    ; G∘F≈id = let module S = Setoid (≃.Functor-NI-setoid C C)
               in S.trans (S.trans (associator (e′.F ∘F e.F) e′.G e.G)
                                   (e.G ⓘˡ (unitorˡ ⓘᵥ (e′.G∘F≈id ⓘʳ e.F) ⓘᵥ ≃.sym (associator e.F e′.F e′.G))))
                          e.G∘F≈id
    }
  }
  where module e  = StrongEquivalence e
        module e′ = StrongEquivalence e′

isEquivalence : ∀ {o ℓ e} → IsEquivalence (StrongEquivalence {o} {ℓ} {e})
isEquivalence = record
  { refl  = refl
  ; sym   = sym
  ; trans = trans
  }

setoid : ∀ o ℓ e → Setoid _ _
setoid o ℓ e = record
  { Carrier       = Category o ℓ e
  ; _≈_           = StrongEquivalence
  ; isEquivalence = isEquivalence
  }

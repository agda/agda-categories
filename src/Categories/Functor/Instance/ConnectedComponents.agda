{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Instance.ConnectedComponents where

open import Level
open import Function using () renaming (_∘′_ to _∙_)
open import Relation.Binary.Construct.Closure.SymmetricTransitive as ST using (Plus⇔; minimal)

open import Categories.Category
open import Categories.Category.Instance.Cats using (Cats)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor hiding (id)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)

-- this is the left adjoint to Disc : Setoids ⇒ Cats
Π₀ : ∀ {o ℓ e} → Functor (Cats o ℓ e) (Setoids o (o ⊔ ℓ))
Π₀ = record
  { F₀ = λ C → ST.setoid (Category._⇒_ C) (Category.id C)
  ; F₁ = λ F → record
    { _⟨$⟩_ = Functor.F₀ F
    ; cong = ST.gmap (Functor.F₀ F) (Functor.F₁ F)
    }
  ; identity = λ x → x
  ; homomorphism = λ {_ _ _ F G} → ST.gmap
      (Functor.F₀ G ∙ Functor.F₀ F)
      (Functor.F₁ G ∙ Functor.F₁ F)
  ; F-resp-≈ = my-resp _ _
  }
  where
  my-resp : ∀ {A B : Category _ _ _} (f g : Functor A B)
    (f≅g : NaturalIsomorphism f g) {x y} →
    Plus⇔ (Category._⇒_ A) x y →
    Plus⇔ (Category._⇒_ B) (Functor.F₀ f x) (Functor.F₀ g y)
  my-resp {A} {B} f g f≅g {x} {y} (Plus⇔.forth m)
    = Plus⇔.forth (B [ NaturalIsomorphism.⇒.η f≅g _ ∘ Functor.F₁ f m ])
  my-resp {A} {B} f g f≅g {x} {y} (Plus⇔.back m)
    = Plus⇔.back (B [ Functor.F₁ f m ∘ NaturalIsomorphism.⇐.η f≅g _ ])
  my-resp {A} {B} f g f≅g {x} {y} (Plus⇔.forth⁺ m ms)
    = Plus⇔.forth⁺
        (B [ NaturalIsomorphism.⇒.η f≅g _ ∘ Functor.F₁ f m ])
        (ST.gmap (Functor.F₀ g) (Functor.F₁ g) ms)
  my-resp {A} {B} f g f≅g {x} {y} (Plus⇔.back⁺ m ms)
    = Plus⇔.back⁺
        (B [ Functor.F₁ f m ∘ NaturalIsomorphism.⇐.η f≅g _ ])
        (ST.gmap (Functor.F₀ g) (Functor.F₁ g) ms)

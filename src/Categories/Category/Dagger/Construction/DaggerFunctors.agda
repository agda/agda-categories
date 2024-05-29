{-# OPTIONS --safe --without-K #-}

module Categories.Category.Dagger.Construction.DaggerFunctors where

open import Categories.Category.Dagger using (DaggerCategory)
import Categories.Category.Construction.DaggerFunctors as cat
open import Categories.Functor.Dagger using (DaggerFunctor)
open import Categories.NaturalTransformation using (NaturalTransformation)

open import Function.Base using (_$_)
open import Level using (Level; _⊔_)

private
  variable
    o ℓ e o′ ℓ′ e′ : Level

DaggerFunctors : (C : DaggerCategory o ℓ e) (D : DaggerCategory o′ ℓ′ e′)
               → DaggerCategory (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) (o ⊔ e′)
DaggerFunctors C D = record
  { C = cat.DaggerFunctors C D
  ; hasDagger = record
    { _† = λ {F} {G} α →
      let
         module F = DaggerFunctor F
         module G = DaggerFunctor G
         module α = NaturalTransformation α
      in record
      { η = λ X → α.η X †
      ; commute = λ {X Y} f → begin
        α.η Y † ∘ G.₁ f       ≈˘⟨ †-involutive _ ⟩
        (α.η Y † ∘ G.₁ f) † † ≈⟨ †-resp-≈ $ begin
          (α.η Y † ∘ G.₁ f) †   ≈⟨ †-homomorphism ⟩
          G.₁ f † ∘ α.η Y † †   ≈⟨ G.F-resp-† ⟩∘⟨ †-involutive _ ⟩
          G.₁ (f ‡) ∘ α.η Y     ≈⟨ α.sym-commute (f ‡) ⟩
          α.η X ∘ F.₁ (f ‡)     ≈˘⟨ †-involutive _ ⟩∘⟨ F.F-resp-† ⟩
          α.η X † † ∘ F.₁ f †   ≈˘⟨ †-homomorphism ⟩
          (F.₁ f ∘ α.η X †) †   ∎ ⟩
        (F.₁ f ∘ α.η X †) † † ≈⟨ †-involutive _ ⟩
        F.₁ f ∘ α.η X †       ∎
      ; sym-commute = λ {X Y} f → begin
        F.₁ f ∘ α.η X †       ≈˘⟨ †-involutive _ ⟩
        (F.₁ f ∘ α.η X †) † † ≈⟨ †-resp-≈ $ begin
          (F.₁ f ∘ α.η X †) †   ≈⟨ †-homomorphism ⟩
          α.η X † † ∘ F.₁ f †   ≈⟨ †-involutive _ ⟩∘⟨ F.F-resp-† ⟩
          α.η X ∘ F.₁ (f ‡)     ≈⟨ α.commute (f ‡) ⟩
          G.₁ (f ‡) ∘ α.η Y     ≈˘⟨ G.F-resp-† ⟩∘⟨ †-involutive _ ⟩
          G.₁ f † ∘ α.η Y † †   ≈˘⟨ †-homomorphism ⟩
          (α.η Y † ∘ G.₁ f) †   ∎ ⟩
        (α.η Y † ∘ G.₁ f) † † ≈⟨ †-involutive _ ⟩
        α.η Y † ∘ G.₁ f       ∎
      }
    ; †-identity = †-identity
    ; †-homomorphism = †-homomorphism
    ; †-resp-≈ = λ α≈β → †-resp-≈ α≈β
    ; †-involutive = λ α → †-involutive (NaturalTransformation.η α _)
    }
  }
  where
    open DaggerCategory C using () renaming (_† to _‡)
    open DaggerCategory D hiding (C)
    open HomReasoning

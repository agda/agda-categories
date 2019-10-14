{-# OPTIONS --without-K --safe #-}
module Categories.Category.Construction.Functors where

-- the "Functor Category", often denoted [ C , D ]

open import Level
open import Data.Product using (Σ; _,_; _×_; uncurry′; proj₁)

open import Categories.Category
open import Categories.Functor
open import Categories.Functor.Bifunctor
open import Categories.NaturalTransformation renaming (id to idN)
open import Categories.NaturalTransformation.Equivalence using (_≃_; ≃-isEquivalence)
import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e o′ ℓ′ e′ : Level
    C D : Category o ℓ e

-- The reason the proofs below are so easy is that _∘ᵥ_ 'computes' all the way down into
-- expressions in D, from which the properties follow.
Functors : Category o ℓ e → Category o′ ℓ′ e′ → Category (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) (o ⊔ e′)
Functors C D = record
  { Obj       = Functor C D
  ; _⇒_       = NaturalTransformation
  ; _≈_       = _≃_
  ; id        = idN
  ; _∘_       = _∘ᵥ_
  ; assoc     = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; equiv     = ≃-isEquivalence
  ; ∘-resp-≈  = λ eq eq′ → ∘-resp-≈ eq eq′
  }
  where module C = Category C
        module D = Category D
        open D

-- Part of the proof that Cats is a CCC:
eval : Bifunctor (Functors C D) C D
eval {C = C} {D = D} = record
  { F₀           = uncurry′ Functor.F₀
  ; F₁           = λ where
    {F , _} {_ , B} (α , f) →
      let open NaturalTransformation α
          open Functor F
      in η B ∘ F₁ f
  ; identity     = λ where
    {F , _} → elimʳ (Functor.identity F)
  ; homomorphism = λ where
    {F , _} {G , B} {_ , C} {α , f} {β , g} →
      let open NaturalTransformation
          open Functor
      in begin
        (η β C ∘ η α C) ∘ F₁ F (g C.∘ f)  ≈⟨ refl ⟩∘⟨ homomorphism F ⟩
        (η β C ∘ η α C) ∘ F₁ F g ∘ F₁ F f ≈⟨ assoc ⟩
        η β C ∘ η α C ∘ F₁ F g ∘ F₁ F f   ≈⟨ refl ⟩∘⟨ pullˡ (commute α g) ⟩
        η β C ∘ (F₁ G g ∘ η α B) ∘ F₁ F f ≈⟨ refl ⟩∘⟨ assoc ⟩
        η β C ∘ F₁ G g ∘ η α B ∘ F₁ F f   ≈˘⟨ assoc ⟩
        (η β C ∘ F₁ G g) ∘ η α B ∘ F₁ F f ∎
  ; F-resp-≈     = λ where
    {F , _} (comm , eq) → ∘-resp-≈ comm (Functor.F-resp-≈ F eq)
  }
  where module C = Category C
        module D = Category D
        open D
        open MR D
        open HomReasoning

-- Godement product ?
product : {A B C : Category o ℓ e} → Bifunctor (Functors B C) (Functors A B) (Functors A C)
product {A = A} {B = B} {C = C} = record
  { F₀ = uncurry′ _∘F_
  ; F₁ = uncurry′ _∘ₕ_
  ; identity = λ {f} → identityʳ ○ identity {D = C} (proj₁ f)
  ; homomorphism = λ { {_ , F₂} {G₁ , G₂} {H₁ , _} {f₁ , f₂} {g₁ , g₂} {x} → begin
      F₁ H₁ (η g₂ x B.∘ η f₂ x) ∘ η g₁ (F₀ F₂ x) ∘ η f₁ (F₀ F₂ x)
          ≈⟨ ∘-resp-≈ˡ (homomorphism H₁) ○ assoc ○ ∘-resp-≈ʳ (⟺ assoc) ⟩
      F₁ H₁ (η g₂ x) ∘ (F₁ H₁ (η f₂ x) ∘ η g₁ (F₀ F₂ x)) ∘ η f₁ (F₀ F₂ x)
          ≈⟨  ⟺ ( refl⟩∘⟨ ( commute g₁ (η f₂ x) ⟩∘⟨refl) ) ⟩
      F₁ H₁ (η g₂ x) ∘ (η g₁ (F₀ G₂ x) ∘ F₁  G₁ (η f₂ x)) ∘ η f₁ (F₀ F₂ x)
          ≈⟨ ∘-resp-≈ʳ assoc ○ ⟺ assoc ⟩
      (F₁ H₁ (η g₂ x) ∘ η g₁ (F₀ G₂ x)) ∘ F₁ G₁ (η f₂ x) ∘ η f₁ (F₀ F₂ x) ∎ }
  ; F-resp-≈ = λ { {_} {g₁ , _} (≈₁ , ≈₂) → ∘-resp-≈ (F-resp-≈ g₁ ≈₂) ≈₁ }
  }
  where
    open Category C
    open HomReasoning
    open Functor
    module B = Category B
    open NaturalTransformation

-- op induces a Functor on the Functors category.
-- This is an instance where the proof-irrelevant version is simpler because (op op C) is
-- just C. Here we rather need to be more explicit.
opF : {A : Category o ℓ e} {B : Category o′ ℓ′ e′} →
      Functor (Category.op (Functors (Category.op A) (Category.op B))) (Functors A B)
opF {A = A} {B} = record
  { F₀ = λ F → record
    { F₀ = F₀ F
    ; F₁ = F₁ F
    ; identity = identity F
    ; homomorphism = homomorphism F
    ; F-resp-≈ = F-resp-≈ F
    }
  ; F₁ = λ B⇒A → record
    { η = η B⇒A
    ; commute = λ f → Equiv.sym (commute B⇒A f)
    }
  ; identity = Equiv.refl
  ; homomorphism = Equiv.refl
  ; F-resp-≈ = λ eq → eq
  }
  where
  open Functor
  open NaturalTransformation
  open Category B

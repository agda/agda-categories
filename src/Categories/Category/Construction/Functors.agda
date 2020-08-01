{-# OPTIONS --without-K --safe #-}
module Categories.Category.Construction.Functors where

-- the "Functor Category", often denoted [ C , D ]

open import Level
open import Data.Product using (_,_; proj₁; uncurry′)

open import Categories.Adjoint.Equivalence using (⊣Equivalence)
open import Categories.Adjoint.TwoSided using (withZig)
open import Categories.Category using (Category; _[_∘_])
open import Categories.Category.Product using (_※ⁿ_) renaming (Product to _×_)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Bifunctor
open import Categories.Functor.Construction.Constant using (constNat)
open import Categories.NaturalTransformation
  using (NaturalTransformation; _∘ᵥ_; _∘ˡ_; _∘ₕ_) renaming (id to idN)
open import Categories.NaturalTransformation.Equivalence using (_≃_; ≃-isEquivalence)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (NaturalIsomorphism)
import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e o′ ℓ′ e′ : Level
    C D C₁ C₂ : Category o ℓ e

-- The reason the proofs below are so easy is that _∘ᵥ_ 'computes' all the way down into
-- expressions in D, from which the properties follow.
Functors : Category o ℓ e → Category o′ ℓ′ e′ → Category (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) (o ⊔ e′)
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
  ; identity² = identity²
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
        (η β C ∘ η α C) ∘ F₁ F (g C.∘ f)  ≈⟨ refl⟩∘⟨ homomorphism F ⟩
        (η β C ∘ η α C) ∘ F₁ F g ∘ F₁ F f ≈⟨ pullʳ (pullˡ (commute α g)) ⟩
        η β C ∘ (F₁ G g ∘ η α B) ∘ F₁ F f ≈⟨ pushʳ assoc ⟩
        (η β C ∘ F₁ G g) ∘ η α B ∘ F₁ F f ∎
  ; F-resp-≈     = λ where
    {F , _} (comm , eq) → ∘-resp-≈ comm (Functor.F-resp-≈ F eq)
  }
  where module C = Category C
        module D = Category D
        open D
        open MR D
        open HomReasoning

evalF : ∀ (C : Category o ℓ e) (D : Category o′ ℓ′ e′) → Category.Obj C → Functor (Functors C D) D
evalF _ _ X = appʳ eval X

-- Currying induces a functor between functor categories -- another
-- part of the proof that Cats is a cartesian closed (bi)category.

curry : Functor (Functors (C₁ × C₂) D) (Functors C₁ (Functors C₂ D))
curry {C₁ = C₁} {C₂ = C₂} {D = D} = record
  { F₀ = curry₀
  ; F₁ = curry₁
  ; identity     = Equiv.refl D
  ; homomorphism = Equiv.refl D
  ; F-resp-≈     = λ F≈G {x₁} {x₂} → F≈G {x₁ , x₂}
  }
  where
    open Category

    curry₀ : Bifunctor C₁ C₂ D → Functor C₁ (Functors C₂ D)
    curry₀ F = record
      { F₀ = λ c → appˡ F c
      ; F₁ = λ f → F ∘ˡ (constNat f ※ⁿ idN)
      ; identity     = identity
      ; homomorphism = λ {_} {_} {_} {f} {g} → begin
          F₁ (C₁ [ g ∘ f ] , id C₂)                ≈˘⟨ F-resp-≈ (Equiv.refl C₁ , identityˡ C₂) ⟩
          F₁ (C₁ [ g ∘ f ] , C₂ [ id C₂ ∘ id C₂ ]) ≈⟨ homomorphism ⟩
          D [ F₁ (g , id C₂) ∘ F₁ (f , id C₂) ]    ∎
      ; F-resp-≈ = λ f≈g → F-resp-≈ (f≈g , Equiv.refl C₂)
      }
      where
        open Functor F
        open HomReasoning D

    curry₁ : {F G : Bifunctor C₁ C₂ D} →
             NaturalTransformation F G →
             NaturalTransformation (curry₀ F) (curry₀ G)
    curry₁ α = record
      { η = λ c → record
        { η           = λ a → η α (c , a)
        ; commute     = λ f →     commute α (id C₁  , f)
        ; sym-commute = λ f → sym-commute α (id C₁  , f)
        }
      ; commute       = λ f →     commute α (f , id C₂)
      ; sym-commute   = λ f → sym-commute α (f , id C₂)
      }
      where open NaturalTransformation

module curry {o₁ e₁ ℓ₁} {C₁ : Category o₁ e₁ ℓ₁}
             {o₂ e₂ ℓ₂} {C₂ : Category o₂ e₂ ℓ₂}
             {o′ e′ ℓ′} {D  : Category o′ e′ ℓ′}
             where
  open Functor (curry {C₁ = C₁} {C₂ = C₂} {D = D}) public
  open Category
  open NaturalIsomorphism

  -- Currying preserves natural isos.
  -- This makes |curry.F₀| a map between the hom-setoids of Cats.

  resp-NI : {F G : Bifunctor C₁ C₂ D} →
            NaturalIsomorphism F G → NaturalIsomorphism (F₀ F) (F₀ G)
  resp-NI α = record
    { F⇒G = F₁ (F⇒G α)
    ; F⇐G = F₁ (F⇐G α)
    ; iso = λ x → record
      { isoˡ = iso.isoˡ α (x , _)
      ; isoʳ = iso.isoʳ α (x , _)
      }
    }

-- Godement product ?
product : {A B C : Category o ℓ e} → Bifunctor (Functors B C) (Functors A B) (Functors A C)
product {A = A} {B = B} {C = C} = record
  { F₀ = uncurry′ _∘F_
  ; F₁ = uncurry′ _∘ₕ_
  ; identity = λ {f} → identityʳ ○ identity {D = C} (proj₁ f)
  ; homomorphism = λ { {_ , F₂} {G₁ , G₂} {H₁ , _} {f₁ , f₂} {g₁ , g₂} {x} → begin
      F₁ H₁ (η g₂ x B.∘ η f₂ x) ∘ η g₁ (F₀ F₂ x) ∘ η f₁ (F₀ F₂ x)
        ≈⟨ ∘-resp-≈ˡ (homomorphism H₁) ⟩
      ((F₁ H₁ (η g₂ x) ∘ F₁ H₁ (η f₂ x)) ∘ η g₁ (F₀ F₂ x) ∘ η f₁ (F₀ F₂ x))
        ≈⟨ center (⟺ (commute g₁ (η f₂ x))) ⟩
      F₁ H₁ (η g₂ x) ∘ (η g₁ (F₀ G₂ x) ∘ F₁  G₁ (η f₂ x)) ∘ η f₁ (F₀ F₂ x)
        ≈⟨ pull-first refl ⟩
      (F₁ H₁ (η g₂ x) ∘ η g₁ (F₀ G₂ x)) ∘ F₁ G₁ (η f₂ x) ∘ η f₁ (F₀ F₂ x)
        ∎ }
  ; F-resp-≈ = λ { {_} {g₁ , _} (≈₁ , ≈₂) → ∘-resp-≈ (F-resp-≈ g₁ ≈₂) ≈₁ }
  }
  where
    open Category C
    open MR C
    open HomReasoning
    open Equiv
    open Functor
    module B = Category B
    open NaturalTransformation

-- op induces a Functor on the Functors category.
-- This is an instance where the proof-irrelevant version is simpler because (op op C) is
-- just C. Here we rather need to be more explicit.
opF⇒ : {A : Category o ℓ e} {B : Category o′ ℓ′ e′} →
      Functor (Category.op (Functors (Category.op A) (Category.op B))) (Functors A B)
opF⇒ {A = A} {B} = record
  { F₀           = Functor.op
  ; F₁           = NaturalTransformation.op
  ; identity     = Equiv.refl
  ; homomorphism = Equiv.refl
  ; F-resp-≈     = λ eq → eq
  }
  where open Category B

opF⇐ : {A : Category o ℓ e} {B : Category o′ ℓ′ e′} →
      Functor (Functors A B) (Category.op (Functors (Category.op A) (Category.op B)))
opF⇐ {A = A} {B} = record
  { F₀           = Functor.op
  ; F₁           = NaturalTransformation.op
  ; identity     = Equiv.refl
  ; homomorphism = Equiv.refl
  ; F-resp-≈     = λ eq → eq
  }
  where open Category B

Functorsᵒᵖ-equiv : (A : Category o ℓ e) (B : Category o′ ℓ′ e′) →
                   ⊣Equivalence (Category.op (Functors (Category.op A) (Category.op B))) (Functors A B)
Functorsᵒᵖ-equiv A B = record
  { L    = opF⇒
  ; R    = opF⇐
  ; L⊣⊢R = withZig record
    { unit   = record
      { F⇒G = record
        { η           = λ _ → idN
        ; commute     = λ _ → id-comm-sym
        ; sym-commute = λ _ → id-comm
        }
      ; F⇐G = record
        { η           = λ _ → idN
        ; commute     = λ _ → id-comm-sym
        ; sym-commute = λ _ → id-comm
        }
      ; iso = λ _ → record
        { isoˡ = identity²
        ; isoʳ = identity²
        }
      }
    ; counit = record
      { F⇒G = record
        { η           = λ _ → idN
        ; commute     = λ _ → id-comm-sym
        ; sym-commute = λ _ → id-comm
        }
      ; F⇐G = record
        { η           = λ _ → idN
        ; commute     = λ _ → id-comm-sym
        ; sym-commute = λ _ → id-comm
        }
      ; iso = λ _ → record
        { isoˡ = identity²
        ; isoʳ = identity²
        }
      }
    ; zig    = identity²
    }
  }
  where open Category B
        open HomReasoning
        open MR B

module Functorsᵒᵖ-equiv {o ℓ e o′ ℓ′ e′} (A : Category o ℓ e) (B : Category o′ ℓ′ e′) = ⊣Equivalence (Functorsᵒᵖ-equiv A B)

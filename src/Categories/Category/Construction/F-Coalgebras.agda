{-# OPTIONS --without-K --safe #-}
module Categories.Category.Construction.F-Coalgebras where

open import Level

open import Categories.Category
open import Categories.Functor hiding (id)
open import Categories.Functor.Algebra
open import Categories.Functor.Coalgebra
open import Categories.Object.Initial
open import Categories.Object.Terminal
import Categories.Morphism.Reasoning as MR
import Categories.Morphism as Mor using (_≅_; Iso)
open import Categories.Category.Construction.F-Algebras
open import Categories.Functor.Duality

private
  variable
    o ℓ e : Level
    C : Category o ℓ e

F-Coalgebras : {C : Category o ℓ e} → Endofunctor C → Category (ℓ ⊔ o) (e ⊔ ℓ) e
F-Coalgebras {C = C} F = record
  { Obj       = F-Coalgebra F
  ; _⇒_       = F-Coalgebra-Morphism
  ; _≈_       = λ α₁ α₂ → f α₁ ≈ f α₂
  ; _∘_       = λ α₁ α₂ → coF-Algebra-Morphism⇒F-Coalgebra-Morphism
    (F-Coalgebra-Morphism⇒coF-Algebra-Morphism α₁
    coF-Algebras.∘
    F-Coalgebra-Morphism⇒coF-Algebra-Morphism α₂)
  ; id        = coF-Algebra-Morphism⇒F-Coalgebra-Morphism coF-Algebras.id
  ; assoc     = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv     = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }
  ; ∘-resp-≈  = ∘-resp-≈
  }
  where
    open Category C
    open MR C
    open HomReasoning
    open Equiv
    open F-Coalgebra-Morphism
    module coF-Algebras = Category (Category.op (F-Algebras (Functor.op F)))

F-Coalgebras⇒coF-Algebras : {C : Category o ℓ e} → (F : Endofunctor C) → Functor (F-Coalgebras F) (Category.op (F-Algebras (Functor.op F)))
F-Coalgebras⇒coF-Algebras {C = C} F = record
  { F₀           = F-Coalgebra⇒coF-Algebra
  ; F₁           = F-Coalgebra-Morphism⇒coF-Algebra-Morphism
  ; identity     = refl
  ; homomorphism = refl
  ; F-resp-≈     = λ {_ _ α₁ α₂} α₁≈α₂ →
     begin
      F-Algebra-Morphism.f (F-Coalgebra-Morphism⇒coF-Algebra-Morphism α₁) ≈⟨ refl ⟩
      f α₁ ≈⟨ α₁≈α₂ ⟩
      f α₂ ≈⟨ refl ⟩
      F-Algebra-Morphism.f (F-Coalgebra-Morphism⇒coF-Algebra-Morphism α₂) ∎
  }
  where
    open Category C
    open MR C
    open HomReasoning
    open Equiv
    open F-Coalgebra-Morphism

private
  coIsTerminal⇒Initial : ∀ {C : Category o ℓ e} {F : Endofunctor C}
    {T : Category.Obj (F-Coalgebras F) } →
    IsTerminal (F-Coalgebras F) T →
    IsInitial (F-Algebras (Functor.op F)) (F-Coalgebra⇒coF-Algebra T)
  coIsTerminal⇒Initial {C = C} {F = F} {T = T} isTT = record
    { ! =
        F-Coalgebra-Morphism⇒coF-Algebra-Morphism ¡
    ; !-unique =
        λ  γ  → Functor.F-resp-≈ (F-Coalgebras⇒coF-Algebras F)
        {f = ¡}
        {g = coF-Algebra-Morphism⇒F-Coalgebra-Morphism γ}
        (¡-unique (coF-Algebra-Morphism⇒F-Coalgebra-Morphism γ))
    }
    where
      open Category (F-Algebras (Functor.op F))
      open MR (F-Algebras (Functor.op F))
      open IsTerminal isTT renaming (! to ¡; !-unique to ¡-unique)
      open HomReasoning
      open Equiv

private module CoLambek {C : Category o ℓ e} {F : Endofunctor C} (T : Terminal (F-Coalgebras F)) where
  open Category C
  open Functor F using (F₀)
  open F-Coalgebra using (α)

  open Mor C
  open Terminal T

  private
    module F⊤ = F-Coalgebra ⊤
    A = F⊤.A
    a : A ⇒ F₀ A
    a = F⊤.α

    coInitial : Initial (F-Algebras (Functor.op F))
    coInitial = record
                { ⊥ = F-Coalgebra⇒coF-Algebra ⊤
                ; ⊥-is-initial = coIsTerminal⇒Initial ⊤-is-terminal
                }

    module coLambek = Lambek coInitial

  colambek : A ≅ F₀ A
  colambek = record
    { from = to coLambek.lambek
    ; to = from coLambek.lambek
    ; iso = record
      { isoˡ = isoˡ (iso coLambek.lambek)
      ; isoʳ = isoʳ (iso coLambek.lambek)
      }
    }
    where
      open HomReasoning
      open Mor._≅_
      open Mor.Iso

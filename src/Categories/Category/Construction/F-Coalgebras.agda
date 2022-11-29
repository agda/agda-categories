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
open import Categories.Object.Duality
open import Function.Equality

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


FCo-M⇒coF-M-cong :
  ∀ {C : Category o ℓ e} {F : Endofunctor C} {X Y : F-Coalgebra F} {α₁ α₂ : F-Coalgebra-Morphism X Y}
  → F-Coalgebras F [ α₁ ≈ α₂ ] →
  F-Algebras (Functor.op F) [ F-Coalgebra-Morphism⇒coF-Algebra-Morphism α₁
  ≈ F-Coalgebra-Morphism⇒coF-Algebra-Morphism α₂ ]
FCo-M⇒coF-M-cong {C = C} {F = F} {α₁ = α₁} {α₂ = α₂} α₁≈α₂ = let
  foo : f α₁ ≈ f α₂
  foo = α₁≈α₂
  goal : F-Algebra-Morphism.f (F-Coalgebra-Morphism⇒coF-Algebra-Morphism α₁) ≈ F-Algebra-Morphism.f (F-Coalgebra-Morphism⇒coF-Algebra-Morphism α₂)
  goal = begin
    F-Algebra-Morphism.f (F-Coalgebra-Morphism⇒coF-Algebra-Morphism α₁) ≈⟨ refl ⟩
    f α₁ ≈⟨ foo ⟩
    f α₂ ≈⟨ refl ⟩
    F-Algebra-Morphism.f (F-Coalgebra-Morphism⇒coF-Algebra-Morphism α₂) ∎
  in goal
  where
    open Category C
    open MR C
    open HomReasoning
    open Equiv
    open F-Coalgebra-Morphism



F-Co-M⇒coF-M : {C : Category o ℓ e} → (F : Endofunctor C) → Functor (F-Coalgebras F) (Category.op (F-Algebras (Functor.op F)))
F-Co-M⇒coF-M {C = C} F = record
  { F₀           = F-Coalgebra⇒coF-Algebra
  ; F₁           = F-Coalgebra-Morphism⇒coF-Algebra-Morphism
  ; identity     = refl
  ; homomorphism = refl
  ; F-resp-≈     = λ {_ _ α₁ α₂} α₁≈α₂ →
    let foo : f α₁ ≈ f α₂
        foo = α₁≈α₂
        goal : F-Algebra-Morphism.f (F-Coalgebra-Morphism⇒coF-Algebra-Morphism α₁) ≈ F-Algebra-Morphism.f (F-Coalgebra-Morphism⇒coF-Algebra-Morphism α₂)
        goal = begin
          F-Algebra-Morphism.f (F-Coalgebra-Morphism⇒coF-Algebra-Morphism α₁) ≈⟨ refl ⟩
          f α₁ ≈⟨ foo ⟩
          f α₂ ≈⟨ refl ⟩
          F-Algebra-Morphism.f (F-Coalgebra-Morphism⇒coF-Algebra-Morphism α₂) ∎
        in  goal
  }
  where
    open Category C
    open MR C
    open HomReasoning
    open Equiv
    open F-Coalgebra-Morphism


termToInit : ∀ {C : Category o ℓ e} {F : Endofunctor C} {T : Category.Obj (F-Coalgebras F)} →
  IsTerminal (F-Coalgebras F) T →
    IsInitial (F-Algebras (Functor.op F)) (F-Coalgebra⇒coF-Algebra T)
termToInit {C = C} {F = F} {T = T} isTT = record
  { ! =
      F-Coalgebra-Morphism⇒coF-Algebra-Morphism ¡
  ; !-unique =
      λ γ →
        let
          known : F-Coalgebras F [ ¡ ≈ coF-Algebra-Morphism⇒F-Coalgebra-Morphism γ ]
          known = ¡-unique (coF-Algebra-Morphism⇒F-Coalgebra-Morphism γ)
          bar :
            F-Algebras (Functor.op F)
              [ F-Coalgebra-Morphism⇒coF-Algebra-Morphism ¡
                ≈ F-Coalgebra-Morphism⇒coF-Algebra-Morphism (coF-Algebra-Morphism⇒F-Coalgebra-Morphism γ) ]
          bar = Functor.F-resp-≈ (F-Co-M⇒coF-M F) known
          result : F-Algebras (Functor.op F)
            [ F-Coalgebra-Morphism⇒coF-Algebra-Morphism ¡ ≈ γ ]
          result = begin
            F-Coalgebra-Morphism⇒coF-Algebra-Morphism ¡ ≈⟨ bar ⟩
            F-Coalgebra-Morphism⇒coF-Algebra-Morphism (coF-Algebra-Morphism⇒F-Coalgebra-Morphism γ)
            ≈⟨ refl ⟩
            γ ∎

        in result
  }
  where
    open Category (F-Algebras (Functor.op F))
    open MR (F-Algebras (Functor.op F))
    open IsTerminal isTT renaming (! to ¡; !-unique to ¡-unique)
    open HomReasoning
    open Equiv


private module CoLambek {C : Category o ℓ e} {F : Endofunctor C} (T : Terminal (F-Coalgebras F)) where
  open Category C hiding (_≈_)
  open Functor F
  open F-Coalgebra using (α)

  open Mor C
  open Terminal T -- so ⊤ is an F-Coalgebra, which is initial

  private
    module F⊤ = F-Coalgebra ⊤
    A = F⊤.A
    a : A ⇒ F₀ A
    a = F⊤.α

    initial : Initial (F-Algebras (Functor.op F))
    initial = record
                { ⊥ = F-Coalgebra⇒coF-Algebra ⊤
                ; ⊥-is-initial = termToInit ⊤-is-terminal
                }

    module bar = Lambek initial

  colambek : A ≅ F₀ A
  colambek = record
    { from = to bar.lambek
    ; to = from bar.lambek
    ; iso = record
      { isoˡ = isoˡ (iso bar.lambek)
      ; isoʳ = isoʳ (iso bar.lambek)
      }
    }
    where
      open HomReasoning
      open Mor._≅_
      open Mor.Iso

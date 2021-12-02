{-# OPTIONS --without-K --safe #-}

open import Level
open import Categories.Category.Core using (Category)
open import Categories.Category
open import Categories.Monad

module Categories.Adjoint.Construction.AdjunctionTerminalInitial {o ℓ e} {C : Category (o ⊔ ℓ ⊔ e) (ℓ ⊔ e) e} (M : Monad C) where

open import Categories.Adjoint
open import Categories.Functor
open import Categories.NaturalTransformation.Core as NT
open import Categories.NaturalTransformation.NaturalIsomorphism as NI
open import Categories.Morphism.Reasoning as MR

open import Categories.Adjoint.Construction.Adjunctions M

open import Categories.Object.Terminal (Split M)
open import Categories.Object.Initial (Split M)
open import Categories.Category.Construction.EilenbergMoore
open import Categories.Category.Construction.Kleisli
open import Categories.Adjoint.Construction.Kleisli M as KL
open import Categories.Adjoint.Construction.EilenbergMoore M as EM

EM-object : SplitObj
EM-object = record
  { D = EilenbergMoore M
  ; F = EM.Free
  ; G = EM.Forgetful
  ; adj = EM.Free⊣Forgetful
  ; eqM = EM.FF≃F
  }

EM-terminal : IsTerminal EM-object
EM-terminal = record
  { ! = {!!}
  ; !-unique = {!   !}
  }


Kl-object : SplitObj
Kl-object = record
  { D = Kleisli M
  ; F = KL.Free
  ; G = KL.Forgetful
  ; adj = KL.Free⊣Forgetful
  ; eqM = KL.FF≃F
  }

Kl-initial : IsInitial Kl-object
Kl-initial = record
  { ! = bang
  ; !-unique = {!   !}
  }
  where
    -- vanno aperte un po' di cose per non diventar matti
    bang : {A : SplitObj} → Split⇒ Kl-object A
    bang {splitobj D F G adj eq} = record
      { H = record
            { F₀ = λ T → Functor.F₀ F T
            ; F₁ = λ {A} {B} f → adj.counit.η (F.₀ B) ∘ F.₁ (eq.⇐.η B C.∘ f)
            ; identity = λ {A} → begin
              adj.counit.η (F.₀ A) ∘ F.₁ (eq.⇐.η A C.∘ M.η.η A) ≈⟨ refl⟩∘⟨ Functor.F-resp-≈ F lemma ⟩
              adj.counit.η (F.₀ A) ∘ F.₁ (adj.unit.η A)         ≈⟨ adj.zig ⟩
              D.id                                              ∎
            ; homomorphism = λ {X} {Y} {Z} {f} {g} → {!   !}
            ; F-resp-≈ = λ x → D.∘-resp-≈ʳ (Functor.F-resp-≈ F (C.∘-resp-≈ʳ x))
            }
      ; HF≃F' = {!   !}
      ; G'H≃G = {!   !}
      }
      where module adj    = Adjoint adj
            module F      = Functor F
            module M      = Monad M
            module eq     = NaturalIsomorphism eq
            open module D = Category D
            open D.HomReasoning
            module C = Category C

            lemma : ∀ {A} → eq.⇐.η A C.∘ M.η.η A C.≈ adj.unit.η A
            lemma {A} = C.HomReasoning.begin
                eq.⇐.η A C.∘ M.η.η A C.HomReasoning.≈⟨ {!   !} ⟩
                adj.unit.η A         C.HomReasoning.∎
              where open C.HomReasoning
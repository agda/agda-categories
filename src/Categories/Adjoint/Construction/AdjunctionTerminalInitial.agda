{-# OPTIONS --without-K --safe #-}

open import Level
open import Categories.Category.Core using (Category)
open import Categories.Category
open import Categories.Monad

module Categories.Adjoint.Construction.AdjunctionTerminalInitial {o ℓ e} {C : Category (o ⊔ ℓ ⊔ e) (ℓ ⊔ e) e} (M : Monad C) where

open Category C

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

open Category (Split M)
open SplitObj
open Split⇒

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
  { ! = {!   !}
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
  bang {Splitc D F G adj eq} = record
    { H = record
          { F₀ = λ T → Functor.F₀ F T
          ; F₁ = λ {A} {B} f → Adjoint.counit.η adj (Functor.F₀ F B) D.∘ (Functor.F₁ F (⇐.η B) D.∘ Functor.F₁ F f)
          ; identity = λ {A} → begin
            NaturalTransformation.η (Adjoint.counit adj) (Functor.F₀ F A) D.∘ Functor.F₁ F (⇐.η A) D.∘ Functor.F₁ F (M.η.η A) ≈⟨ (refl⟩∘⟨ D.Equiv.sym (Functor.homomorphism F)) ⟩
            NaturalTransformation.η (Adjoint.counit adj) (Functor.F₀ F A) D.∘ Functor.F₁ F (⇐.η A C.∘ M.η.η A) ≈⟨ (refl⟩∘⟨ Functor.F-resp-≈ F lemma) ⟩
            NaturalTransformation.η (Adjoint.counit adj) (Functor.F₀ F A) D.∘ Functor.F₁ F (NaturalTransformation.η (Adjoint.unit adj) A) ≈⟨ Adjoint.zig adj ⟩
            D.id ∎
          ; homomorphism = λ {X} {Y} {Z} {f} {g} → {!   !}
          ; F-resp-≈ = λ {A} {B} {f} {g} x → D.∘-resp-≈ʳ (D.∘-resp-≈ʳ (Functor.F-resp-≈ F x))
          }
    ; HF≃F' = {!   !}
    ; G'H≃G = {!   !}
    }
    where module D = Category D
          module C = Category C
          open C
          open D
          open D.HomReasoning
          module M = Monad M
          module eq = NaturalIsomorphism eq
          open eq
          lemma : {A : C.Obj} → ⇐.η A C.∘ M.η.η A C.≈ NaturalTransformation.η (Adjoint.unit adj) A
          lemma {A} = C.HomReasoning.begin
            ⇐.η A C.∘ M.η.η A C.HomReasoning.≈⟨ {!   !} ⟩
            NaturalTransformation.η (Adjoint.unit adj) A
            C.HomReasoning.∎
            where open C.HomReasoning

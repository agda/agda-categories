{-# OPTIONS --without-K --safe #-}

open import Level
open import Categories.Category
open import Categories.Category.Monoidal

module Categories.Enriched.Functor {o ℓ e : Level} {V : Category o ℓ e} (M : Monoidal V) where

open import Function renaming (id to id→; _∘_ to _●_) using ()
open import Relation.Binary hiding (_⇒_)

open import Categories.Enriched.Category renaming (Category to Enriched) hiding (_[_,_])
import Categories.Functor as Func
import Categories.Morphism as R
import Categories.Morphism.Reasoning as MR

private
  variable
    v v′ v″ : Level

record Functor (C : Enriched M v) (D : Enriched M v′) : Set (o ⊔ ℓ ⊔ e ⊔ v ⊔ v′) where
  eta-equality
  private
    module C = Enriched C
    module D = Enriched D
  open Category V hiding (id)
  open Monoidal M using (_⊗₁_)

  field
    F₀ : C.Obj → D.Obj
    F₁ : (A B : C.Obj) → V [ C.hom A B , D.hom (F₀ A) (F₀ B) ]

    identity     : {A : C.Obj} → V [ (F₁ A A ∘ C.id) ≈ D.id {F₀ A} ]
    homomorphism : {X Y Z : C.Obj} → V [ (F₁ X Z ∘ C.⊚) ≈ (D.⊚ ∘ F₁ Y Z ⊗₁ F₁ X Y) ]
    -- We don't need F-resp-≈ as "C.hom A B" is an object of V, which has no 'equality'

{-
  op : Functor C.op D.op
  op = record
    { F₀           = F₀
    ; F₁           = F₁
    ; identity     = identity
    ; homomorphism = homomorphism
    ; F-resp-≈     = F-resp-≈
    }
-}

Endofunctor : Enriched M v → Set _
Endofunctor C = Functor C C

id : ∀ {C : Enriched M v} → Endofunctor C
id {C = C} = record
  { F₀ = id→
  ; F₁ = λ A B → idV {C.hom A B}
  ; identity = identityˡ
  ; homomorphism = λ {X Y Z} → begin
    idV ∘ C.⊚        ≈⟨ MR.id-comm-sym V ⟩
    C.⊚ ∘ idV        ≈˘⟨ refl⟩∘⟨ identity ⟩
    C.⊚ ∘ idV ⊗₁ idV ∎
  }
  where
  open Category V renaming (id to idV)
  module C = Enriched C
  open HomReasoning
  open Monoidal M using (_⊗₁_; ⊗)
  open Func.Functor ⊗

infixr 9 _∘F_

-- note that this definition could be shortened a lot by inlining the definitions for
-- identity′ and homomorphism′, but the definitions below are simpler to understand.
_∘F_ : {C : Enriched M v} {D : Enriched M v′} {E : Enriched M v″}
    → Functor D E → Functor C D → Functor C E
_∘F_ {C = C} {D = D} {E = E} F G = record
  { F₀ = F₀ ● G₀
  ; F₁ = λ A B → F₁ (G₀ A) (G₀ B) ∘ G₁ A B
  ; identity = identity′
  ; homomorphism = homomorphism′
  }
  where
  open Category V using (_∘_; assoc; sym-assoc; module HomReasoning)
  open HomReasoning
  module C = Enriched C
  module D = Enriched D
  module E = Enriched E
  module F = Functor F
  module G = Functor G
  open F
  open G renaming (F₀ to G₀; F₁ to G₁)
  open Monoidal M
  open Enriched using (Obj; ⊚) renaming (id to idE)

  identity′ : {A : Obj C} → V [ ((F₁ (G₀ A) (G₀ A) ∘ G₁ A A) ∘ idE C) ≈ idE E {F₀ (G₀ A)} ]
  identity′ {A} = begin
    (F₁ (G₀ A) (G₀ A) ∘ G₁ A A) ∘ idE C  ≈⟨ assoc ⟩
    F₁ (G₀ A) (G₀ A) ∘ (G₁ A A ∘ idE C)  ≈⟨ refl⟩∘⟨ (identity G) ⟩
    F₁ (G₀ A) (G₀ A) ∘ (idE D)           ≈⟨ identity F ⟩
    idE E                                ∎

  homomorphism′ : {X Y Z : C.Obj} →
      V [ (F₁ (G₀ X) (G₀ Z) ∘ G₁ X Z) ∘ C.⊚ ≈
      E.⊚ ∘ (F₁ (G₀ Y) (G₀ Z) ∘ G₁ Y Z) ⊗₁ (F₁ (G₀ X) (G₀ Y) ∘ G₁ X Y) ]
  homomorphism′ {X} {Y} {Z} = begin
    (F₁ (G₀ X) (G₀ Z) ∘ G₁ X Z) ∘ C.⊚                                 ≈⟨ assoc ⟩
    F₁ (G₀ X) (G₀ Z) ∘ (G₁ X Z ∘ C.⊚)                                 ≈⟨ refl⟩∘⟨ homomorphism G ⟩
    F₁ (G₀ X) (G₀ Z) ∘ D.⊚ ∘ G₁ Y Z ⊗₁ G₁ X Y                         ≈⟨ sym-assoc ⟩
    (F₁ (G₀ X) (G₀ Z) ∘ D.⊚) ∘ G₁ Y Z ⊗₁ G₁ X Y                       ≈⟨ homomorphism F ⟩∘⟨refl ⟩
    (E.⊚ ∘ F₁ (G₀ Y) (G₀ Z) ⊗₁ F₁ (G₀ X) (G₀ Y)) ∘ G₁ Y Z ⊗₁ G₁ X Y   ≈⟨ assoc ⟩
    E.⊚ ∘ (F₁ (G₀ Y) (G₀ Z) ⊗₁ F₁ (G₀ X) (G₀ Y) ∘ G₁ Y Z ⊗₁ G₁ X Y)   ≈˘⟨ refl⟩∘⟨ Func.Functor.homomorphism ⊗ ⟩
    E.⊚ ∘ (F₁ (G₀ Y) (G₀ Z) ∘ G₁ Y Z) ⊗₁ (F₁ (G₀ X) (G₀ Y) ∘ G₁ X Y)  ∎

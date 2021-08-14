{-# OPTIONS --without-K --safe #-}

--  Restriction Functor
module Categories.Functor.Restriction where

open import Level using (Level; _⊔_)

open import Categories.Category using (Category; _[_,_]; _[_≈_])
open import Categories.Category.Restriction using (Restriction)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)

private
  variable
    o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ : Level
    C : Category o ℓ e
    D : Category o′ ℓ′ e′
    E : Category o″ ℓ″ e″

record RestrictionF {C : Category o ℓ e} {D : Category o′ ℓ′ e′}
  (RC : Restriction C) (RD : Restriction D) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  private
    module C = Category C using (Obj)
    module RC = Restriction RC
    module RD = Restriction RD
  field
    Func : Functor C D
  open Functor Func using (F₁)
  field
    F-resp-↓ : {A B : C.Obj} → (f : C [ A , B ]) → D [ F₁ (f RC.↓) ≈ (F₁ f) RD.↓ ]

id : {RC : Restriction C} → RestrictionF RC RC
id {C = C} = record { Func = idF ; F-resp-↓ = λ f → Category.Equiv.refl C }

_∘R_ : {RC : Restriction C} {RD : Restriction D} {RE : Restriction E} → RestrictionF RD RE → RestrictionF RC RD → RestrictionF RC RE
_∘R_ {C = C} {E = E} {RC} {RD} {RE} F G = record
  { Func = Func F ∘F Func G
  ; F-resp-↓ = resp
  }
  where
    open RestrictionF
    open Category E using (_≈_; module HomReasoning)
    open HomReasoning
    module F = Functor (Func F)
    module G = Functor (Func G)
    module RC = Restriction RC
    module RD = Restriction RD
    module RE = Restriction RE
    resp : ∀ {A B : Category.Obj C} → (f : C [ A , B ]) → F.₁ (G.₁ (f RC.↓)) ≈ F.₁ (G.₁ f) RE.↓
    resp f = begin
       F.₁ (G.₁ (f RC.↓)) ≈⟨ F.F-resp-≈ (F-resp-↓ G f) ⟩
       F.₁ ((G.₁ f) RD.↓) ≈⟨ F-resp-↓ F _ ⟩
       F.₁ (G.₁ f) RE.↓ ∎

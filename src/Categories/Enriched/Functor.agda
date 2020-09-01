{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (module Commutation) renaming (Category to Setoid-Category)
open import Categories.Category.Monoidal using (Monoidal)

module Categories.Enriched.Functor {o ℓ e} {V : Setoid-Category o ℓ e}
                                   (M : Monoidal V) where

open import Level

open import Categories.Enriched.Category M
open import Categories.Enriched.Category.Underlying M
open import Categories.Functor using () renaming (Functor to Setoid-Functor)
open import Categories.Morphism.Reasoning V
open import Categories.Category.Monoidal.Reasoning M using (⊗-distrib-over-∘)

open Setoid-Category V renaming (Obj to ObjV; id to idV)
open Commutation V
open HomReasoning
open Monoidal M

record Functor {c d} (C : Category c) (D : Category d) : Set (ℓ ⊔ e ⊔ c ⊔ d) where
  eta-equality
  private
    module C = Category C
    module D = Category D

  field
    map₀ : C.Obj → D.Obj
    map₁ : ∀ {X Y} → C [ X , Y ] ⇒ D [ map₀ X , map₀ Y ]

    identity     : ∀ {X} → map₁ ∘ C.id ≈ D.id {map₀ X}
    homomorphism : ∀ {X Y Z} →
      [ C [ Y , Z ] ⊗₀ C [ X , Y ] ⇒ D [ map₀ X , map₀ Z ] ]⟨
        C.⊚           ⇒⟨ C [ X , Z ]                ⟩  map₁
      ≈ map₁ ⊗₁ map₁  ⇒⟨ D [ _ , _ ] ⊗₀ D [ _ , _ ] ⟩  D.⊚
      ⟩

    -- We don't need an analogue of F-resp-≈ because |hom A B| is not
    -- a hom-Setoid but a hom-object (in V) and the functorial action
    -- is not a Setoid-map but a V-morphism.  Whether V-objects have a
    -- notion of equality, and whether such equalities are preserved
    -- by V-morphisms, depends entirely on V.

  -- Shorthands for the functorial actions that work well as
  -- post-projections.

  ₀ = map₀
  ₁ = map₁

Endofunctor : ∀ {c} → Category c → Set (ℓ ⊔ e ⊔ c)
Endofunctor C = Functor C C

id : ∀ {c} {C : Category c} → Endofunctor C
id {_} {C} = record
  { map₀         = λ X → X
  ; map₁         = idV
  ; identity     = identityˡ
  ; homomorphism = id-comm-sym ○ ∘-resp-≈ʳ (⟺ ⊗.identity)
  }
  where
  open Category C

infixr 9 _∘F_

_∘F_ : ∀ {c d e} {C : Category c} {D : Category d} {E : Category e} →
       Functor D E → Functor C D → Functor C E
_∘F_ {_} {_} {_} {C} {D} {E} G F = record
  { map₀     = λ X → G.₀ (F.₀ X)
  ; map₁     = G.₁ ∘ F.₁
  ; identity = begin
      (G.₁ ∘ F.₁) ∘ C.id   ≈⟨ pullʳ F.identity ⟩
      G.₁ ∘ D.id           ≈⟨ G.identity ⟩
      E.id                 ∎
  ; homomorphism = begin
      (G.₁ ∘ F.₁) ∘ C.⊚                  ≈⟨ pullʳ F.homomorphism ⟩
      G.₁ ∘ (D.⊚ ∘ F.₁ ⊗₁ F.₁)           ≈⟨ pullˡ G.homomorphism ⟩
      (E.⊚ ∘ G.₁ ⊗₁ G.₁) ∘ F.₁ ⊗₁ F.₁    ≈˘⟨ pushʳ ⊗-distrib-over-∘ ⟩
      E.⊚ ∘ (G.₁ ∘ F.₁) ⊗₁ (G.₁ ∘ F.₁)   ∎
  }
  where
    module C = Category C
    module D = Category D
    module E = Category E
    module F = Functor F
    module G = Functor G

-- A V-enriched functor induces an ordinary functor on the underlying
-- categories.

module _ {c d} {C : Category c} {D : Category d} where

  UnderlyingFunctor : Functor C D → Setoid-Functor (Underlying C) (Underlying D)
  UnderlyingFunctor F = record
    { F₀           = F.₀
    ; F₁           = F.₁ ∘_
    ; identity     = F.identity
    ; homomorphism = λ {_} {_} {_} {f} {g} → begin
        F.₁ ∘ C.⊚ ∘ g ⊗₁ f ∘ λ⇐             ≈⟨ pullˡ F.homomorphism ⟩
        (D.⊚ ∘ F.₁ ⊗₁ F.₁) ∘ g ⊗₁ f ∘ λ⇐    ≈˘⟨ pushʳ (pushˡ ⊗-distrib-over-∘) ⟩
        D.⊚ ∘ (F.₁ ∘ g) ⊗₁ (F.₁ ∘ f) ∘ λ⇐   ∎
    ; F-resp-≈     = ∘-resp-≈ʳ
    }
    where
      module C = Category C
      module D = Category D
      module F = Functor F

      λ⇐ = unitorˡ.to

  module UnderlyingFunctor F = Setoid-Functor (UnderlyingFunctor F)

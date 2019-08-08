{-# OPTIONS --without-K --safe #-}

module Categories.Strict.Functor where

-- Strict Functor, over Strict Category. Has its own, external _≡F_
-- relation. It is a sort-of Heterogeneous equality, but without ever
-- assuming Axiom K.

open import Level
open import Function renaming (id to id→; _∘_ to _●_) using ()
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality
open import Data.Product using (Σ; proj₁; proj₂) renaming (_,_ to _,,_)

open import Categories.Utils.EqReasoning

import Relation.Binary.Reasoning.Setoid as SetoidR

open import Categories.Strict.Category

private
  variable
    o ℓ o′ ℓ′ o″ ℓ″ : Level
    A B C D : Category o ℓ

record Functor (C : Category o ℓ) (D : Category o′ ℓ′) : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
  eta-equality
  private module C = Category C
  private module D = Category D

  field
    F₀ : C.Obj → D.Obj
    F₁ : ∀ {A B} → C [ A , B ] → D [ F₀ A , F₀ B ]

    identity     : ∀ {A} → F₁ (C.id {A}) ≡ D.id
    homomorphism : ∀ {X Y Z} {f : C [ X , Y ]} {g : C [ Y , Z ]} →
                     F₁ (C [ g ∘ f ]) ≡ D [ F₁ g ∘ F₁ f ]

  op : Functor C.op D.op
  op = record
    { F₀           = F₀
    ; F₁           = F₁
    ; identity     = identity
    ; homomorphism = homomorphism
    }

Endofunctor : Category o ℓ → Set _
Endofunctor C = Functor C C

id : Endofunctor C
id = record
  { F₀           = id→
  ; F₁           = id→
  ; identity     = refl
  ; homomorphism = refl
  }

infixr 9 _∘F_
-- note that this definition could be shortened a lot by inlining the definitions for
-- identity′ and homomorphism′, but the definitions below are simpler to understand.
_∘F_ : ∀ {C : Category o ℓ} {D : Category o′ ℓ′} {E : Category o″ ℓ″}
    → Functor D E → Functor C D → Functor C E
_∘F_ {C = C} {D = D} {E = E} F G = record
  { F₀ = F₀ ● G₀
  ; F₁ = F₁ ● G₁
  ; identity = identity′
  ; homomorphism = homomorphism′
  }
  where
  module C = Category C
  module D = Category D
  module E = Category E
  module F = Functor F
  module G = Functor G
  open F
  open G renaming (F₀ to G₀; F₁ to G₁)

  identity′ : ∀ {A} → F₁ (G₁ (C.id {A})) ≡ E.id
  identity′ = begin
    F₁ (G₁ C.id) ≈⟨ cong F₁ G.identity  ⟩
    F₁ D.id      ≈⟨ F.identity ⟩
    E.id         ∎
    where open E.HomReasoning

  homomorphism′ : ∀ {X Y Z} {f : C [ X , Y ]} {g : C [ Y , Z ]}
                 → F₁ (G₁ (C [ g ∘ f ])) ≡ E [ F₁ (G₁ g) ∘ F₁ (G₁ f) ]
  homomorphism′ {f = f} {g = g} = begin
    F₁ (G₁ (C [ g ∘ f ]))       ≈⟨ cong F₁ G.homomorphism  ⟩
    F₁ (D [ G₁ g ∘ G₁ f ])      ≈⟨ F.homomorphism ⟩
    E [ F₁ (G₁ g) ∘ F₁ (G₁ f) ] ∎
    where open E.HomReasoning

-- "extensional" equality of Functors. A Heterogeneous equality, specialized for this case.
infix  4 _≡F_

-- Note how the first equality is 'backwards', but that is what is needed for the substitution!
_≡F_ : ∀ {o ℓ} {o′ ℓ′} {C : Category o ℓ} {D : Category o′ ℓ′} → (F G : Functor C D) → Set (ℓ′ ⊔ ℓ ⊔ o ⊔ o′)
_≡F_ {C = C} {D} F G = ∀ {A B} → (f : C [ A , B ]) →
  Σ ({X : Category.Obj C} → Functor.F₀ G X ≡ Functor.F₀ F X) (λ eq → Functor.F₁ F f ≡ subst₂ _⇒_ (eq {A}) (eq {B}) (Functor.F₁ G f))
  where open Category D

-- (subst₂ _⇒_ cong ((F₀ i) (eq₂ {X})) (cong (F₀ i) (eq₂ {X})) (F₁ i Fg) ≡ F₁ i (subst₂ B._⇒_ eq₂ eq₂ Fg)
≡F-equiv : ∀ {o ℓ} {o′ ℓ′} {C : Category o ℓ} {D : Category o′ ℓ′} → IsEquivalence (_≡F_ {o} {ℓ} {o′} {ℓ′} {C} {D})
≡F-equiv {C = C} {D} = record
  { refl = λ f → refl ,, refl
  ; sym = λ {i} {j} x f → sym (proj₁ (x f)) ,,
    let eq = proj₁ (x f) in begin
    F₁ j f                                                   ≡˘⟨ subst₂-sym-subst₂ _⇒_ eq eq ⟩
    subst₂ _⇒_ (sym eq) (sym eq) (subst₂ _⇒_ eq eq (F₁ j f)) ≡˘⟨ cong (subst₂ _⇒_ _ _) (proj₂ (x f)) ⟩
    subst₂ _⇒_ (sym eq) (sym eq) (F₁ i f)                    ∎

  ; trans = λ {i} {j} {k} i≡j j≡k f → trans (proj₁ (j≡k f)) (proj₁ (i≡j f)) ,,
    let eq₁ {X} = proj₁ (i≡j f) {X} in
    let eq₂ {X} = proj₁ (j≡k f) {X} in
    let eq₃ {X} = trans eq₂ (eq₁ {X}) in
    begin
    F₁ i f                                           ≡⟨ proj₂ (i≡j f) ⟩
    subst₂ _⇒_ eq₁ eq₁ (F₁ j f)                      ≡⟨ cong (subst₂ _⇒_ _ _) (proj₂ (j≡k f)) ⟩
    subst₂ _⇒_ eq₁ eq₁ (subst₂ _⇒_ eq₂ eq₂ (F₁ k f)) ≡⟨ subst₂-subst₂ _⇒_ eq₂ eq₁ eq₂ eq₁ ⟩
    subst₂ _⇒_ eq₃ eq₃ (F₁ k f) ∎
  }
  where
  open Category D
  open Functor
  open HomReasoning

-- Since the above isn't just ≡, it is convenient to also prove here that ≡F is preserved by ∘F
-- Note that this proof below is "the same" as horizontal composition of NaturalIsomorphism _ⓘₕ_
∘F-perserves-≡F : {A : Category o ℓ} {B : Category o′ ℓ′} {C : Category o″ ℓ″} {h i : Functor B C} {f g : Functor A B} →
      h ≡F i → f ≡F g → h ∘F f ≡F i ∘F g
∘F-perserves-≡F {A = A} {B} {C} {h} {i} {f} {g} h≡i f≡g {a₁} {a₂} a₁⇒a₂ = obj-≡ ,, hom-≡
  where
  open Functor
  open Category C
  open HomReasoning
  module B = Category B
  obj-≡ : {X : Category.Obj A} → F₀ i (F₀ g X) ≡ F₀ h (F₀ f X)
  obj-≡ {X} = trans (cong (F₀ i) (proj₁ (f≡g a₁⇒a₂))) (proj₁ (h≡i (F₁ f a₁⇒a₂)))
  hom-≡ : F₁ h (F₁ f a₁⇒a₂) ≡ subst₂ _⇒_ obj-≡ obj-≡ (F₁ i (F₁ g a₁⇒a₂))
  hom-≡ =
    let Ff = F₁ f a₁⇒a₂ in
    let Fg = F₁ g a₁⇒a₂ in
    let eq₁ {X} = proj₁ (h≡i (F₁ f a₁⇒a₂)) {X} in
    let eq₂ {X} = proj₁ (f≡g a₁⇒a₂) {X} in
    let eq₃ {X} = cong (F₀ i) (eq₂ {X}) in
    let s = subst₂ _⇒_ eq₁ eq₁ in
    begin
    F₁ h Ff                            ≡⟨ proj₂ (h≡i (F₁ f a₁⇒a₂)) ⟩
    s (F₁ i Ff)                        ≡⟨ cong s (cong (F₁ i) (proj₂ (f≡g a₁⇒a₂))) ⟩
    s (F₁ i (subst₂ B._⇒_ eq₂ eq₂ Fg)) ≡⟨ cong s (sym (subst₂-app _⇒_ Fg (λ _ _ x → F₁ i x) eq₂ eq₂) ) ⟩
    s (subst₂ _⇒_ eq₃ eq₃ (F₁ i Fg))   ≡⟨ subst₂-subst₂ _⇒_ eq₃ eq₁ eq₃ eq₁ ⟩
    subst₂ _⇒_ obj-≡ obj-≡ (F₁ i Fg) ∎

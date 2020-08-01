{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.FinCatShapes where

open import Data.Fin.Base using (Fin)

open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality as ≡ using (refl; _≡_; module ≡-Reasoning)

open import Categories.Category.Core using (Category)
open import Categories.Category.Helper
open import Categories.Category.Finite.Fin

open import Categories.Utils.EqReasoning

-- essentially a functor, but we don't need the congruence rule
record FinCatShape⇒ (X Y : FinCatShape) : Set where
  private
    module X = FinCatShape X
    module Y = FinCatShape Y

  field
    F₀ : Fin X.size → Fin Y.size
    F₁ : ∀ {x y} → x X.⇒ y → F₀ x Y.⇒ F₀ y

    identity : ∀ {x} → F₁ (X.id {x}) ≡ Y.id
    homomorphism : ∀ {x y z} {f : x X.⇒ y} {g : y X.⇒ z} →
                     F₁ (g X.∘ f) ≡ F₁ g Y.∘ F₁ f

record _≈_ {X Y} (f g : FinCatShape⇒ X Y) : Set where
  private
    module X = FinCatShape X
    module Y = FinCatShape Y
    module f = FinCatShape⇒ f
    module g = FinCatShape⇒ g

  field
    F₀≡ : ∀ x → f.F₀ x ≡ g.F₀ x
    F₁≡ : ∀ {x y} (w : x X.⇒ y) → ≡.subst₂ Y._⇒_ (F₀≡ x) (F₀≡ y) (f.F₁ w) ≡ g.F₁ w

private
  open ≡-Reasoning

  id : ∀ {A} → FinCatShape⇒ A A
  id {A} = record
    { F₀           = λ x → x
    ; F₁           = λ x → x
    ; identity     = refl
    ; homomorphism = refl
    }
    where open FinCatShape A

  comp : ∀ {A B C} → FinCatShape⇒ B C → FinCatShape⇒ A B → FinCatShape⇒ A C
  comp {A} {B} {C} f g = record
    { F₀           = λ a → f.F₀ (g.F₀ a)
    ; F₁           = λ w → f.F₁ (g.F₁ w)
    ; identity     = λ {a} → begin
      f.F₁ (g.F₁ A.id)                ≡⟨ ≡.cong f.F₁ g.identity  ⟩
      f.F₁ B.id                       ≡⟨ f.identity ⟩
      C.id                            ∎
    ; homomorphism = λ {a b c} {z w} → begin
      f.F₁ (g.F₁ (w A.∘ z))           ≡⟨ ≡.cong f.F₁ g.homomorphism ⟩
      f.F₁ (g.F₁ w B.∘ g.F₁ z)        ≡⟨ f.homomorphism ⟩
      f.F₁ (g.F₁ w) C.∘ f.F₁ (g.F₁ z) ∎
    }
    where module A = FinCatShape A using (id; _∘_)
          module B = FinCatShape B using (id; _∘_)
          module C = FinCatShape C using (id; _∘_)
          module f = FinCatShape⇒ f
          module g = FinCatShape⇒ g

  assoc : ∀ {A B C D} {f : FinCatShape⇒ A B} {g : FinCatShape⇒ B C} {h : FinCatShape⇒ C D} →
            comp (comp h g) f ≈ comp h (comp g f)
  assoc {A} {B} {C} {D} {f} {g} {h} = record
    { F₀≡ = λ a → refl
    ; F₁≡ = λ w → refl
    }
    where module A = FinCatShape A
          module B = FinCatShape B
          module C = FinCatShape C
          module D = FinCatShape D
          module f = FinCatShape⇒ f
          module g = FinCatShape⇒ g
          module h = FinCatShape⇒ h

  identityˡ : ∀ {A B} {f : FinCatShape⇒ A B} → comp id f ≈ f
  identityˡ {A} {B} {f} = record
    { F₀≡ = λ x → refl
    ; F₁≡ = λ w → refl
    }

  identityʳ : ∀ {A B} {f : FinCatShape⇒ A B} → comp f id ≈ f
  identityʳ {A} {B} {f} = record
    { F₀≡ = λ x → refl
    ; F₁≡ = λ w → refl
    }

  equiv : ∀ {A B} → IsEquivalence (_≈_ {A} {B})
  equiv {A} {B} = record
    { refl  = record
      { F₀≡ = λ x → refl
      ; F₁≡ = λ w → refl
      }
    ; sym   = λ {x y} eq →
      let module x = FinCatShape⇒ x
          module y = FinCatShape⇒ y
          open _≈_ eq
      in record
      { F₀≡ = λ z → ≡.sym (F₀≡ z)
      ; F₁≡ = λ {a b} w → begin
        ≡.subst₂ B._⇒_ (≡.sym (F₀≡ a)) (≡.sym (F₀≡ b)) (y.F₁ w)
          ≡˘⟨ ≡.cong (≡.subst₂ B._⇒_ (≡.sym (F₀≡ a)) (≡.sym (F₀≡ b))) (F₁≡ w) ⟩
        ≡.subst₂ B._⇒_ (≡.sym (F₀≡ a)) (≡.sym (F₀≡ b)) (≡.subst₂ B._⇒_ (F₀≡ a) (F₀≡ b) (x.F₁ w))
          ≡⟨ subst₂-sym-subst₂ B._⇒_ (F₀≡ a) (F₀≡ b) ⟩
        x.F₁ w
          ∎
      }
    ; trans = λ {x y z} eq eq′ →
      let module x   = FinCatShape⇒ x
          module y   = FinCatShape⇒ y
          module z   = FinCatShape⇒ z
          module eq  = _≈_ eq
          module eq′ = _≈_ eq′
      in record
      { F₀≡ = λ a → ≡.trans (eq.F₀≡ a) (eq′.F₀≡ a)
      ; F₁≡ = λ {a b} w → begin
        ≡.subst₂ B._⇒_ (≡.trans (eq.F₀≡ a) (eq′.F₀≡ a)) (≡.trans (eq.F₀≡ b) (eq′.F₀≡ b)) (x.F₁ w)
          ≡˘⟨ subst₂-subst₂ B._⇒_ (eq.F₀≡ a) (eq′.F₀≡ a) (eq.F₀≡ b) (eq′.F₀≡ b) ⟩
        ≡.subst₂ B._⇒_ (eq′.F₀≡ a) (eq′.F₀≡ b) (≡.subst₂ B._⇒_ (eq.F₀≡ a) (eq.F₀≡ b) (x.F₁ w))
          ≡⟨ ≡.cong (≡.subst₂ B._⇒_ (eq′.F₀≡ a) (eq′.F₀≡ b)) (eq.F₁≡ w) ⟩
        ≡.subst₂ B._⇒_ (eq′.F₀≡ a) (eq′.F₀≡ b) (y.F₁ w)
          ≡⟨ eq′.F₁≡ w ⟩
        z.F₁ w
          ∎
      }
    }
    where module A = FinCatShape A
          module B = FinCatShape B

  ∘-resp-≈ : ∀ {A B C} {f h : FinCatShape⇒ B C} {g i : FinCatShape⇒ A B} →
               f ≈ h → g ≈ i → comp f g ≈ comp h i
  ∘-resp-≈ {A} {B} {C} {f} {h} {g} {i} eq eq′ = record
    { F₀≡ = λ a → ≡.trans (≡.cong f.F₀ (eq′.F₀≡ a)) (eq.F₀≡ (i.F₀ a))
    ; F₁≡ = λ {x y} w → begin
      ≡.subst₂ C._⇒_
        (≡.trans (≡.cong f.F₀ (eq′.F₀≡ x)) (eq.F₀≡ (i.F₀ x)))
        (≡.trans (≡.cong f.F₀ (eq′.F₀≡ y)) (eq.F₀≡ (i.F₀ y)))
        (F₁ (comp f g) w)
        ≡˘⟨ subst₂-subst₂ C._⇒_ (≡.cong f.F₀ (eq′.F₀≡ x)) (eq.F₀≡ (i.F₀ x)) (≡.cong f.F₀ (eq′.F₀≡ y)) (eq.F₀≡ (i.F₀ y)) ⟩
      ≡.subst₂ C._⇒_ (eq.F₀≡ (i.F₀ x)) (eq.F₀≡ (i.F₀ y))
               (≡.subst₂ C._⇒_ (≡.cong f.F₀ (eq′.F₀≡ x)) (≡.cong f.F₀ (eq′.F₀≡ y))
                         (F₁ (comp f g) w))
        ≡⟨ ≡.cong (≡.subst₂ C._⇒_ (eq.F₀≡ (i.F₀ x)) (eq.F₀≡ (i.F₀ y))) (subst₂-app C._⇒_ (g.F₁ w) (λ _ _ → f.F₁) (eq′.F₀≡ x) (eq′.F₀≡ y)) ⟩
      ≡.subst₂ C._⇒_ (eq.F₀≡ (i.F₀ x)) (eq.F₀≡ (i.F₀ y))
               (f.F₁ (≡.subst₂ B._⇒_ (eq′.F₀≡ x) (eq′.F₀≡ y) (g.F₁ w)))
        ≡⟨ ≡.cong (λ j → ≡.subst₂ C._⇒_ (eq.F₀≡ (i.F₀ x)) (eq.F₀≡ (i.F₀ y)) (f.F₁ j)) (eq′.F₁≡ w) ⟩
      ≡.subst₂ C._⇒_ (eq.F₀≡ (i.F₀ x)) (eq.F₀≡ (i.F₀ y)) (f.F₁ (i.F₁ w))
        ≡⟨ eq.F₁≡ (i.F₁ w) ⟩
      h.F₁ (i.F₁ w)
        ∎
    }
    where module A   = FinCatShape A
          module B   = FinCatShape B
          module C   = FinCatShape C
          module f   = FinCatShape⇒ f
          module g   = FinCatShape⇒ g
          module h   = FinCatShape⇒ h
          module i   = FinCatShape⇒ i
          module eq  = _≈_ eq
          module eq′ = _≈_ eq′
          open FinCatShape⇒

FinCatShapes : Category _ _ _
FinCatShapes = categoryHelper record
  { Obj       = FinCatShape
  ; _⇒_       = FinCatShape⇒
  ; _≈_       = _≈_
  ; id        = id
  ; _∘_       = comp
  ; assoc     = λ {A B C D} {f g} {h} → assoc {f = f} {g} {h}
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; equiv     = equiv
  ; ∘-resp-≈  = ∘-resp-≈
  }

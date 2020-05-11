{-# OPTIONS --without-K --safe #-}

module Categories.Category.Finite.Fin.Instance.Span where

open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Patterns
open import Relation.Binary.PropositionalEquality.Core using (_≡_ ; refl)

open import Categories.Category.Finite.Fin
open import Categories.Category
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.NaturalTransformation using (ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_)
open import Categories.Adjoint.Equivalence using (⊣Equivalence)
open import Categories.Adjoint.TwoSided using (_⊣⊢_; withZig)
import Categories.Morphism as Mor
import Categories.Category.Instance.Span as Sp

private
  variable
    a b c d : Fin 3

-- The diagram is the following:
--
-- 1 <------- 0 -------> 2
--
SpanShape : FinCatShape
SpanShape = shapeHelper record
  { size      = 3
  ; ∣_⇒_∣     = morph
  ; id        = id
  ; _∘_       = _∘_
  ; assoc     = assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  }
  where morph : Fin 3 → Fin 3 → ℕ
        morph 0F 0F = 1
        morph 0F 1F = 1
        morph 0F 2F = 1
        morph 1F 1F = 1
        morph 2F 2F = 1
        morph _ _   = 0

        id : Fin (morph a a)
        id {0F} = 0F
        id {1F} = 0F
        id {2F} = 0F

        _∘_ : ∀ {a b c} → Fin (morph b c) → Fin (morph a b) → Fin (morph a c)
        _∘_ {0F} {0F} {0F} 0F 0F = 0F
        _∘_ {0F} {0F} {1F} 0F 0F = 0F
        _∘_ {0F} {0F} {2F} 0F 0F = 0F
        _∘_ {0F} {1F} {1F} 0F 0F = 0F
        _∘_ {0F} {2F} {2F} 0F 0F = 0F
        _∘_ {1F} {1F} {1F} 0F 0F = 0F
        _∘_ {2F} {2F} {2F} 0F 0F = 0F

        assoc : ∀ {f : Fin (morph a b)} {g : Fin (morph b c)} {h : Fin (morph c d)} →
                  ((h ∘ g) ∘ f) ≡ (h ∘ (g ∘ f))
        assoc {0F} {0F} {0F} {0F} {0F} {0F} {0F} = refl
        assoc {0F} {0F} {0F} {1F} {0F} {0F} {0F} = refl
        assoc {0F} {0F} {0F} {2F} {0F} {0F} {0F} = refl
        assoc {0F} {0F} {1F} {1F} {0F} {0F} {0F} = refl
        assoc {0F} {0F} {2F} {2F} {0F} {0F} {0F} = refl
        assoc {0F} {1F} {1F} {1F} {0F} {0F} {0F} = refl
        assoc {0F} {2F} {2F} {2F} {0F} {0F} {0F} = refl
        assoc {1F} {1F} {1F} {1F} {0F} {0F} {0F} = refl
        assoc {2F} {2F} {2F} {2F} {0F} {0F} {0F} = refl

        identityˡ : ∀ {f : Fin (morph a b)} → (id ∘ f) ≡ f
        identityˡ {0F} {0F} {0F} = refl
        identityˡ {0F} {1F} {0F} = refl
        identityˡ {0F} {2F} {0F} = refl
        identityˡ {1F} {1F} {0F} = refl
        identityˡ {2F} {2F} {0F} = refl

        identityʳ : ∀ {f : Fin (morph a b)} → (f ∘ id) ≡ f
        identityʳ {0F} {0F} {0F} = refl
        identityʳ {0F} {1F} {0F} = refl
        identityʳ {0F} {2F} {0F} = refl
        identityʳ {1F} {1F} {0F} = refl
        identityʳ {2F} {2F} {0F} = refl

Span : Category _ _ _
Span = FinCategory SpanShape

module Span = Category Span

open FinCatShape SpanShape

SpanToF : Functor Span Sp.Span
SpanToF = record
  { F₀           = F₀
  ; F₁           = F₁
  ; identity     = identity
  ; homomorphism = homomorphism
  ; F-resp-≈     = F-resp-≈
  }
  where F₀ : Fin 3 → Sp.SpanObj
        F₀ 0F = Sp.center
        F₀ 1F = Sp.left
        F₀ 2F = Sp.right

        F₁ : Fin ∣ a ⇒ b ∣ → Sp.SpanArr (F₀ a) (F₀ b)
        F₁ {0F} {0F} 0F = Sp.span-id
        F₁ {0F} {1F} 0F = Sp.span-arrˡ
        F₁ {0F} {2F} 0F = Sp.span-arrʳ
        F₁ {1F} {1F} 0F = Sp.span-id
        F₁ {2F} {2F} 0F = Sp.span-id

        identity : F₁ (id {a}) ≡ Sp.span-id
        identity {0F} = refl
        identity {1F} = refl
        identity {2F} = refl

        homomorphism : ∀ {f : Fin ∣ a ⇒ b ∣} {g : Fin ∣ b ⇒ c ∣} →
                         F₁ (g ∘ f) ≡ Sp.span-compose (F₁ g) (F₁ f)
        homomorphism {0F} {0F} {0F} {0F} {0F} = refl
        homomorphism {0F} {0F} {1F} {0F} {0F} = refl
        homomorphism {0F} {0F} {2F} {0F} {0F} = refl
        homomorphism {0F} {1F} {1F} {0F} {0F} = refl
        homomorphism {0F} {2F} {2F} {0F} {0F} = refl
        homomorphism {1F} {1F} {1F} {0F} {0F} = refl
        homomorphism {2F} {2F} {2F} {0F} {0F} = refl

        F-resp-≈ : ∀ {f g : Fin ∣ a ⇒ b ∣} → f ≡ g → F₁ f ≡ F₁ g
        F-resp-≈ {0F} {0F} {0F} {0F} _ = refl
        F-resp-≈ {0F} {1F} {0F} {0F} _ = refl
        F-resp-≈ {0F} {2F} {0F} {0F} _ = refl
        F-resp-≈ {1F} {1F} {0F} {0F} _ = refl
        F-resp-≈ {2F} {2F} {0F} {0F} _ = refl

module SpanToF = Functor SpanToF

SpanFromF : Functor Sp.Span Span
SpanFromF = record
  { F₀           = F₀
  ; F₁           = F₁
  ; identity     = identity
  ; homomorphism = homomorphism
  ; F-resp-≈     = F-resp-≈
  }
  where F₀ : Sp.SpanObj → Fin 3
        F₀ Sp.center = 0F
        F₀ Sp.left   = 1F
        F₀ Sp.right  = 2F

        F₁ : ∀ {A B} → Sp.Span [ A , B ] → Span [ F₀ A , F₀ B ]
        F₁ {Sp.center} Sp.span-id = 0F
        F₁ {Sp.left} Sp.span-id   = 0F
        F₁ {Sp.right} Sp.span-id  = 0F
        F₁ Sp.span-arrˡ           = 0F
        F₁ Sp.span-arrʳ           = 0F

        identity : ∀ {A} → F₁ (Category.id Sp.Span {A}) ≡ id
        identity {Sp.center} = refl
        identity {Sp.left}   = refl
        identity {Sp.right}  = refl

        homomorphism : ∀ {X Y Z} {f : Sp.Span [ X , Y ]} {g : Sp.Span [ Y , Z ]} →
                       F₁ (Sp.Span [ g ∘ f ]) ≡ F₁ g ∘ F₁ f
        homomorphism {Sp.center} {_} {_} {Sp.span-id} {Sp.span-id} = refl
        homomorphism {Sp.left} {_} {_} {Sp.span-id} {Sp.span-id}   = refl
        homomorphism {Sp.right} {_} {_} {Sp.span-id} {Sp.span-id}  = refl
        homomorphism {_} {_} {_} {Sp.span-id} {Sp.span-arrˡ}       = refl
        homomorphism {_} {_} {_} {Sp.span-id} {Sp.span-arrʳ}       = refl
        homomorphism {_} {_} {_} {Sp.span-arrˡ} {Sp.span-id}       = refl
        homomorphism {_} {_} {_} {Sp.span-arrʳ} {Sp.span-id}       = refl

        F-resp-≈ : ∀ {A B} {f g : Sp.Span [ A , B ]} → f ≡ g → F₁ f ≡ F₁ g
        F-resp-≈ {Sp.center} {_} {Sp.span-id} {Sp.span-id} _              = refl
        F-resp-≈ {Sp.left} {_} {Sp.span-id} {Sp.span-id} _                = refl
        F-resp-≈ {Sp.right} {_} {Sp.span-id} {Sp.span-id} _               = refl
        F-resp-≈ {.Sp.center} {.Sp.left} {Sp.span-arrˡ} {Sp.span-arrˡ} _  = refl
        F-resp-≈ {.Sp.center} {.Sp.right} {Sp.span-arrʳ} {Sp.span-arrʳ} _ = refl

module SpanFromF = Functor SpanFromF

SpansEquivF : SpanToF ⊣⊢ SpanFromF
SpansEquivF = withZig record
  { unit   = unit
  ; counit = counit
  ; zig    = zig
  }
  where unit⇒η : ∀ a → Fin ∣ a ⇒ SpanFromF.₀ (SpanToF.₀ a) ∣
        unit⇒η 0F = 0F
        unit⇒η 1F = 0F
        unit⇒η 2F = 0F
        unit⇐η : ∀ a → Fin ∣ SpanFromF.₀ (SpanToF.₀ a) ⇒ a ∣
        unit⇐η 0F = 0F
        unit⇐η 1F = 0F
        unit⇐η 2F = 0F

        unit : idF ≃ SpanFromF ∘F SpanToF
        unit = record
          { F⇒G = ntHelper record
            { η       = unit⇒η
            ; commute = commute₁
            }
          ; F⇐G = ntHelper record
            { η       = unit⇐η
            ; commute = commute₂
            }
          ; iso = iso
          }
          where open Mor Span
                commute₁ : ∀ (f : Fin ∣ a ⇒ b ∣) → unit⇒η b ∘ f ≡ SpanFromF.₁ (SpanToF.₁ f) ∘ unit⇒η a
                commute₁ {0F} {0F} 0F = refl
                commute₁ {0F} {1F} 0F = refl
                commute₁ {0F} {2F} 0F = refl
                commute₁ {1F} {1F} 0F = refl
                commute₁ {2F} {2F} 0F = refl
                commute₂ : ∀ (f : Fin ∣ a ⇒ b ∣) → unit⇐η b ∘ SpanFromF.₁ (SpanToF.₁ f) ≡ f ∘ unit⇐η a
                commute₂ {0F} {0F} 0F = refl
                commute₂ {0F} {1F} 0F = refl
                commute₂ {0F} {2F} 0F = refl
                commute₂ {1F} {1F} 0F = refl
                commute₂ {2F} {2F} 0F = refl

                iso : ∀ a → Iso (unit⇒η a) (unit⇐η a)
                iso 0F = record
                  { isoˡ = refl
                  ; isoʳ = refl
                  }
                iso 1F = record
                  { isoˡ = refl
                  ; isoʳ = refl
                  }
                iso 2F = record
                  { isoˡ = refl
                  ; isoʳ = refl
                  }

        counit⇒η : ∀ X → Sp.Span [ Functor.F₀ (SpanToF ∘F SpanFromF) X , X ]
        counit⇒η Sp.center = Sp.span-id
        counit⇒η Sp.left   = Sp.span-id
        counit⇒η Sp.right  = Sp.span-id

        counit⇐η : ∀ X → Sp.Span [ X , Functor.F₀ (SpanToF ∘F SpanFromF) X ]
        counit⇐η Sp.center = Sp.span-id
        counit⇐η Sp.left   = Sp.span-id
        counit⇐η Sp.right  = Sp.span-id

        counit : SpanToF ∘F SpanFromF ≃ idF
        counit = record
          { F⇒G = ntHelper record
            { η       = counit⇒η
            ; commute = commute₁
            }
          ; F⇐G = ntHelper record
            { η       = counit⇐η
            ; commute = commute₂
            }
          ; iso = iso
          }
          where open Mor Sp.Span
                commute₁ : ∀ {X Y} (f : Sp.SpanArr X Y) →
                             Sp.span-compose (counit⇒η Y) (SpanToF.₁ (SpanFromF.₁ f)) ≡ Sp.span-compose f (counit⇒η X)
                commute₁ {Sp.center} {.Sp.center} Sp.span-id   = refl
                commute₁ {Sp.left} {.Sp.left} Sp.span-id       = refl
                commute₁ {Sp.right} {.Sp.right} Sp.span-id     = refl
                commute₁ {.Sp.center} {.Sp.left} Sp.span-arrˡ  = refl
                commute₁ {.Sp.center} {.Sp.right} Sp.span-arrʳ = refl

                commute₂ : ∀ {X Y} (f : Sp.SpanArr X Y) →
                             Sp.span-compose (counit⇐η Y) f ≡ Sp.span-compose (SpanToF.₁ (SpanFromF.₁ f)) (counit⇐η X)
                commute₂ {Sp.center} {.Sp.center} Sp.span-id   = refl
                commute₂ {Sp.left} {.Sp.left} Sp.span-id       = refl
                commute₂ {Sp.right} {.Sp.right} Sp.span-id     = refl
                commute₂ {.Sp.center} {.Sp.left} Sp.span-arrˡ  = refl
                commute₂ {.Sp.center} {.Sp.right} Sp.span-arrʳ = refl

                iso : ∀ X → Iso (counit⇒η X) (counit⇐η X)
                iso Sp.center = record
                  { isoˡ = refl
                  ; isoʳ = refl
                  }
                iso Sp.left   = record
                  { isoˡ = refl
                  ; isoʳ = refl
                  }
                iso Sp.right  = record
                  { isoˡ = refl
                  ; isoʳ = refl
                  }

        zig : ∀ {a} → Sp.span-compose (counit⇒η (SpanToF.₀ a)) (SpanToF.₁ (unit⇒η a)) ≡ Sp.span-id
        zig {0F} = refl
        zig {1F} = refl
        zig {2F} = refl

SpansEquiv : ⊣Equivalence Span Sp.Span
SpansEquiv = record { L⊣⊢R = SpansEquivF }

module SpansEquiv = ⊣Equivalence SpansEquiv

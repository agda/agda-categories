{-# OPTIONS --without-K --safe #-}
open import Categories.Category

module Categories.Square.Core {o ℓ e} (C : Category o ℓ e) where

open import Level
open import Function renaming (id to idᶠ; _∘_ to _∙_)

open import Relation.Binary hiding (_⇒_)

open Category C

private
  variable
    X Y : Obj
    a a′ a″ b b′ b″ c c′ c″ : X ⇒ Y
    f g h i : X ⇒ Y
    
open HomReasoning

module Pulls (ab≡c : a ∘ b ≈ c) where

  pullʳ : (f ∘ a) ∘ b ≈ f ∘ c
  pullʳ {f = f} = begin
    (f ∘ a) ∘ b ≈⟨ assoc ⟩
    f ∘ (a ∘ b) ≈⟨ ∘-resp-≈ʳ ab≡c ⟩
    f ∘ c       ∎

  pullˡ : a ∘ b ∘ f ≈ c ∘ f
  pullˡ {f = f} = begin
    a ∘ b ∘ f   ≈⟨ sym assoc ⟩
    (a ∘ b) ∘ f ≈⟨ ab≡c ⟩∘⟨ refl ⟩
    c ∘ f       ∎

open Pulls public

module Pushes (c≡ab : c ≈ a ∘ b) where
  pushʳ : f ∘ c ≈ (f ∘ a) ∘ b
  pushʳ {f = f} = begin
    f ∘ c       ≈⟨ ∘-resp-≈ʳ c≡ab ⟩
    f ∘ (a ∘ b) ≈⟨ sym assoc ⟩
    (f ∘ a) ∘ b ∎

  pushˡ : c ∘ f ≈ a ∘ (b ∘ f)
  pushˡ {f = f} = begin
    c ∘ f       ≈⟨ ∘-resp-≈ˡ c≡ab ⟩
    (a ∘ b) ∘ f ≈⟨ assoc ⟩
    a ∘ (b ∘ f) ∎

open Pushes public

module IntroElim (a≡id : a ≈ id) where
  elimʳ : f ∘ a ≈ f
  elimʳ {f = f} = begin
    f ∘ a  ≈⟨ ∘-resp-≈ʳ a≡id ⟩
    f ∘ id ≈⟨ identityʳ ⟩
    f      ∎

  introʳ : f ≈ f ∘ a
  introʳ = Equiv.sym elimʳ

  elimˡ : (a ∘ f) ≈ f
  elimˡ {f = f} = begin
    a ∘ f  ≈⟨ ∘-resp-≈ˡ a≡id ⟩
    id ∘ f ≈⟨ identityˡ ⟩
    f      ∎

  introˡ : f ≈ a ∘ f
  introˡ = Equiv.sym elimˡ

open IntroElim public

module Extends (s : CommutativeSquare f g h i) where
  extendˡ : CommutativeSquare f g (a ∘ h) (a ∘ i)
  extendˡ {a = a} = begin
    (a ∘ h) ∘ f ≈⟨ pullʳ s ⟩
    a ∘ i ∘ g   ≈⟨ sym assoc ⟩
    (a ∘ i) ∘ g ∎

  extendʳ : CommutativeSquare (f ∘ a) (g ∘ a) h i
  extendʳ {a = a} = begin
    h ∘ (f ∘ a) ≈⟨ pullˡ s ⟩
    (i ∘ g) ∘ a ≈⟨ assoc ⟩
    i ∘ (g ∘ a) ∎

  extend² : CommutativeSquare (f ∘ b) (g ∘ b) (a ∘ h) (a ∘ i)
  extend² {b = b} {a = a } = begin
    (a ∘ h) ∘ (f ∘ b) ≈⟨ pullʳ extendʳ ⟩
    a ∘ (i ∘ (g ∘ b)) ≈⟨ sym assoc ⟩
    (a ∘ i) ∘ (g ∘ b) ∎

open Extends public

-- essentially composition in the arrow category
{-
   A₁ -- c --> B₁
   |           |
   b′  comm    b
   |           |
   V           V
   A₂ -- c′ -> B₂
   |           |
   a′  comm    a
   |           |
   V           V
   A₃ -- c″ -> B₃
 
   then the whole diagram commutes
-}
glue : CommutativeSquare c′ a′ a c″ →
       CommutativeSquare c b′ b c′ →
       CommutativeSquare c (a′ ∘ b′) (a ∘ b) c″
glue {c′ = c′} {a′ = a′} {a = a} {c″ = c″} {c = c} {b′ = b′} {b = b} sq-a sq-b = begin
  (a ∘ b) ∘ c    ≈⟨ pullʳ sq-b ⟩
  a ∘ (c′ ∘ b′)  ≈⟨ pullˡ sq-a ⟩
  (c″ ∘ a′) ∘ b′ ≈⟨ assoc ⟩
  c″ ∘ (a′ ∘ b′) ∎

glue◃◽ : a ∘ c′ ≈ c″ → CommutativeSquare c b′ b c′ → CommutativeSquare c b′ (a ∘ b) c″
glue◃◽ {a = a} {c′ = c′} {c″ = c″} {c = c} {b′ = b′} {b = b} tri-a sq-b = begin
  (a ∘ b) ∘ c   ≈⟨ pullʳ sq-b ⟩
  a ∘ (c′ ∘ b′) ≈⟨ pullˡ tri-a ⟩
  c″ ∘ b′       ∎

-- essentially composition in the over category
glueTrianglesʳ : a ∘ b ≈ a′ → a′ ∘ b′ ≈ a″ → a ∘ (b ∘ b′) ≈ a″
glueTrianglesʳ {a = a} {b = b} {a′ = a′} {b′ = b′} {a″ = a″} a∘b≡a′ a′∘b′≡a″ = begin
  a ∘ (b ∘ b′) ≈⟨ pullˡ a∘b≡a′ ⟩
  a′ ∘ b′      ≈⟨ a′∘b′≡a″ ⟩
  a″           ∎

-- essentially composition in the under category
glueTrianglesˡ : a′ ∘ b′ ≈ b″ → a ∘ b ≈ b′ → (a′ ∘ a) ∘ b ≈ b″
glueTrianglesˡ {a′ = a′} {b′ = b′} {b″ = b″} {a = a} {b = b} a′∘b′≡b″ a∘b≡b′ = begin
  (a′ ∘ a) ∘ b ≈⟨ pullʳ a∘b≡b′ ⟩
  a′ ∘ b′      ≈⟨ a′∘b′≡b″ ⟩
  b″           ∎

module Cancellers (inv : h ∘ i ≈ id) where

  cancelRight : (f ∘ h) ∘ i ≈ f
  cancelRight {f = f} = begin
    (f ∘ h) ∘ i ≈⟨ pullʳ inv ⟩
    f ∘ id      ≈⟨ identityʳ ⟩
    f           ∎

  cancelLeft : h ∘ (i ∘ f) ≈ f
  cancelLeft {f = f} = begin
    h ∘ (i ∘ f) ≈⟨ pullˡ inv ⟩
    id ∘ f      ≈⟨ identityˡ ⟩
    f           ∎

  cancelInner : (f ∘ h) ∘ (i ∘ g) ≈ f ∘ g
  cancelInner {f = f} {g = g} = begin
    (f ∘ h) ∘ (i ∘ g) ≈⟨ pullˡ cancelRight ⟩
    f ∘ g             ∎

open Cancellers public

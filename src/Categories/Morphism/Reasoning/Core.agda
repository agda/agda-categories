{-# OPTIONS --without-K --safe #-}
open import Categories.Category

{-
  Helper routines most often used in reasoning with commutative squares,
  at the level of arrows in categories.

  Identity : reasoning about identity
  Assoc4   : associativity combinators for composites of 4 morphisms
  Pulls  : use a ∘ b ≈ c as left-to-right rewrite
  Pushes : use c ≈ a ∘ b as a left-to-right rewrite
  IntroElim : introduce/eliminate an equivalent-to-id arrow
  Extend : 'extends' a commutative square with an equality on left/right/both

  Convention - in this file, extra parentheses are used to clearly show
    associativity. This makes reading the source more pedagogical as to the
    intent of each routine.
-}
module Categories.Morphism.Reasoning.Core {o ℓ e} (C : Category o ℓ e) where

open import Level
open import Function renaming (id to idᶠ; _∘_ to _∙_)

open import Relation.Binary hiding (_⇒_)

open Category C
open Definitions C

private
  variable
    X Y : Obj
    a a′ a″ b b′ b″ c c′ c″ : X ⇒ Y
    f g h i : X ⇒ Y

open HomReasoning

module Identity where
  id-unique : ∀ {o} {f : o ⇒ o} → (∀ g → g ∘ f ≈ g) → f ≈ id
  id-unique g∘f≈g = Equiv.trans (Equiv.sym identityˡ) (g∘f≈g id)

  id-comm : ∀ {a b} {f : a ⇒ b} → f ∘ id ≈ id ∘ f
  id-comm = Equiv.trans identityʳ (Equiv.sym identityˡ)

  id-comm-sym : ∀ {a b} {f : a ⇒ b} → id ∘ f ≈ f ∘ id
  id-comm-sym = Equiv.trans identityˡ (Equiv.sym identityʳ)

open Identity public

module Assoc4 where
  {-
  Explanation of naming scheme:

  Each successive association is given a Greek letter, from 'α' associated all
  the way to the left, to 'ε' associated all the way to the right. Then,
  'assoc²XY' is the proof that X is equal to Y. Explicitly:

  α = ((i ∘ h) ∘ g) ∘ f
  β = (i ∘ (h ∘ g)) ∘ f
  γ = (i ∘ h) ∘ (g ∘ f)
  δ = i ∘ ((h ∘ g) ∘ f)
  ε = i ∘ (h ∘ (g ∘ f))

  Only reassociations that need two assoc steps are defined here.
  -}

  assoc²αδ : ((i ∘ h) ∘ g) ∘ f ≈ i ∘ ((h ∘ g) ∘ f)
  assoc²αδ = ∘-resp-≈ˡ assoc ○ assoc

  assoc²αε : ((i ∘ h) ∘ g) ∘ f ≈ i ∘ (h ∘ (g ∘ f))
  assoc²αε = assoc ○ assoc

  assoc²βγ : (i ∘ (h ∘ g)) ∘ f ≈ (i ∘ h) ∘ (g ∘ f)
  assoc²βγ = ∘-resp-≈ˡ sym-assoc ○ assoc

  assoc²βε : (i ∘ (h ∘ g)) ∘ f ≈ i ∘ (h ∘ (g ∘ f))
  assoc²βε = assoc ○ ∘-resp-≈ʳ assoc

  assoc²γβ : (i ∘ h) ∘ (g ∘ f) ≈ (i ∘ (h ∘ g)) ∘ f
  assoc²γβ = sym-assoc ○ ∘-resp-≈ˡ assoc

  assoc²γδ : (i ∘ h) ∘ (g ∘ f) ≈ i ∘ ((h ∘ g) ∘ f)
  assoc²γδ = assoc ○ ∘-resp-≈ʳ sym-assoc

  assoc²δα : i ∘ ((h ∘ g) ∘ f) ≈ ((i ∘ h) ∘ g) ∘ f
  assoc²δα = sym-assoc ○ ∘-resp-≈ˡ sym-assoc

  assoc²δγ : i ∘ ((h ∘ g) ∘ f) ≈ (i ∘ h) ∘ (g ∘ f)
  assoc²δγ = ∘-resp-≈ʳ assoc ○ sym-assoc

  assoc²εα : i ∘ (h ∘ (g ∘ f)) ≈ ((i ∘ h) ∘ g) ∘ f
  assoc²εα = sym-assoc ○ sym-assoc

  assoc²εβ : i ∘ (h ∘ (g ∘ f)) ≈ (i ∘ (h ∘ g)) ∘ f
  assoc²εβ = ∘-resp-≈ʳ sym-assoc ○ sym-assoc

open Assoc4 public

-- Pulls use "a ∘ b ≈ c" as left-to-right rewrite
-- pull to the right / left of something existing
module Pulls (ab≡c : a ∘ b ≈ c) where

  pullʳ : (f ∘ a) ∘ b ≈ f ∘ c
  pullʳ {f = f} = begin
    (f ∘ a) ∘ b ≈⟨ assoc ⟩
    f ∘ (a ∘ b) ≈⟨ refl⟩∘⟨ ab≡c ⟩
    f ∘ c       ∎

  pullˡ : a ∘ (b ∘ f) ≈ c ∘ f
  pullˡ {f = f} = begin
    a ∘ b ∘ f   ≈⟨ sym-assoc ⟩
    (a ∘ b) ∘ f ≈⟨ ab≡c ⟩∘⟨refl ⟩
    c ∘ f       ∎

open Pulls public

-- Pushes use "c ≈ a ∘ b" as a left-to-right rewrite
-- push to the right / left of something existing
module Pushes (c≡ab : c ≈ a ∘ b) where
  pushʳ : f ∘ c ≈ (f ∘ a) ∘ b
  pushʳ {f = f} = begin
    f ∘ c       ≈⟨ refl⟩∘⟨ c≡ab ⟩
    f ∘ (a ∘ b) ≈⟨ sym-assoc ⟩
    (f ∘ a) ∘ b ∎

  pushˡ : c ∘ f ≈ a ∘ (b ∘ f)
  pushˡ {f = f} = begin
    c ∘ f       ≈⟨ c≡ab ⟩∘⟨refl ⟩
    (a ∘ b) ∘ f ≈⟨ assoc ⟩
    a ∘ (b ∘ f) ∎

open Pushes public

-- Introduce/Elimilate an equivalent-to-identity
-- on left, right or 'in the middle' of something existing
module IntroElim (a≡id : a ≈ id) where
  elimʳ : f ∘ a ≈ f
  elimʳ {f = f} = begin
    f ∘ a  ≈⟨ refl⟩∘⟨ a≡id ⟩
    f ∘ id ≈⟨ identityʳ ⟩
    f      ∎

  introʳ : f ≈ f ∘ a
  introʳ = Equiv.sym elimʳ

  elimˡ : (a ∘ f) ≈ f
  elimˡ {f = f} = begin
    a ∘ f  ≈⟨ a≡id ⟩∘⟨refl ⟩
    id ∘ f ≈⟨ identityˡ ⟩
    f      ∎

  introˡ : f ≈ a ∘ f
  introˡ = Equiv.sym elimˡ

  intro-center : f ∘ g ≈ f ∘ (a ∘ g)
  intro-center = ∘-resp-≈ʳ introˡ

  elim-center : f ∘ (a ∘ g) ≈ f ∘ g
  elim-center = ∘-resp-≈ʳ elimˡ

open IntroElim public

-- given h ∘ f ≈ i ∘ g
module Extends (s : CommutativeSquare f g h i) where
  -- rewrite (a ∘ h) ∘ f to (a ∘ i) ∘ g
  extendˡ : CommutativeSquare f g (a ∘ h) (a ∘ i)
  extendˡ {a = a} = begin
    (a ∘ h) ∘ f ≈⟨ pullʳ s ⟩
    a ∘ (i ∘ g) ≈⟨ sym-assoc ⟩
    (a ∘ i) ∘ g ∎

  -- rewrite h ∘ (f ∘ a) to i ∘ (g ∘ a)
  extendʳ : CommutativeSquare (f ∘ a) (g ∘ a) h i
  extendʳ {a = a} = begin
    h ∘ (f ∘ a) ≈⟨ pullˡ s ⟩
    (i ∘ g) ∘ a ≈⟨ assoc ⟩
    i ∘ (g ∘ a) ∎

  -- rewrite (a ∘ h) ∘ (f ∘ b) to (a ∘ i) ∘ (g ∘ b)
  extend² : CommutativeSquare (f ∘ b) (g ∘ b) (a ∘ h) (a ∘ i)
  extend² {b = b} {a = a } = begin
    (a ∘ h) ∘ (f ∘ b) ≈⟨ pullʳ extendʳ ⟩
    a ∘ (i ∘ (g ∘ b)) ≈⟨ sym-assoc ⟩
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
  a ∘ (c′ ∘ b′)  ≈⟨ extendʳ sq-a ⟩
  c″ ∘ (a′ ∘ b′) ∎

-- A "rotated" version of glue′. Equivalent to 'Equiv.sym (glue (Equiv.sym sq-a) (Equiv.sym sq-b))'
glue′ : CommutativeSquare a′ c′ c″ a →
        CommutativeSquare b′ c c′ b →
        CommutativeSquare (a′ ∘ b′) c c″ (a ∘ b)
glue′ {a′ = a′} {c′ = c′} {c″ = c″} {a = a} {b′ = b′} {c = c} {b = b} sq-a sq-b = begin
  c″ ∘ (a′ ∘ b′) ≈⟨ pullˡ sq-a ⟩
  (a ∘ c′) ∘ b′  ≈⟨ extendˡ sq-b ⟩
  (a ∘ b) ∘ c    ∎

-- Various gluings of triangles onto sides of squares
glue◃◽ : a ∘ c′ ≈ c″ → CommutativeSquare c b′ b c′ → CommutativeSquare c b′ (a ∘ b) c″
glue◃◽ {a = a} {c′ = c′} {c″ = c″} {c = c} {b′ = b′} {b = b} tri-a sq-b = begin
  (a ∘ b) ∘ c   ≈⟨ pullʳ sq-b ⟩
  a ∘ (c′ ∘ b′) ≈⟨ pullˡ tri-a ⟩
  c″ ∘ b′       ∎

glue◃◽′ : c ∘ c′ ≈ a′ → CommutativeSquare a b a′ b′ → CommutativeSquare (c′ ∘ a) b c b′
glue◃◽′ {c = c} {c′ = c′} {a′ = a′} {a = a} {b = b} {b′ = b′} tri sq = begin
  c ∘ (c′ ∘ a) ≈⟨ pullˡ tri ⟩
  a′ ∘ a       ≈⟨ sq ⟩
  b′ ∘ b       ∎

glue◽◃ : CommutativeSquare a b a′ b′ → b ∘ c ≈ c′ → CommutativeSquare (a ∘ c) c′ a′ b′
glue◽◃ {a = a} {b = b} {a′ = a′} {b′ = b′} {c = c} {c′ = c′} sq tri = begin
  a′ ∘ a ∘ c   ≈⟨ pullˡ sq ⟩
  (b′ ∘ b) ∘ c ≈⟨ pullʳ tri ⟩
  b′ ∘ c′      ∎

glue▹◽ : b ∘ a″ ≈ c → CommutativeSquare a b a′ b′ → CommutativeSquare (a ∘ a″) c a′ b′
glue▹◽ {b = b} {a″ = a″} {c = c} {a = a} {a′ = a′} {b′ = b′} tri sq = begin
  a′ ∘ a ∘ a″   ≈⟨ pullˡ sq ⟩
  (b′ ∘ b) ∘ a″ ≈⟨ pullʳ tri ⟩
  b′ ∘ c        ∎

glue◽▹ : CommutativeSquare a b a′ b′ → c ∘ c′ ≈ a → CommutativeSquare c′ b (a′ ∘ c) b′
glue◽▹ {a = a} {b = b} {a′ = a′} {b′ = b′} {c = c} {c′ = c′} sq tri = begin
  (a′ ∘ c) ∘ c′   ≈⟨ pullʳ tri ⟩
  a′ ∘ a ≈⟨ sq ⟩
  b′ ∘ b      ∎

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

-- Cancel (or insert) inverses on right/left/middle
module Cancellers (inv : h ∘ i ≈ id) where

  cancelʳ : (f ∘ h) ∘ i ≈ f
  cancelʳ {f = f} = begin
    (f ∘ h) ∘ i ≈⟨ pullʳ inv ⟩
    f ∘ id      ≈⟨ identityʳ ⟩
    f           ∎

  insertʳ : f ≈ (f ∘ h) ∘ i
  insertʳ = ⟺ cancelʳ

  cancelˡ : h ∘ (i ∘ f) ≈ f
  cancelˡ {f = f} = begin
    h ∘ (i ∘ f) ≈⟨ pullˡ inv ⟩
    id ∘ f      ≈⟨ identityˡ ⟩
    f           ∎

  insertˡ : f ≈ h ∘ (i ∘ f)
  insertˡ = ⟺ cancelˡ

  cancelInner : (f ∘ h) ∘ (i ∘ g) ≈ f ∘ g
  cancelInner = pullˡ cancelʳ

  insertInner : f ∘ g ≈ (f ∘ h) ∘ (i ∘ g)
  insertInner = ⟺ cancelInner

open Cancellers public

-- operate in the 'center' instead (like pull/push)
center : g ∘ h ≈ a → (f ∘ g) ∘ (h ∘ i) ≈ f ∘ (a ∘ i)
center eq = pullʳ (pullˡ eq)

-- operate on the left part, then the right part
center⁻¹ : f ∘ g ≈ a → h ∘ i ≈ b →  f ∘ ((g ∘ h) ∘ i) ≈ a ∘ b
center⁻¹ {f = f} {g = g} {a = a} {h = h} {i = i} {b = b} eq eq′ = begin
  f ∘ (g ∘ h) ∘ i ≈⟨ refl⟩∘⟨ pullʳ eq′ ⟩
  f ∘ (g ∘ b)     ≈⟨ pullˡ eq ⟩
  a ∘ b           ∎

-- could be called pull₃ʳ
pull-last : h ∘ i ≈ a → (f ∘ g ∘ h) ∘ i ≈ f ∘ g ∘ a
pull-last eq = pullʳ (pullʳ eq)

pull-first : f ∘ g ≈ a → f ∘ ((g ∘ h) ∘ i) ≈ a ∘ (h ∘ i)
pull-first {f = f} {g = g} {a = a} {h = h} {i = i} eq = begin
  f ∘ (g ∘ h) ∘ i ≈⟨ refl⟩∘⟨ assoc ⟩
  f ∘ g ∘ h ∘ i   ≈⟨ pullˡ eq ⟩
  a ∘ h ∘ i       ∎

pull-center : g ∘ h ≈ a → f ∘ (g ∘ (h ∘ i)) ≈ f ∘ (a ∘ i)
pull-center eq = ∘-resp-≈ʳ (pullˡ eq)

push-center : a ≈ g ∘ h → f ∘ (a ∘ i) ≈ f ∘ (g ∘ (h ∘ i))
push-center eq = Equiv.sym (pull-center (Equiv.sym eq))

intro-first : a ∘ b ≈ id → f ∘ g ≈ a ∘ ((b ∘ f) ∘ g)
intro-first {a = a} {b = b} {f = f} {g = g} eq = begin
  f ∘ g             ≈⟨ introˡ eq ⟩
  (a ∘ b) ∘ (f ∘ g) ≈⟨ pullʳ sym-assoc ⟩
  a ∘ ((b ∘ f) ∘ g) ∎

intro-last : a ∘ b ≈ id → f ∘ g ≈ f ∘ (g ∘ a) ∘ b
intro-last {a = a} {b = b} {f = f} {g = g} eq = begin
  f ∘ g           ≈⟨ introʳ eq ⟩
  (f ∘ g) ∘ a ∘ b ≈⟨ pullʳ sym-assoc ⟩
  f ∘ (g ∘ a) ∘ b ∎

{-# OPTIONS --without-K --safe #-}

--------------------------------------------------------------------------------
-- Monoidal coherence tactic.
--
-- `Core` exposes a free structural language for monoidal categories and its
-- interpretation in an arbitrary monoidal category.  `solve₀` proves
-- object-level canonical isomorphism goals, and `solveMonoidal` proves equality
-- of interpreted structural paths whose normal-form loop computes to `refl`.
--------------------------------------------------------------------------------

module Categories.Tactic.Monoidal where

open import Function using (_⟨_⟩_)

open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Agda.Builtin.Reflection
open import Reflection.AST.Argument
open import Reflection.AST.Term using (_⋯⟅∷⟆_)
open import Reflection.TCM.Syntax

open import Categories.Tactic.Monoidal.Core public

private
  visibleTailPair : List (Arg Term) → Maybe (Term × Term)
  visibleTailPair (vArg x ∷ vArg y ∷ []) = just (x , y)
  visibleTailPair (_ ∷ args)             = visibleTailPair args
  visibleTailPair []                     = nothing

  getArgs : Term → Maybe (Term × Term)
  getArgs (def _ args) = visibleTailPair args
  getArgs _ = nothing

  lastVisible : List (Arg Term) → Maybe Term
  lastVisible []              = nothing
  lastVisible (vArg x ∷ [])   = just x
  lastVisible (vArg x ∷ args) = maybe just (just x) (lastVisible args)
  lastVisible (_ ∷ args)      = lastVisible args

  getPath : Term → Maybe Term
  getPath (def _ args) = lastVisible args
  getPath (con _ args) = lastVisible args
  getPath _            = nothing

  getPathPair : Term × Term → Maybe (Term × Term)
  getPathPair (lhs , rhs) =
    maybe
      (λ lhs′ → maybe (λ rhs′ → just (lhs′ , rhs′)) nothing (getPath rhs))
      nothing
      (getPath lhs)

  getPaths : Term → Maybe (Term × Term)
  getPaths goal = maybe getPathPair nothing (getArgs goal)

  -- Full normalisation unfolds `⟦_⟧₁` and loses the free structural path.
  -- Weak reduction is enough to expose simple goal aliases.
  parseFallback : Term → TC (Term × Term)
  parseFallback goal = do
    goal′ ← reduce goal
    maybe returnTC
      (typeError
        ( strErr "Categories.Tactic.Monoidal: expected a goal of the form "
        ∷ strErr "⟦ f ⟧₁ ≈ ⟦ g ⟧₁ or ⟦ X ⟧₀ ≅ ⟦ Y ⟧₀; got "
        ∷ termErr goal ∷ []))
      (getPaths goal′)

  parseGoal : Term → TC (Term × Term)
  parseGoal goal = maybe returnTC (parseFallback goal) (getPaths goal)

  constructSoln : Term → Term → Term → Term → Term
  constructSoln M ⟦_⟧ₐ lhs rhs =
    quote Categories.Tactic.Monoidal.Core.coherence ⟨ def ⟩
      5 ⋯⟅∷⟆
      M ⟨∷⟩
      unknown ⟅∷⟆
      ⟦_⟧ₐ ⟨∷⟩
      unknown ⟅∷⟆
      unknown ⟅∷⟆
      lhs ⟨∷⟩
      rhs ⟨∷⟩
      (quote refl ⟨ con ⟩ []) ⟨∷⟩
      []

  constructObjectSoln : Term → Term → Term → Term → Term
  constructObjectSoln M ⟦_⟧ₐ lhs rhs =
    quote Categories.Tactic.Monoidal.Core.object-coherence ⟨ def ⟩
      5 ⋯⟅∷⟆
      M ⟨∷⟩
      unknown ⟅∷⟆
      ⟦_⟧ₐ ⟨∷⟩
      lhs ⟅∷⟆
      rhs ⟅∷⟆
      (quote refl ⟨ con ⟩ []) ⟨∷⟩
      []

  solve-macro : Term → Term → Term → TC _
  solve-macro M ⟦_⟧ₐ hole = do
    goal ← inferType hole
    (lhs , rhs) ← parseGoal goal
    unify hole (constructSoln M ⟦_⟧ₐ lhs rhs)

  solve₀-macro : Term → Term → Term → TC _
  solve₀-macro M ⟦_⟧ₐ hole = do
    goal ← inferType hole
    (lhs , rhs) ← parseGoal goal
    unify hole (constructObjectSoln M ⟦_⟧ₐ lhs rhs)

macro
  solve₀ : Term → Term → Term → TC _
  solve₀ = solve₀-macro

  solveMonoidal : Term → Term → Term → TC _
  solveMonoidal = solve-macro

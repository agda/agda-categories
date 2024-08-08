{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category; _[_,_])

open import Data.List.Base    as List    using (List; _∷_; [] ; _++_)
open import Data.Fin

open import Reflection.AST
open import Reflection.AST.Term
open import Reflection.AST.Argument
import Reflection.AST.Name as Name
open import Reflection.TCM
open import Reflection.TCM.Syntax

open import Data.Nat
open import Data.Bool
open import Data.Unit

module Categories.Category.AssociativitySolver {o ℓ e} (CC : Category o ℓ e) where

-- We use a simple code to document the real code. This simple code is
-- a magma associativity solver. Similar to Monoid solver in Agda
-- stdlib.
module Documentation1 where

  private
    variable
      X : Set
      
  infixr 7 _∙_
  data Expr {a} (A : Set a) : Set a where
    _∙_  : Expr A → Expr A → Expr A
    gen  : A → Expr A

  data NF {a} (A : Set a) : Set a where
    _∙_  : A → NF A → NF A
    gen  : A → NF A

  combine-nf : NF X -> NF X -> NF X
  combine-nf (x ∙ a) b = x ∙ (combine-nf a b)
  combine-nf (gen x) b = x ∙ b

  combine-nf' : Expr X -> Expr X -> Expr X
  combine-nf' (x ∙ a) b = x ∙ (combine-nf' a b)
  combine-nf' (gen x) b = gen x ∙ b

  nf : Expr X -> NF X
  nf (e ∙ e₁) = combine-nf (nf e) (nf e₁)
  nf (gen a) = gen a

  nf' : Expr X -> Expr X
  nf' (e ∙ e₁) = combine-nf' (nf' e) (nf' e₁)
  nf' (gen a) = gen a

  expr-of-nf : NF X -> Expr X
  expr-of-nf (x ∙ n) = gen x ∙ expr-of-nf n
  expr-of-nf (gen x) = gen x

  infix 6 _===_

  data _===_ {X : Set} : Expr X -> Expr X -> Set where

    -- The relation '===' is a congruence.
    refl : ∀ {w} -> w === w
    symm : ∀ {w v} -> w === v -> v === w
    tran : ∀ {w v u} -> w === v -> v === u -> w === u
    cong : ∀ {w w' v v'} -> w === w' -> v === v' -> w ∙ v === w' ∙ v'

    -- associativity.
    asso : ∀ {w v u} -> (w ∙ v) ∙ u === w ∙ (v ∙ u)

  lemma-combine : ∀ (n m : NF X) -> expr-of-nf n ∙ expr-of-nf m === expr-of-nf (combine-nf n m)
  lemma-combine (x ∙ n) m with lemma-combine n m
  ... | ih = tran asso (cong refl ih)
  lemma-combine (gen x) m = refl

  lemma-combine' : ∀ (n m : Expr X) -> n ∙ m === (combine-nf' n m)
  lemma-combine' (n ∙ n₁) m = tran asso (cong refl (lemma-combine' n₁ m))
  lemma-combine' (gen x) m = refl

  lemma-nf : (e : Expr X) -> e === expr-of-nf (nf e)
  lemma-nf (e ∙ e₁) with lemma-nf e | lemma-nf e₁
  ... | ih1 | ih2 = tran (cong ih1 ih2) (lemma-combine (nf e) (nf e₁))
  lemma-nf (gen x) = refl

  lemma-nf' : (e : Expr X) -> e === nf' e
  lemma-nf' (e ∙ e₁) = tran (cong (lemma-nf' e) (lemma-nf' e₁)) (lemma-combine' (nf' e) (nf' e₁))
  lemma-nf' (gen x) = refl


-- Real code starts here:

open Category CC

-- Terms for fields of Category CC.
idlt : Term
idlt = def (quote identityˡ) (3 ⋯⟅∷⟆ [])

idrt : Term
idrt = def (quote identityʳ) (3 ⋯⟅∷⟆ [])

assoct : Term
assoct = def (quote assoc) (7 ⋯⟅∷⟆ [])

sym-assoct : Term
sym-assoct = def (quote sym-assoc) (7 ⋯⟅∷⟆ [])

id2t : Term
id2t = def (quote identity²) (1 ⋯⟅∷⟆ [])

equivt : Term
equivt = def (quote identity²) (2 ⋯⟅∷⟆ [])

respt : Term -> Term -> Term
respt fh gi = def (quote ∘-resp-≈) (7 ⋯⟅∷⟆ fh ⟨∷⟩ gi ⟨∷⟩ [])

reflt : Term
reflt = def (quote Equiv.refl) (3 ⋯⟅∷⟆ [])

symt : Term -> Term
symt x = def (quote Equiv.sym) (4 ⋯⟅∷⟆ x ⟨∷⟩ [])

transt : Term -> Term -> Term
transt xy yz = def (quote Equiv.trans) (5 ⋯⟅∷⟆ xy ⟨∷⟩ yz ⟨∷⟩ [])

-- Code documentation2. Assuming we can easily pattern matching to get
-- operands.
module Documentation2 where
  -- Given two normal forms, combine them into one normal form.
  combine-nf : Term -> Term -> Term
  combine-nf (def (quote _∘_) (i4 ⟅∷⟆ i5 ⟅∷⟆ i6 ⟅∷⟆ a ⟨∷⟩ b ⟨∷⟩ [])) r = (def (quote _∘_) (3 ⋯⟅∷⟆ a ⟨∷⟩ (combine-nf b r) ⟨∷⟩ [])) 
  combine-nf l r = def (quote _∘_) (3 ⋯⟅∷⟆ l ⟨∷⟩ r ⟨∷⟩ [])

  -- Normalize a term wrt _∘_.
  nf : Term -> Term
  nf (def (quote _∘_) (i4 ⟅∷⟆ i5 ⟅∷⟆ i6 ⟅∷⟆ a ⟨∷⟩ b ⟨∷⟩ [])) = combine-nf (nf a) (nf b)
  nf t = t

  -- lemma-combine-nf nf1 nf2 gives a proof that nf1 • nf2 == combine-nf
  -- nf1 nf2.
  lemma-combine-nf : Term -> Term -> Term
  lemma-combine-nf (def (quote _∘_) (i4 ⟅∷⟆ i5 ⟅∷⟆ i6 ⟅∷⟆ a ⟨∷⟩ b ⟨∷⟩ [])) r = transt assoct (respt reflt (lemma-combine-nf b r))
  lemma-combine-nf l r = reflt

  -- lemma-nf e gives a proof that e == nf e.
  lemma-nf : Term -> Term
  lemma-nf (def (quote _∘_) (i4 ⟅∷⟆ i5 ⟅∷⟆ i6 ⟅∷⟆ bc ⟨∷⟩ ab ⟨∷⟩ [])) with lemma-nf bc | lemma-nf ab
  ...| ih1 | ih2 = transt (respt ih1 ih2) (lemma-combine-nf (nf bc) (nf ab))
  lemma-nf e = reflt

  construct-sol : Term → Term → Term
  construct-sol lhs rhs = let
    le = lemma-nf lhs in let
    re = lemma-nf rhs in
    (transt le (symt re))

-- Real code reusme:
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Product using (_×_ ; _,_)

-- Get the last two visible argument in a list of arguments. For
-- binary operators, the last visible two arguments are its operands.
last2 : List (Arg Term) → Maybe (Term × Term)
last2 (vArg x ∷ vArg y ∷ []) = just (x , y)
last2 (x ∷ xs)               = last2 xs
last2 _                      = nothing

-- A wrap for last2 that works for a term.
last2' : Term → Maybe (Term × Term)
last2' (def _ xs) = last2 xs
last2' _ = nothing

-- Something happens here, which I don't fully understand:

-- On one hand, in assoct, transt, ... etc, the args in "def (quote
-- assoc) args" contains only its own argumments, not including
-- levels in "record Category (o ℓ e : Level)" and an explicit
-- Category record. If you unify this simple assoct, it works. E.g.

-- assoct = def (quote assoc) (7 ⋯⟅∷⟆ [])
-- (def (quote _∘_) (i1 ⟅∷⟆ i2 ⟅∷⟆ i3 ⟅∷⟆ a ⟨∷⟩ b ⟨∷⟩ [])

-- One the other hand, when you "quoteTerm (f ∘ g)", you will get
-- "full arguments" like:

-- def (quote Category._∘_) (unknown ⟅∷⟆ unknown ⟅∷⟆ unknown ⟅∷⟆ var
-- 9 [] ⟨∷⟩ var 8 [] ⟅∷⟆ var 7 [] ⟅∷⟆ var 6 [] ⟅∷⟆ var 5 [] ⟨∷⟩ var
-- 3 [] ⟨∷⟩ [])

-- So, the following 4 function deal with both cases.

-- Combine two normal form into one.
combine-nf : ℕ -> Term -> Term -> TC Term
combine-nf zero l@(def (quote Category._∘_) args) r = typeError (termErr l ∷ [])
combine-nf (suc n) l@(def (quote Category._∘_) args) r = do
  just (a , b) <- pure (last2 args)
    where nothing → typeError (termErr l ∷ [])
  br <- combine-nf n b r
  pure ((def (quote _∘_) (3 ⋯⟅∷⟆ a ⟨∷⟩ (br) ⟨∷⟩ [])) )
combine-nf zero l@(def (quote _∘_) args) r = typeError (termErr l ∷ [])
combine-nf (suc n) l@(def (quote _∘_) args) r = do
  just (a , b) <- pure (last2 args)
    where nothing → typeError (termErr l ∷ [])
  br <- combine-nf n b r
  pure ((def (quote _∘_) (3 ⋯⟅∷⟆ a ⟨∷⟩ (br) ⟨∷⟩ [])) )
combine-nf n l r = pure (def (quote _∘_) (3 ⋯⟅∷⟆ l ⟨∷⟩ r ⟨∷⟩ []))

-- Normalize a term wrt _∘_.
nf : ℕ -> Term -> TC Term
nf zero e@(def (quote Category._∘_) args) = typeError (termErr e ∷ [])
nf (suc n) e@(def (quote Category._∘_) args) = do
  just (a , b) <- pure (last2 args)
    where nothing → typeError (termErr e ∷ [])
  a' <- nf (n) a
  b' <- nf (n) b
  combine-nf n (a') (b')
nf zero e@(def (quote _∘_) args) = typeError (termErr e ∷ [])
nf (suc n) e@(def (quote _∘_) args) = do
  just (a , b) <- pure (last2 args)
    where nothing → typeError (termErr e ∷ [])
  a' <- nf (n) a
  b' <- nf (n) b
  combine-nf n (a') (b')
nf n t = pure t

-- lemma-combine-nf nf1 nf2 gives a proof that nf1 • nf2 == combine-nf
-- nf1 nf2.
lemma-combine-nf : ℕ -> Term -> Term -> TC Term
lemma-combine-nf zero l@(def (quote Category._∘_) args) r = typeError (termErr l ∷ [])
lemma-combine-nf (suc n) l@(def (quote Category._∘_) args) r = do
  just (a , b) ← pure (last2 args)
    where nothing → typeError (termErr l ∷ [])
  br <- lemma-combine-nf n b r
  pure (transt assoct (respt reflt br))
lemma-combine-nf zero l@(def (quote _∘_) args) r = typeError (termErr l ∷ [])
lemma-combine-nf (suc n) l@(def (quote _∘_) args) r = do
  just (a , b) ← pure (last2 args)
    where nothing → typeError (termErr l ∷ [])
  br <- lemma-combine-nf n b r
  pure (transt assoct (respt reflt br))
lemma-combine-nf n l r = pure reflt

-- lemma-nf e gives a proof that e == nf e.
lemma-nf : ℕ -> Term -> TC Term
lemma-nf zero e@(def (quote Category._∘_) args) = typeError (termErr e ∷ [])
lemma-nf (suc n) e@(def (quote Category._∘_) args) = do
  just (bc , ab) ← pure (last2 args)
    where nothing → typeError (termErr e ∷ [])
  ih1 <- lemma-nf n bc
  ih2 <- lemma-nf n ab
  nfbc <- nf (suc n) bc
  nfab <- nf (suc n) ab
  comb <- (lemma-combine-nf (suc n) (nfbc) (nfab))
  pure (transt (respt ih1 ih2) comb)
lemma-nf zero e@(def (quote _∘_) args) = typeError (termErr e ∷ [])
lemma-nf (suc n) e@(def (quote _∘_) args) = do
  just (bc , ab) ← pure (last2 args)
    where nothing → typeError (termErr e ∷ [])
  ih1 <- lemma-nf n bc
  ih2 <- lemma-nf n ab
  nfbc <- nf (suc n) bc
  nfab <- nf (suc n) ab
  comb <- (lemma-combine-nf (suc n) (nfbc) (nfab))
  pure (transt (respt ih1 ih2) comb)
lemma-nf n e = pure reflt

-- Given lhs and rhs, construct a proof that lhs == rhs.
construct-sol : ℕ -> Term → Term → TC Term
construct-sol n lhs rhs = do
  le <- lemma-nf n lhs
  re <- lemma-nf n rhs
  pure (transt le (symt re))

-- Agda macro mechanism quotes the hole and, we then can get the lhs
-- and rhs.
auto-assoc-macro : ℕ -> Term -> TC ⊤
auto-assoc-macro n hole = do
  hole′ ← inferType hole >>= normalise
  just (lhs , rhs) ← pure (last2' hole′)
    where nothing → typeError (termErr hole′ ∷ [])
  sol <- construct-sol n lhs rhs
  unify sol hole

macro
  auto-assoc : ℕ -> Term -> TC ⊤
  auto-assoc = auto-assoc-macro

module Example  where

  eg1 : ∀ {A B C D : Obj} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} →
    ((h ∘ g) ∘ f) ≈ (h ∘ (g ∘ f))
  eg1 {A}{B}{C}{D} {f}  = auto-assoc 10

  eg2 : ∀ {A B C D : Obj} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} →
    ((h ∘ g) ∘ f) ≈ (h ∘ (g ∘ f))
  eg2 = auto-assoc 10

  eg3 : ∀ {A B C D E F G H I J K L M N : Obj} {a : A ⇒ B} {b : B ⇒ C} {c : C ⇒ D} {d : D ⇒ E} {e : E ⇒ F} {f : F ⇒ G} {g : G ⇒ H} {h : H ⇒ I} {i : I ⇒ J} {j : J ⇒ K} {k : K ⇒ L} {l : L ⇒ M} {m : M ⇒ N} →
    m ∘ l ∘ ((k ∘ j) ∘ (i ∘ h)) ∘ (g ∘ f) ∘ (e ∘ d) ∘ c ∘ b ∘ a ≈
    m ∘ (l ∘ k ∘ j ∘ i ∘ h) ∘ (g ∘ f) ∘ e ∘ (d ∘ c) ∘ b ∘ a
  eg3 =  auto-assoc 50

  eg4 : ∀ {A B C D E F G H I J K L M N : Obj} {a : A ⇒ B} {b : B ⇒ C} {c : C ⇒ D} {d : D ⇒ E} {e : E ⇒ F} {f : F ⇒ G} {g : G ⇒ H} {h : H ⇒ I} {i : I ⇒ J} {j : J ⇒ K} {k : K ⇒ L} {l : L ⇒ M} {m : M ⇒ N} →
    (m ∘ l) ∘ (k ∘ j ∘ i ∘ h ∘ g) ∘ f ∘ (e ∘ d ∘ c) ∘ b ∘ a ≈
    m ∘ (l ∘ k) ∘ (j ∘ i ∘ h) ∘ ((((g ∘ f) ∘ e) ∘ d) ∘ c) ∘ b ∘ a
  eg4 = auto-assoc 50
 

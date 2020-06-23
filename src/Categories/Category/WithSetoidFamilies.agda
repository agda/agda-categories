{-# OPTIONS --without-K --safe #-}
module Categories.Category.WithSetoidFamilies where

-- Category With Families (as model of dependent type theory)
-- see https://ncatlab.org/nlab/show/categorical+model+of+dependent+types#categories_with_families
-- for more details.  Actually, Dybjer's paper "Internal Type Theory" is really the one to
-- use.

open import Level
open import Function.Equality using (_⟨$⟩_)
open import Relation.Binary using (Setoid)

open import Categories.Category.Core using (Category)
open import Categories.Functor
-- open import Categories.NaturalTransformation.NaturalIsomorphism hiding
open import Categories.Object.Terminal

open import Categories.Category.Instance.FamilyOfSetoids
open import Categories.Functor.Presheaf
open import Categories.Category.Slice
open import Categories.Category.Instance.Sets

private
  variable
    o ℓ e a b c d : Level
-- We want to re-interpret the members of C as
-- the various parts of a type theory -- Context, types, terms, etc.
module UnpackFam {C : Category o ℓ e}
                 (T : Presheaf C (FamilyOfSetoids a b c d)) where
  private
    module C = Category C
    module T = Functor T

  open Setoid using () renaming (Carrier to ∣_∣ )
  -- A context is still just a type
  Context : Set o
  Context = C.Obj

  -- but a type is an indexed Setoid
  TyS : C.Obj → Setoid a b
  TyS Γ = Fam.U (T.F₀ Γ)

  Ty : C.Obj → Set a
  Ty Γ = ∣ TyS Γ ∣

  -- remember that context morphisms are substitutions
  infix 4 _⇛_
  _⇛_ : (Γ Δ : Context) → Set ℓ
  _⇛_ = C._⇒_

  -- which are here applied postfix
  infixr 10 _[_]
  _[_] : ∀ {Γ Δ} → (T : Ty Γ) → Δ ⇛ Γ → Ty Δ
  _[_] T σ = Hom.map (T.F₁ σ) ⟨$⟩ T

  TmS : (Γ : Context) → Ty Γ → Setoid c d
  TmS Γ = Fam.T (T.F₀ Γ)

  Tm : (Γ : Context) → Ty Γ → Set c
  Tm Γ t = ∣ TmS Γ t ∣

  -- substitute into a term
  _[_⁺] : {Γ Δ : Context} {tp : Ty Γ} → (term : Tm Γ tp ) → (σ : Δ ⇛ Γ) → Tm Δ (tp [ σ ])
  _[_⁺] term σ = Hom.transport (T.F₁ σ) _ ⟨$⟩ term

  -- type equality
  infix 4 _Ty≈_
  _Ty≈_ : {Γ : Context} → (t₁ t₂ : Ty Γ) → Set b
  _Ty≈_ {Γ} t₁ t₂ = Setoid._≈_ (TyS Γ) t₁ t₂

  -- Use that T is a Functor to create type equalities
  [-∘-]⇒[-][-] : {Γ₁ Γ₂ Γ₃ : Context} (f : Γ₂ ⇛ Γ₃) → (g : Γ₁ ⇛ Γ₂) → {x : Ty Γ₃} →
    x [ f C.∘ g ] Ty≈ x [ f ] [ g ]
  [-∘-]⇒[-][-] f g {x} = _≈≈_.g≈f (T.homomorphism {f = f} {g}) {x}

  A[id]⇒A : {Γ : Context} {A : Ty Γ} → A [ C.id ] Ty≈ A
  A[id]⇒A = _≈≈_.g≈f T.identity

  ∘-pres-Ty≈ : {Γ₁ Γ₂ : Context} {f g : Γ₁ ⇛ Γ₂} {A : Ty Γ₂} → f C.≈ g →  A [ f ] Ty≈ A [ g ]
  ∘-pres-Ty≈ eq = _≈≈_.g≈f (T.F-resp-≈ eq)

  -- Coerce a term from one type to another via an equality
  coe : {Γ : Context} {t₁ t₂ : Ty Γ} → t₁ Ty≈ t₂ → Tm Γ t₂ → Tm Γ t₁
  coe {Γ} eq x = Fam.reindex (T.F₀ Γ) eq ⟨$⟩ x

  -- term equality
  infix 4 _Tm≈_
  _Tm≈_ : {Γ : Context} {t : Ty Γ} (tm₁ tm₂ : Tm Γ t) → Set d
  _Tm≈_ {Γ} {t} tm₁ tm₂ = Setoid._≈_ (TmS Γ t) tm₁ tm₂

-- This is the original definition from Dybjer. The one from nLab is too tricky to do quite yet.
record CwF : Set (suc (o ⊔ ℓ ⊔ e ⊔ a ⊔ b ⊔ c ⊔ d)) where
  field
    C : Category o ℓ e
    T : Presheaf C (FamilyOfSetoids a b c d)
    Empty : Terminal C

  infix 5 _⟫_
  infix 3 <_,_>

  module C = Category C
  module T = Functor T
  open UnpackFam T
  module Empty = Terminal Empty

  field
    -- context snoc
    _⟫_ : (Γ : Context) → Ty Γ → Context

    -- projections
    p : {Γ : Context} {A : Ty Γ} → (Γ ⟫ A) ⇛ Γ
    q : {Γ : Context} {A : Ty Γ} → Tm (Γ ⟫ A) (A [ p ])

    -- constructor
    <_,_> : {Γ Δ : Context} {A : Ty Γ} → (γ : Δ ⇛ Γ) (a : Tm Δ (A [ γ ])) → Δ ⇛ (Γ ⟫ A)

  -- This is not quite q [ γ ⁺], but rather a coerced version.
  q[_] : {Γ Δ : Context} {A : Ty Γ}  → (γ : Δ ⇛ Γ) -> Tm (Δ ⟫ A [ γ ]) (A [ γ C.∘ p ])
  q[_] {Γ} {Δ} {A} γ = coe ([-∘-]⇒[-][-] γ p) q

  field
    p∘<γ,a>≡γ    : ∀ {Γ A} → ∀ {Δ} {γ : Δ ⇛ Γ} {a : Tm Δ (A [ γ ])} → p C.∘ < γ , a > C.≈ γ

  _at_ : ∀ {Γ A} → ∀ {Δ} {γ : Δ C.⇒ Γ} {δ : Δ C.⇒ (Γ ⟫ A)} (a : Tm Δ (A [ γ ])) (pδ≈γ : p C.∘ δ C.≈ γ) →
           Tm Δ (A [ p ] [ δ ])
  _at_ {Γ} {A} {Δ} {γ} {δ} a pδ≈γ = let open Setoid (TyS Δ) in
    coe (trans (sym ([-∘-]⇒[-][-] p δ)) (∘-pres-Ty≈ pδ≈γ)) a

  field
    q[<γ,a>]≡a   : ∀ {Γ A} → ∀ {Δ} {γ : Δ C.⇒ Γ} {a : Tm Δ (A [ γ ])} →
      q [ < γ , a > ⁺] Tm≈ a at p∘<γ,a>≡γ

    <γ,a>-unique : {Γ Δ : Context} {A : Ty Γ} {γ : Δ ⇛ Γ} {a : Tm Δ (A [ γ ])} →
                      (δ : Δ ⇛ (Γ ⟫ A)) → (pδ≈γ : p C.∘ δ C.≈ γ) → ( q [ δ ⁺] Tm≈ (a at pδ≈γ)) → δ C.≈ < γ , a >

  _[id] : ∀ {Γ A} -> Tm Γ A -> Tm Γ (A [ C.id ])
  _[id] {Γ} {A} x = Fam.reindex (T.F₀ Γ) A[id]⇒A ⟨$⟩ x

  open UnpackFam T public
  open Empty public using () renaming (⊤ to <>)

-- Not all the laws are here: the coecions involve are non-trivial and should be done
-- in the above, as they are Π independent
record Pi {o ℓ e a b c d} (Cwf : CwF {o} {ℓ} {e} {a} {b} {c} {d}) : Set (o ⊔ ℓ ⊔ a ⊔ b ⊔ c ⊔ d) where
  open CwF Cwf
  field
    Π : ∀ {Γ} -> (A : Ty Γ) (B : Ty (Γ ⟫ A)) -> Ty Γ
    lam : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ⟫ A)} -> (b : Tm (Γ ⟫ A) B) -> Tm Γ (Π A B)
    _$_ : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ⟫ A)} ->
            (f : Tm Γ (Π A B)) (x : Tm Γ A) -> Tm Γ (B [ < C.id , x [id] > ])

    -- naturality laws
    Π-nat   : ∀ {Γ} -> (A : Ty Γ) (B : Ty (Γ ⟫ A)) -> ∀ {Δ} (γ : Δ ⇛ Γ)
                     -> Π A B [ γ ] Ty≈ Π (A [ γ ]) (B [ < (γ C.∘ p) , q[ γ ] > ])
    -- lam-nat relies on Π-nat for a coercions
    lam-nat : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ⟫ A)} -> (b : Tm (Γ ⟫ A) B) -> ∀ {Δ} (γ : Δ ⇛ Γ)
                     -> (lam b [ γ ⁺]) Tm≈
                     coe (Π-nat A B γ) (lam {A = A [ γ ]} (b [ < γ C.∘ p , q[ γ ] > ⁺]))

    -- app-nat : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ⟫ A)} -> (f : Tm Γ (Π A B)) (x : Tm Γ A) -> ∀ {Δ} (γ : Δ ⇛ Γ)
    --                  -> (f $ x) [ γ ⁺] Tm≈  coe {!!} ((coe (Setoid.sym (TyS Δ) (Π-nat A B γ)) (f [ γ ⁺])) $ (x [ γ ⁺]))

    -- proofs of the lam/_$_ isomorphism
    β : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ⟫ A)} -> (b : Tm (Γ ⟫ A) B) (x : Tm Γ A)
           -> (lam b $ x) Tm≈ b [ < C.id , x [id] > ⁺]

    -- η : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ⟫ A)} -> (f : Tm Γ (Π A B))
    --        -> lam ( coe (Setoid.sym (TyS (Γ ⟫ A)) (Π-nat A B p)) (f [ p ⁺]) $ q ) Tm≈ coe {!!} f

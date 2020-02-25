{-# OPTIONS --without-K --safe #-}
module Categories.Category.WithFamilies where

-- Category With Families (as model of dependent type theory)
-- see https://ncatlab.org/nlab/show/categorical+model+of+dependent+types#categories_with_families
-- for more details.

open import Level
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation.NaturalIsomorphism
open import Categories.Object.Terminal

open import Categories.Category.Instance.FamilyOfSets
open import Categories.Functor.Presheaf
open import Categories.Category.Slice
open import Categories.Category.Instance.Sets

private
  variable
    o ℓ e a b : Level
-- We want to re-interpret the members of C as
-- the various parts of a type theory -- Context, types, terms, etc.
module UnpackFam {C : Category o ℓ e}
                 (T : Presheaf C (FamilyOfSets a b)) where
  private
    module C = Category C
    module T = Functor T

  Context : Set o
  Context = C.Obj

  Ty : C.Obj → Set a
  Ty Γ = Fam.U (T.F₀ Γ)

  -- remember that context morphisms are substitutions
  -- which are here applied postfix
  _[_] : ∀ {Γ Δ} → (T : Ty Γ) → (σ : Δ C.⇒ Γ) → Ty Δ
  _[_] T σ = Hom.f (T.F₁ σ) T

  Tm : ∀ Γ → Ty Γ → Set b
  Tm Γ = Fam.T (T.F₀ Γ)

  -- substitute into a term
  _[_⁺] : {Γ Δ : Context} {tp : Ty Γ} → (term : Tm Γ tp) → (σ : Δ C.⇒ Γ) → Tm Δ (tp [ σ ])
  _[_⁺] term σ = Hom.φ (T.F₁ σ) _ term

-- This is the original definition from Dybjer. The one from nLab is too tricky to do quite yet.
record CwF : Set (suc (o ⊔ ℓ ⊔ e ⊔ a ⊔ b)) where
  field
    C : Category o ℓ e
    T : Presheaf C (FamilyOfSets a b)
    Empty : Terminal C

  infix 5 _>_

  module C = Category C
  module T = Functor T
  open UnpackFam T
  module Empty = Terminal Empty


  field
    -- context snoc
    _>_ : ∀ Γ → Ty Γ → Context
    -- projections
    p : ∀ {Γ A} → (Γ > A) C.⇒ Γ
    v : ∀ {Γ A} → Tm (Γ > A) (A [ p ])
    -- constructor
    <_,_>         : ∀ {Γ A} → ∀ {Δ} (γ : Δ C.⇒ Γ) (a : Tm Δ (A [ γ ])) → Δ C.⇒ (Γ > A)

  v[_] : ∀ {Γ A Δ} → (γ : Δ C.⇒ Γ) -> Tm (Δ > A [ γ ]) (A [ γ C.∘ p ])
  v[_] {Γ} {A} {Δ} γ = ≡.subst (Tm (Δ > A [ γ ])) (Eq.g≡f (T.homomorphism {Γ})) v


  -- Note that the original used Heterogenenous equality (yuck). So here we use
  -- explicit transport. Explicit yuck.
  field
    p∘<γ,a>≡γ    : ∀ {Γ A} → ∀ {Δ} {γ : Δ C.⇒ Γ} {a : Tm Δ (A [ γ ])} → p C.∘ < γ , a > C.≈ γ

  patch : ∀ {Γ A} → ∀ {Δ} {γ : Δ C.⇒ Γ} {δ : Δ C.⇒ (Γ > A)} (a : Tm Δ (A [ γ ])) (pδ≈γ : p C.∘ δ C.≈ γ)
          → Fam.T (T.F₀ Δ) ((A [ p ]) [ δ ])
  patch {Γ} {A} {Δ} {γ} a pδ≈γ = ≡.subst (Fam.T (T.F₀ Δ)) (≡.trans (Eq.g≡f (T.F-resp-≈ pδ≈γ)) (≡.sym (Eq.g≡f (T.homomorphism {Γ})))) a
  field
    v[<γ,a>]≡a   : ∀ {Γ A} → ∀ {Δ} {γ : Δ C.⇒ Γ} {a : Tm Δ (A [ γ ])} → v [ < γ , a > ⁺] ≡  patch a p∘<γ,a>≡γ
    <γ,a>-unique : ∀ {Γ A} → ∀ {Δ} {γ : Δ C.⇒ Γ} {a : Tm Δ (A [ γ ])} →
                      (δ : Δ C.⇒ (Γ > A)) → (pδ≈γ : p C.∘ δ C.≈ γ) → ( v [ δ ⁺] ≡ patch a pδ≈γ) → δ C.≈ < γ , a >

  _[id] : ∀ {Γ A} -> Tm Γ A -> Tm Γ (A [ C.id ])
  _[id] {Γ} {A} x = ≡.subst (Tm Γ) (Eq.g≡f (T.identity {Γ}) {A}) x

  open UnpackFam T public
  open Empty public using () renaming (⊤ to <>)

-- inside a CwF, we can sort-of 'define' a λ-calculus with Π, but the results are way too
-- heterogeneous to contemplate...
{-
record Pi {o ℓ e a b} (Cwf : CwF {o} {ℓ} {e} {a} {b}) : Set (o ⊔ ℓ ⊔ a ⊔ b) where
  open CwF Cwf
  field
    Π : ∀ {Γ} -> (A : Ty Γ) (B : Ty (Γ > A)) -> Ty Γ
    lam : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ > A)} -> (b : Tm (Γ > A) B) -> Tm Γ (Π A B)
    _$_ : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ > A)} ->
            (f : Tm Γ (Π A B)) (x : Tm Γ A) -> Tm Γ (B [ < C.id , x [id] > ])

    -- naturality laws
    Π-nat   : ∀ {Γ} -> (A : Ty Γ) (B : Ty (Γ > A)) -> ∀ {Δ} (γ : Δ C.⇒ Γ)
                     -> Π A B [ γ ] ≡ Π (A [ γ ]) (B [ < (γ C.∘ p) , v[ γ ] > ])
    lam-nat : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ > A)} -> (b : Tm (Γ > A) B) -> ∀ {Δ} (γ : Δ C.⇒ Γ)
                     -> lam b [ γ ⁺] ≡ {! lam {A = A [ γ ]} (b [ < γ C.∘ p , v[ γ ] > ⁺]) !}
    app-nat : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ > A)} -> (f : Tm Γ (Π A B)) (x : Tm Γ A) -> ∀ {Δ} (γ : Δ C.⇒ Γ)
                     -> (f $ x) [ γ ⁺] ≡ {! ≡.subst (Tm Δ) (Π-nat A B γ) (f [ γ ⁺]) $ (x [ γ ⁺]) !}

    -- proofs of the lam/_$_ isomorphism
    β : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ > A)} -> (b : Tm (Γ > A) B) (x : Tm Γ A)
           -> (lam b $ x) ≡ b [ < C.id , x [id] > ⁺]

    η : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ > A)} -> (f : Tm Γ (Π A B))
           -> lam (≡.subst (Tm (Γ > A)) (Π-nat A B p) (f [ p ⁺]) $ v) ≡ {! f !}
-}

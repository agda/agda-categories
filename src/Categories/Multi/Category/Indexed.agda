{-# OPTIONS --without-K --safe #-}

-- Multicategories but over an 'index' type, rather than forcing Fin n
module Categories.Multi.Category.Indexed where

open import Level
open import Data.Fin.Base using (Fin)
open import Data.Product using (Σ; uncurry; curry; _×_; _,_; proj₁; proj₂)
open import Data.Product.Properties
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec.Functional
open import Function.Base using (const) renaming (_∘_ to _●_; id to id→)
open import Function.Equality using (_⟨$⟩_)
-- note how this is Function.Inverse instead of the one from Function.
open import Function.Inverse as Inv renaming (id to id↔; _∘_ to trans)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- any point can be lifted to a function from ⊤
pointed : {s t : Level} {S : Set s} (x : S) → ⊤ {t} → S
pointed x _ = x

-- the standard library doesn't seem to have the 'right' version of these.
⊤×K↔K : {t k : Level} {K : Set k} → (⊤ {t} × K) ↔ K
⊤×K↔K = inverse proj₂ (tt ,_) (λ _ → refl) λ _ → refl

K×⊤↔K : {t k : Level} {K : Set k} → (K × ⊤ {t}) ↔ K
K×⊤↔K = inverse proj₁ (_, tt) (λ _ → refl) λ _ → refl

⊤×⊤↔⊤ : {t : Level} → (⊤ {t} × ⊤) ↔ ⊤
⊤×⊤↔⊤ = inverse proj₁ (λ x → x , x) (λ _ → refl) λ _ → refl

Σ-assoc : {a b c : Level} {I : Set a} {J : I → Set b} {K : Σ I J → Set c} →
  Σ (Σ I J) K ↔ Σ I (λ i → Σ (J i) (curry K i))
Σ-assoc {I = I} {J} {K} = inverse g f (λ _ → refl) λ _ → refl
  where
  f : Σ I (λ i → Σ (J i) (λ j → K (i , j))) → Σ (Σ I J) K
  f (i , j , k) = (i , j) , k
  g : Σ (Σ I J) K → Σ I (λ i → Σ (J i) (λ j → K (i , j)))
  g ((i , j) , k) = i , j , k

-- the ı level is for the 'index' (and to not steal 'i')

-- The important part is that in _∘_, there is no flattening of the
-- index set. But also _≈[_]_ builds in an explicit equivalence
-- that allows one to properly re-index things. The classical view
-- of MultiCategory sweeps all of that under the rug, which gives
-- Agda conniptions (and rightfully so). The advantage of doing it
-- this way makes it clear that the 3 laws are based on the underlying
-- 3 laws that hold for (dependent!) product.

-- The upshot is that this version of MultiCategory makes no finiteness
-- assumption whatsoever.  The index sets involved could be huge,
-- without any issues.

-- Note that this still isn't Symmetric Multicategory. The renaming that
-- happens on indices say nothing about the relation to the contents
-- of the other Hom set.
record MultiCategory (o ℓ e ı : Level) : Set (suc (o ⊔ ℓ ⊔ e ⊔ ı)) where
  infix  4 _≈[_]_
  infixr 9 _∘_

  field
    Obj : Set o
    Hom : {I : Set ı} → (I → Obj) → Obj → Set ℓ
    id : (o : Obj) → Hom {⊤} (pointed o) o
    _∘_ : {I : Set ı} {aₙ : I → Obj} {a : Obj} {J : I → Set ı}
          {v : (i : I) → J i → Obj} →
          Hom {I} aₙ a → ((i : I) → Hom (v i) (aₙ i)) → Hom {Σ I J} (uncurry v) a
    _≈[_]_ : {I J : Set ı} {aₙ : I → Obj} {a : Obj} →
          Hom {I} aₙ a → (σ : I ↔ J) → Hom {J} (aₙ ● ( Inverse.from σ ⟨$⟩_ )) a → Set e

    identityˡ : {K : Set ı} {aₖ : K → Obj} {a : Obj} {f : Hom aₖ a} →
              id a ∘ pointed f ≈[ ⊤×K↔K ]  f
    identityʳ : {K : Set ı} {aₖ : K → Obj} {a : Obj} {f : Hom aₖ a} →
              f ∘ (id ● aₖ) ≈[ K×⊤↔K ] f

    identity² : {a : Obj} → id a ∘ pointed (id a) ≈[ ⊤×⊤↔⊤ ] id a

    assoc : -- the 3 index sets
            {I : Set ı} {J : I → Set ı} {K : Σ I J → Set ı}
            -- the 4 (increasingly indexed) objects
            {a : Obj} {aᵢ : I → Obj}
            {aᵢⱼ : (i : I) → J i → Obj}
            {aᵢⱼₖ : (h : Σ I J) → K h → Obj}
            -- the 3 Homs
            {h : Hom aᵢ a}
            {g : (i : I) → Hom (aᵢⱼ i) (aᵢ i)}
            {f : (k : Σ I J) → Hom (aᵢⱼₖ k) (uncurry aᵢⱼ k)} →
            -- and their relation under composition
            (h ∘ g) ∘ f ≈[ Σ-assoc ] h ∘ (λ i → g i ∘ curry f i)

    -- we also need that _≈[_]_ is, in an appropriate sense, an equivalence relation, which in this case
    -- means that _≈[ id↔ ]_ is.  In other words, we don't care when transport is over 'something else'.
    refl≈ : {I : Set ı} {aₙ : I → Obj} {a : Obj} →
            {h : Hom {I} aₙ a} → h ≈[ id↔ ] h
    sym≈ : {I : Set ı} {aₙ : I → Obj} {a : Obj} →
           {g h : Hom {I} aₙ a} → g ≈[ id↔ ] h → h ≈[ id↔ ] g
    trans≈ : {I : Set ı} {aₙ : I → Obj} {a : Obj} →
           {f g h : Hom {I} aₙ a} → f ≈[ id↔ ] g → g ≈[ id↔ ] h → f ≈[ id↔ ] h

    ∘-resp-≈ : {I : Set ı} {J : I → Set ı}
               {a : Obj} {aᵢ : I → Obj} {aᵢⱼ : (i : I) → J i → Obj}
               {g g′ : Hom aᵢ a} {f f′ : (i : I) → Hom (aᵢⱼ i) (aᵢ i)} →
               g ≈[ id↔ ] g′ → (∀ i → f i ≈[ id↔ ] f′ i) →
               g ∘ f ≈[ id↔ ] g′ ∘ f′

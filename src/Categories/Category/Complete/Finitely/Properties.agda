{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Complete.Finitely

module Categories.Category.Complete.Finitely.Properties {o ℓ e} {C : Category o ℓ e} (finite : FinitelyComplete C) where

open import Level using (Level)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; proj₁)
open import Data.Fin
open import Data.Fin.Properties
open import Data.List
open import Data.List.Relation.Unary.Any as Any using (here; there)
open import Data.List.Relation.Unary.Any.Properties
open import Data.List.Membership.Propositional
open import Relation.Binary.PropositionalEquality as ≡

open import Categories.Category
open import Categories.Category.Cartesian.Properties C
open import Categories.Category.Finite.Fin
open import Categories.Diagram.Equalizer C
open import Categories.Functor

import Categories.Category.Construction.Cones as Co
import Categories.Diagram.Limit as Lim

open FinitelyComplete finite

module GeneralProperties {a} {A : Set a} where

  tabulate-∈ : ∀ {n} (f : Fin n → A) → ∀ m → f m ∈ tabulate f
  tabulate-∈ {.(ℕ.suc _)} f Fin.zero    = here ≡.refl
  tabulate-∈ {.(ℕ.suc _)} f (Fin.suc m) = there (tabulate-∈ (λ x → f (suc x)) m)

  concatMap-∈ : ∀ {b} {B : Set b} (f : A → List B) {l : List A} →
                ∀ {x y} → x ∈ l → y ∈ f x → y ∈ concatMap f l
  concatMap-∈ f (here refl) y∈fx     = ++⁺ˡ y∈fx
  concatMap-∈ f (there {z} x∈l) y∈fx = ++⁺ʳ (f z) (concatMap-∈ f x∈l y∈fx)

open GeneralProperties
open Prods cartesian

-- construct a finite limit from cartesian products and equalizer
--
-- c.f. Awodey 5.21
module _ (shape : FinCatShape) (F : Functor (FinCategory shape) C) where
  private
    module C = Category C
    open C
    open HomReasoning
    S = FinCategory shape
    open Co F
    open Lim F
    open FinCatShape shape using (size; ∣_⇒_∣; objects; morphisms)
    module S = Category S
    module F = Functor F

    prods-gen : List (Fin size) → Obj
    prods-gen ns = prod (map F.₀ ns)

    prods : Obj
    prods = prods-gen objects

    cods : List Obj
    cods = map (λ n → F.₀ (Arrow.cod n)) morphisms

    arrs : Obj
    arrs = prod cods

    ∈-objects : ∀ n → n ∈ objects
    ∈-objects n = tabulate-∈ (λ x → x) n

    π : ∀ n → prods ⇒ F.₀ n
    π n = π[ map⁺ (Any.map (≡.cong F.₀) (∈-objects n)) ]

    ϕπ-rec : ∀ (ns : List (Arrow size ∣_⇒_∣)) → prods ⇒ map (λ n → F.₀ (Arrow.cod n)) ns *
    ϕπ-rec []       = prods ~[]
    ϕπ-rec (n ∷ ns) = π (Arrow.cod n) ∷ ϕπ-rec ns

    ϕπ : prods ⇒ cods *
    ϕπ = ϕπ-rec morphisms

    ϕ : prods ⇒ arrs
    ϕ = ⟨ ϕπ ⟩*

    ψπ-rec : ∀ (ns : List (Arrow size ∣_⇒_∣)) → prods ⇒ map (λ n → F.₀ (Arrow.cod n)) ns *
    ψπ-rec []       = prods ~[]
    ψπ-rec (n ∷ ns) = F.₁ (Arrow.arr n) ∘ π (Arrow.dom n) ∷ ψπ-rec ns

    ψπ : prods ⇒ cods *
    ψπ = ψπ-rec morphisms

    ψ : prods ⇒ arrs
    ψ = ⟨ ψπ ⟩*

    ∈-morphisms : ∀ {d c} (f : Fin ∣ d ⇒ c ∣) → record { arr = f } ∈ morphisms
    ∈-morphisms {d} {c} f = concatMap-∈ _ (∈-objects d) f∈d
      where arr : Arrow size ∣_⇒_∣
            arr = record { arr = f }
            f∈dc : arr ∈ tabulate {n = ∣ d ⇒ c ∣} λ arr → record { arr = arr }
            f∈dc = tabulate-∈ _ f
            f∈d : arr ∈ concatMap (λ c → tabulate {n = ∣ d ⇒ c ∣} (λ arr → record { arr = arr })) objects
            f∈d = concatMap-∈ _ (∈-objects c) f∈dc

    Fc∈cods : ∀ {d c} (f : Fin ∣ d ⇒ c ∣) → F.₀ c ∈ cods
    Fc∈cods f = map⁺ (Any.map (cong (λ n → F.₀ (Arrow.cod n))) (∈-morphisms f))

    π′ : ∀ {d c} (f : Fin ∣ d ⇒ c ∣) → arrs ⇒ F.₀ c
    π′ f = π[ Fc∈cods f ]

    e⇒prods : Equalizer ψ ϕ
    e⇒prods = equalizer ψ ϕ

    module e⇒prods = Equalizer e⇒prods

    open e⇒prods

    -- ⊤cone : Cone
    -- ⊤cone = record
    --   { N    = obj
    --   ; apex = record
    --     { ψ       = λ n → π n ∘ arr
    --     ; commute = λ {m n} f → begin
    --       F.₁ f ∘ π m ∘ arr ≈⟨ {!project* ψπ (Fc∈cods f)!} ⟩
    --       {!!} ≈⟨ {!!} ⟩
    --       {!!} ≈⟨ {!!} ⟩
    --       π n ∘ arr ∎
    --     }
    --   }

  -- -- finiteLimit : Limit
  -- -- finiteLimit = record
  -- --   { terminal = record
  -- --     { ⊤        = {!obj!}
  -- --     ; !        = {!!}
  -- --     ; !-unique = {!!}
  -- --     }
  -- --   }

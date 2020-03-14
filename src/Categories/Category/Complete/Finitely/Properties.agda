{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Complete.Finitely

module Categories.Category.Complete.Finitely.Properties {o ℓ e} {C : Category o ℓ e} (finite : FinitelyComplete C) where

open import Level using (Level)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; proj₁; ∃₂) renaming (_×_ to _&_)
open import Data.Fin
open import Data.Fin.Properties
open import Data.Sum using (inj₁; inj₂)
open import Data.List
open import Data.List.Relation.Unary.Any as Any using (here; there)
open import Data.List.Relation.Unary.Any.Properties
open import Data.List.Membership.Propositional
open import Relation.Binary.PropositionalEquality as ≡
open import Function renaming (_∘_ to _∙_)

open import Categories.Category
open import Categories.Category.Cartesian.Properties C
open import Categories.Category.Finite.Fin
open import Categories.Diagram.Equalizer C
open import Categories.Morphism.Reasoning C
open import Categories.Functor

import Categories.Category.Construction.Cones as Co
import Categories.Diagram.Limit as Lim

open FinitelyComplete finite

module GeneralProperties where

  module _ {a} {A : Set a} where
  
    tabulate-∈ : ∀ {n} (f : Fin n → A) → ∀ m → f m ∈ tabulate f
    tabulate-∈ {.(ℕ.suc _)} f Fin.zero    = here ≡.refl
    tabulate-∈ {.(ℕ.suc _)} f (Fin.suc m) = there (tabulate-∈ (λ x → f (suc x)) m)

    tabulate-∈⁻¹ : ∀ {n} (f : Fin n → A) → ∀ {fm} → fm ∈ tabulate f → Σ (Fin n) (λ m → fm ≡ f m)
    tabulate-∈⁻¹ {ℕ.suc n} f (here px) = zero , px
    tabulate-∈⁻¹ {ℕ.suc n} f (there fm∈) with tabulate-∈⁻¹ (f ∙ suc) fm∈
    ... | m , eq                       = suc m , eq

    concatMap-∈ : ∀ {b} {B : Set b} (f : A → List B) {l : List A} →
                  ∀ {x y} → x ∈ l → y ∈ f x → y ∈ concatMap f l
    concatMap-∈ f (here refl) y∈fx     = ++⁺ˡ y∈fx
    concatMap-∈ f (there {z} x∈l) y∈fx = ++⁺ʳ (f z) (concatMap-∈ f x∈l y∈fx)

    concatMap-∈⁻¹ : ∀ {b} {B : Set b} (f : A → List B) (l : List A) →
                      ∀ {y} → y ∈ concatMap f l → Σ A (λ x → x ∈ l & y ∈ f x)
    concatMap-∈⁻¹ f (a ∷ l) y∈ with ++⁻ (f a) y∈
    ... | inj₁ y∈fa = a , here refl , y∈fa
    ... | inj₂ y∈fl with concatMap-∈⁻¹ f l y∈fl
    ... | x , x∈l , y∈fx = x , there x∈l , y∈fx

    module _ {b} {B : Set b} (f : A → B) where

      map⁺⁻¹ : ∀ {x l} (x∈fl : x ∈ map f l) → Σ A (λ a → a ∈ l & x ≡ f a)
      map⁺⁻¹ {x} {a ∷ l} (here px) = a , here ≡.refl , px
      map⁺⁻¹ {x} {b ∷ l} (there x∈fl) with map⁺⁻¹ x∈fl
      ... | a , a∈l , eq           = a , there a∈l , eq

  module _ {a} {A : Set a} where

    concatMap²-∈ : ∀ {m n} {ms : List (Fin m)} {ns : List (Fin n)}
                     (f : Fin m → Fin n → List A) →
                     ∀ {x y k} → x ∈ ms → y ∈ ns → k ∈ f x y →
                       k ∈ concatMap (λ z → concatMap (λ w → f z w) ns) ms
    concatMap²-∈ {m} {n} {ms} {ns} f {x} {y} {k} x∈ms y∈ns k∈fxy = concatMap-∈ _ x∈ms k∈ns
      where k∈ns : k ∈ concatMap (λ w → f x w) ns
            k∈ns  = concatMap-∈ _ y∈ns k∈fxy

    concatMap²-∈⁻¹ : ∀ {m n} (ms : List (Fin m)) (ns : List (Fin n))
                       (f : Fin m → Fin n → List A) →
                       ∀ {k} → k ∈ concatMap (λ z → concatMap (λ w → f z w) ns) ms →
                       ∃₂ (λ x y → x ∈ ms & y ∈ ns & k ∈ f x y)
    concatMap²-∈⁻¹ {m} {n} ms ns f {k} k∈ = x , y , x∈ms , y∈ns , k∈xy
      where tup₁ = concatMap-∈⁻¹ (λ z → concatMap (λ w → f z w) ns) ms k∈
            x    : Fin m
            x    = let x , x∈ms , k∈x = tup₁ in x
            x∈ms : x ∈ ms
            x∈ms = let x , x∈ms , k∈x = tup₁ in x∈ms
            k∈x  : k ∈ concatMap (f x) ns
            k∈x  = let x , x∈ms , k∈x = tup₁ in k∈x
            tup₂ = concatMap-∈⁻¹ (f x) ns k∈x
            y : Fin n
            y = let y , y∈ns , k∈xy = tup₂ in y
            y∈ns : y ∈ ns
            y∈ns = let y , y∈ns , k∈xy = tup₂ in y∈ns
            k∈xy : k ∈ f x y
            k∈xy = let y , y∈ns , k∈xy = tup₂ in k∈xy

    module _ {b} {B : Set b} where

      concatMap²-map-∈ : ∀ {m n} {ms : List (Fin m)} {ns : List (Fin n)}
                           (f : Fin m → Fin n → List A) →
                           (g : A → B) →
                           ∀ {x y k} → x ∈ ms → y ∈ ns → k ∈ f x y →
                             g k ∈ map g (concatMap (λ z → concatMap (λ w → f z w) ns) ms)
      concatMap²-map-∈ f g x∈ms y∈ns k∈fxy = map⁺ (Any.map (cong g) (concatMap²-∈ f x∈ms y∈ns k∈fxy))

      concatMap²-map-∈⁻¹ : ∀ {m n} (ms : List (Fin m)) (ns : List (Fin n))
                             (f : Fin m → Fin n → List A) →
                             (g : A → B) →
                             ∀ {gk} → gk ∈ map g (concatMap (λ z → concatMap (λ w → f z w) ns) ms) →
                             ∃₂ λ x y → Σ A λ k → gk ≡ g k & x ∈ ms & y ∈ ns & k ∈ f x y
      concatMap²-map-∈⁻¹ ms ns f g gk∈ with map⁺⁻¹ g gk∈
      ... | k , k∈c , keq with concatMap²-∈⁻¹ ms ns f k∈c
      ... | x , y , x∈ms , y∈ns , k∈fxy = x , y , k , keq , x∈ms , y∈ns , k∈fxy

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
    open FinCatShape shape using (size; ∣_⇒_∣; objects; morphisms; wrap-arr)
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

    Fn∈obj : ∀ n → F.₀ n ∈ map F.₀ objects
    Fn∈obj n = f∈fl F.₀ (∈-objects n)

    π : ∀ n → prods ⇒ F.₀ n
    π n = π[ Fn∈obj n ]

    ϕπ : prods ⇒ cods *
    ϕπ = build-mors (λ a → F.₀ (Arrow.cod a)) (λ a → π (Arrow.cod a)) morphisms

    ϕ : prods ⇒ arrs
    ϕ = ⟨ ϕπ ⟩*

    ψπ : prods ⇒ cods *
    ψπ = build-mors (λ a → F.₀ (Arrow.cod a))
                    (λ a → F.₁ (Arrow.arr a) ∘ π (Arrow.dom a))
                    morphisms

    ψ : prods ⇒ arrs
    ψ = ⟨ ψπ ⟩*

    ∈-morphisms : ∀ {d c} (f : Fin ∣ d ⇒ c ∣) → record { arr = f } ∈ morphisms
    ∈-morphisms {d} {c} f = concatMap²-∈ (λ _ _ → tabulate wrap-arr) (∈-objects d) (∈-objects c) (tabulate-∈ _ f)

    Fc∈cods : ∀ {d c} (f : Fin ∣ d ⇒ c ∣) → F.₀ c ∈ cods
    Fc∈cods f = f∈fl (λ a → F.₀ (Arrow.cod a)) (∈-morphisms f)

    π′ : ∀ {d c} (f : Fin ∣ d ⇒ c ∣) → arrs ⇒ F.₀ c
    π′ f = π[ Fc∈cods f ]

    ψπ-proj : ∀ {d c} (f : Fin ∣ d ⇒ c ∣) →
                F.₁ f ∘ π d ≈ π[ Fc∈cods f ] ∘ ψ
    ψπ-proj f = build-proj (λ a → F.₀ (Arrow.cod a))
                           (λ a → F.₁ (Arrow.arr a) ∘ π (Arrow.dom a))
                           (∈-morphisms f)

    ϕπ-proj : ∀ {d c} (f : Fin ∣ d ⇒ c ∣) →
                π c ≈ π[ Fc∈cods f ] ∘ ϕ
    ϕπ-proj f = build-proj (λ a → F.₀ (Arrow.cod a))
                           (λ a → π (Arrow.cod a))
                           (∈-morphisms f)

    e⇒prods : Equalizer ψ ϕ
    e⇒prods = equalizer ψ ϕ

    module e⇒prods = Equalizer e⇒prods

    open e⇒prods

    ⊤cone : Cone
    ⊤cone = record
      { N    = obj
      ; apex = record
        { ψ       = λ n → π n ∘ arr
        ; commute = λ {m n} f → begin
          F.₁ f ∘ π m ∘ arr ≈⟨ pullˡ (ψπ-proj f) ⟩
          (π′ f ∘ ψ) ∘ arr  ≈⟨ pullʳ equality ⟩
          π′ f ∘ ϕ ∘ arr    ≈˘⟨ pushˡ (ϕπ-proj f) ⟩
          π n ∘ arr         ∎
        }
      }

    module _ {K : Cone} where
      module K = Cone K

      N⇒* : K.N ⇒ map F.₀ objects *
      N⇒* = build-mors F.₀ K.ψ objects

      Kmor : K.N ⇒ prods
      Kmor = ⟨ N⇒* ⟩*

      π∘ψ∘Kmor : ∀ {d c} (f : Fin ∣ d ⇒ c ∣) →
                   π[ Fc∈cods f ] ∘ ψ ∘ Kmor ≈ F.₁ f ∘ K.ψ d
      π∘ψ∘Kmor {d} {c} f = begin
        π[ Fc∈cods f ] ∘ ψ ∘ Kmor ≈˘⟨ pushˡ (ψπ-proj f) ⟩
        (F.₁ f ∘ π d) ∘ Kmor      ≈˘⟨ pushʳ (build-proj F.₀ K.ψ (∈-objects d)) ⟩
        F.₁ f ∘ K.ψ d             ∎

      π∘ϕ∘Kmor : ∀ {d c} (f : Fin ∣ d ⇒ c ∣) →
                   π[ Fc∈cods f ] ∘ ϕ ∘ Kmor ≈ K.ψ c
      π∘ϕ∘Kmor {d} {c} f = begin
        π[ Fc∈cods f ] ∘ ϕ ∘ Kmor ≈˘⟨ pushˡ (ϕπ-proj f) ⟩
        π c ∘ Kmor ≈˘⟨ build-proj F.₀ K.ψ (∈-objects c) ⟩
        K.ψ c ∎

      -- Kmor-commute : ∀ {z} (z∈zs : z ∈ cods) →
      --                  π[ z∈zs ] ∘ ψ ∘ Kmor ≈ π[ z∈zs ] ∘ ϕ ∘ Kmor
      -- Kmor-commute {z} z∈zs with concatMap²-map-∈⁻¹ objects objects (λ d c → tabulate (wrap-arr {d} {c})) (λ a → F.₀ (Arrow.cod a)) z∈zs
      -- ... | x , y , a , eq , x∈ , y∈ , a∈ = {!commute (Arrow.arr a)!}
      --   where commute : ∀ {d c} (f : Fin ∣ d ⇒ c ∣) → π[ Fc∈cods f ] ∘ ψ ∘ Kmor ≈ π[ Fc∈cods f ] ∘ ϕ ∘ Kmor
      --         commute {d} {c} f = begin
      --           π[ Fc∈cods f ] ∘ ψ ∘ Kmor ≈⟨ π∘ψ∘Kmor f ⟩
      --           F.₁ f ∘ K.ψ d             ≈⟨ K.commute f ⟩
      --           K.ψ c                     ≈˘⟨ π∘ϕ∘Kmor f ⟩
      --           π[ Fc∈cods f ] ∘ ϕ ∘ Kmor ∎

      -- !cone : Cone⇒ K ⊤cone
      -- !cone = record
      --   { arr     = equalize (uniqueness* Kmor-commute)
      --   ; commute = {!K.commute!}
      --   }
  
  -- -- finiteLimit : Limit
  -- -- finiteLimit = record
  -- --   { terminal = record
  -- --     { ⊤        = ⊤cone
  -- --     ; !        = !cone _
  -- --     ; !-unique = {!!}
  -- --     }
  -- --   }

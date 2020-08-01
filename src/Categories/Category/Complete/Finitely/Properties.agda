{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Complete.Finitely

module Categories.Category.Complete.Finitely.Properties {o ℓ e} {C : Category o ℓ e} (finite : FinitelyComplete C) where

open import Level using (Level)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (Σ; _,_; proj₁; ∃₂) renaming (_×_ to _&_)
open import Data.Fin.Base using (Fin)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.List.Base hiding ([_])
open import Data.List.Relation.Unary.Any as Any using (here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ; map⁺)
open import Data.List.Relation.Unary.Unique.Propositional
open import Data.List.Membership.Propositional
open import Relation.Binary.PropositionalEquality as ≡ using (refl; _≡_; cong)
open import Function.Base renaming (_∘_ to _∙_)

import Data.List.Relation.Unary.Unique.Propositional.Properties as Uₚ
import Data.List.Membership.Propositional.Properties as ∈ₚ
import Data.List.Membership.Setoid.Properties as S∈ₚ

open import Categories.Category using (_[_,_]; _[_≈_])
open import Categories.Category.Cartesian.Properties C
open import Categories.Category.Finite.Fin
open import Categories.Diagram.Equalizer C
open import Categories.Morphism.Reasoning C
open import Categories.Functor.Core using (Functor)

import Categories.Category.Construction.Cones as Co
import Categories.Diagram.Limit as Lim

open FinitelyComplete finite

module GeneralProperties where

  module _ {a} {A : Set a} where

    concatMap-∈ : ∀ {b} {B : Set b} (f : A → List B) {l : List A} →
                  ∀ {x y} → x ∈ l → y ∈ f x → y ∈ concatMap f l
    concatMap-∈ f (here refl) y∈fx     = ++⁺ˡ y∈fx
    concatMap-∈ f (there {z} x∈l) y∈fx = ++⁺ʳ (f z) (concatMap-∈ f x∈l y∈fx)

  module _ {a} {A : Set a} where

    concatMap²-∈ : ∀ {m n} {ms : List (Fin m)} {ns : List (Fin n)}
                     (f : Fin m → Fin n → List A) →
                     ∀ {x y k} → x ∈ ms → y ∈ ns → k ∈ f x y →
                       k ∈ concatMap (λ z → concatMap (λ w → f z w) ns) ms
    concatMap²-∈ {m} {n} {ms} {ns} f {x} {y} {k} x∈ms y∈ns k∈fxy = concatMap-∈ _ x∈ms k∈ns
      where k∈ns : k ∈ concatMap (λ w → f x w) ns
            k∈ns  = concatMap-∈ _ y∈ns k∈fxy

    module _ {b} {B : Set b} where

      concatMap²-map-∈ : ∀ {m n} {ms : List (Fin m)} {ns : List (Fin n)}
                           (f : Fin m → Fin n → List A) →
                           (g : A → B) →
                           ∀ {x y k} → x ∈ ms → y ∈ ns → k ∈ f x y →
                             g k ∈ map g (concatMap (λ z → concatMap (λ w → f z w) ns) ms)
      concatMap²-map-∈ f g x∈ms y∈ns k∈fxy = map⁺ (Any.map (cong g) (concatMap²-∈ f x∈ms y∈ns k∈fxy))

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
    open FinCatShape shape using (size; ∣_⇒_∣; objects; morphisms; wrap-arr; Obj-UIP)
    module S = Category S
    module F = Functor F

    obj∈-irr : ∀ {x} → (p q : x ∈ objects) → p ≡ q
    obj∈-irr = S∈ₚ.unique⇒irrelevant (≡.setoid _) Obj-UIP (Uₚ.allFin⁺ size)

    prods-gen : List (Fin size) → Obj
    prods-gen ns = prod (map F.₀ ns)

    prods : Obj
    prods = prods-gen objects

    cods : List Obj
    cods = map (λ n → F.₀ (Arrow.cod n)) morphisms

    arrs : Obj
    arrs = prod cods

    ∈-objects : ∀ n → n ∈ objects
    ∈-objects n = ∈ₚ.∈-allFin n

    Fn∈obj : ∀ n → F.₀ n ∈ map F.₀ objects
    Fn∈obj n = ∈ₚ.∈-map⁺ F.₀ (∈-objects n)

    π : ∀ n → prods ⇒ F.₀ n
    π n = π[ Fn∈obj n ]

    ϕ⇒ : ∀ (a : Arrow size ∣_⇒_∣) → prods ⇒ F.F₀ (Arrow.cod a)
    ϕ⇒ a = π (Arrow.cod a)

    ϕπ : prods ⇒ cods *
    ϕπ = build-mors _ ϕ⇒ morphisms

    ϕ : prods ⇒ arrs
    ϕ = ⟨ ϕπ ⟩*

    ψ⇒ : ∀ a → prods ⇒ F.F₀ (Arrow.cod a)
    ψ⇒ a = F.₁ (Arrow.arr a) ∘ π (Arrow.dom a)

    ψπ : prods ⇒ cods *
    ψπ = build-mors _ ψ⇒ morphisms

    ψ : prods ⇒ arrs
    ψ = ⟨ ψπ ⟩*

    ∈-morphisms : ∀ {d c} (f : Fin ∣ d ⇒ c ∣) → record { arr = f } ∈ morphisms
    ∈-morphisms {d} {c} f = concatMap²-∈ (λ _ _ → tabulate wrap-arr) (∈-objects d) (∈-objects c) (∈ₚ.∈-tabulate⁺ f)

    Fc∈cods : ∀ {d c} (f : Fin ∣ d ⇒ c ∣) → F.₀ c ∈ cods
    Fc∈cods f = ∈ₚ.∈-map⁺ (λ a → F.₀ (Arrow.cod a)) (∈-morphisms f)

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
      private
        module K = Cone K

      N⇒* : K.N ⇒ map F.₀ objects *
      N⇒* = build-mors F.₀ K.ψ objects

      Kmor : K.N ⇒ prods
      Kmor = ⟨ N⇒* ⟩*

      ψ∘Kmor≈ϕ∘Kmor : ∀ a → ψ⇒ a ∘ Kmor ≈ ϕ⇒ a ∘ Kmor
      ψ∘Kmor≈ϕ∘Kmor a = begin
        ψ⇒ a ∘ Kmor                           ≈˘⟨ pushʳ (build-proj F.₀ K.ψ (∈-objects (Arrow.dom a))) ⟩
        F.₁ (Arrow.arr a) ∘ K.ψ (Arrow.dom a) ≈⟨ K.commute (Arrow.arr a) ⟩
        K.ψ (Arrow.cod a)                     ≈⟨ build-proj F.₀ K.ψ (∈-objects (Arrow.cod a)) ⟩
        ϕ⇒ a ∘ Kmor                           ∎

      equalize-eq : ψ ∘ Kmor ≈ ϕ ∘ Kmor
      equalize-eq = begin
        ψ ∘ Kmor                                        ≈⟨ build-⟨⟩*∘ _ ψ⇒ Kmor morphisms ⟩
        ⟨ build-mors _ (λ a → ψ⇒ a ∘ Kmor) morphisms ⟩* ≈⟨ build-uniqueness* _ ψ∘Kmor≈ϕ∘Kmor morphisms ⟩
        ⟨ build-mors _ (λ a → ϕ⇒ a ∘ Kmor) morphisms ⟩* ≈˘⟨ build-⟨⟩*∘ _ ϕ⇒ Kmor morphisms ⟩
        ϕ ∘ Kmor ∎

      !cone : Cone⇒ K ⊤cone
      !cone = record
        { arr     = equalize equalize-eq
        ; commute = commute _
        }
        where commute : ∀ n → (π n ∘ arr) ∘ equalize equalize-eq ≈ K.ψ n
              commute n = begin
                (π n ∘ arr) ∘ equalize equalize-eq ≈˘⟨ pushʳ universal ⟩
                π n ∘ Kmor                         ≈˘⟨ build-proj _ K.ψ (∈-objects n) ⟩
                K.ψ n                              ∎

    module _ {K : Cone} (f : Cones [ K , ⊤cone ]) where
      private
        module K = Cone K
        module f = Cone⇒ f

      !cone-unique : Cones [ !cone ≈ f ]
      !cone-unique = begin
        equalize equalize-eq ≈˘⟨ e⇒prods.unique eq ⟩
        f.arr                ∎
        where eq″ : ∀ y → π y ∘ arr ∘ f.arr ≈ π y ∘ Kmor {K}
              eq″ y = begin
                π y ∘ arr ∘ f.arr   ≈⟨ sym-assoc ⟩
                (π y ∘ arr) ∘ f.arr ≈⟨ f.commute ⟩
                K.ψ y               ≈⟨ build-proj _ K.ψ (∈-objects y) ⟩
                π y ∘ Kmor {K}      ∎

              eq′ : ∀ {y : Fin size} (y∈ys : y ∈ objects) →
                    π[ ∈ₚ.∈-map⁺ F.₀ y∈ys ] ∘ arr ∘ f.arr ≈ π[ ∈ₚ.∈-map⁺ F.₀ y∈ys ] ∘ Kmor {K}
              eq′ {y} y∈ys with obj∈-irr y∈ys (∈-objects y)
              ... | refl = eq″ y

              eq : Kmor {K} ≈ arr ∘ f.arr
              eq = ⟺ (uniqueness*′ F.₀ {K.N} {objects} eq′)

  finiteLimit : Limit
  finiteLimit = record
    { terminal = record
      { ⊤             = ⊤cone
      ; ⊤-is-terminal = record
        { !        = !cone
        ; !-unique = !cone-unique
        }
      }
    }

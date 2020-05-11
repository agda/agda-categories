{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Category.Cartesian.Properties {o ℓ e} (C : Category o ℓ e) where

open import Level using (_⊔_)
open import Function.Base using (_$_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁) renaming (_×_ to _&_)
open import Data.Product.Properties
open import Data.List as List
open import Data.List.Relation.Unary.Any as Any using (here; there)
open import Data.List.Relation.Unary.Any.Properties
open import Data.List.Membership.Propositional
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Unary.Any as AnyV using (here; there)
open import Data.Vec.Relation.Unary.Any.Properties
open import Data.Vec.Membership.Propositional renaming (_∈_ to _∈ᵥ_)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality as ≡ using (refl; _≡_)

import Data.List.Membership.Propositional.Properties as ∈ₚ
import Data.Vec.Membership.Propositional.Properties as ∈ᵥₚ

open import Categories.Category.Cartesian C

open import Categories.Diagram.Pullback C
open import Categories.Diagram.Equalizer C
open import Categories.Morphism.Reasoning C

private
  open Category C
  open HomReasoning
  open Equiv
  variable
    A B X Y : Obj
    f g : A ⇒ B

-- all binary products and pullbacks implies equalizers
module _ (prods : BinaryProducts) (pullbacks : ∀ {A B X} (f : A ⇒ X) (g : B ⇒ X) → Pullback f g) where
  open BinaryProducts prods
  open HomReasoning

  prods×pullbacks⇒equalizers : Equalizer f g
  prods×pullbacks⇒equalizers {f = f} {g = g} = record
    { arr       = pb′.p₁
    ; equality  = begin
      f ∘ pb′.p₁           ≈⟨ refl⟩∘⟨ helper₁ ⟩
      f ∘ pb.p₁ ∘ pb′.p₂   ≈⟨ pullˡ pb.commute ⟩
      (g ∘ pb.p₂) ∘ pb′.p₂ ≈˘⟨ pushʳ helper₂ ⟩
      g ∘ pb′.p₁           ∎
    ; equalize  = λ {_ i} eq → pb′.universal $ begin
      ⟨ id , id ⟩ ∘ i                                       ≈⟨ ⟨⟩∘ ⟩
      ⟨ id ∘ i , id ∘ i ⟩                                   ≈⟨ ⟨⟩-cong₂ identityˡ identityˡ ⟩
      ⟨ i ,  i ⟩                                            ≈˘⟨ ⟨⟩-cong₂ pb.p₁∘universal≈h₁ pb.p₂∘universal≈h₂ ⟩
      ⟨ pb.p₁ ∘ pb.universal eq , pb.p₂ ∘ pb.universal eq ⟩ ≈˘⟨ ⟨⟩∘ ⟩
      h ∘ pb.universal eq                                   ∎
    ; universal = ⟺ pb′.p₁∘universal≈h₁
    ; unique    = λ eq → pb′.unique (⟺ eq) (pb.unique (pullˡ (⟺ helper₁) ○ ⟺ eq) (pullˡ (⟺ helper₂) ○ ⟺ eq))
    }
    where pb : Pullback f g
          pb         = pullbacks _ _
          module pb  = Pullback pb
          h          = ⟨ pb.p₁ , pb.p₂ ⟩
          pb′ : Pullback ⟨ id , id ⟩ h
          pb′        = pullbacks _ _
          module pb′ = Pullback pb′
          helper₁ : pb′.p₁ ≈ pb.p₁ ∘ pb′.p₂
          helper₁    = begin
            pb′.p₁                    ≈˘⟨ cancelˡ project₁ ⟩
            π₁ ∘ ⟨ id , id ⟩ ∘ pb′.p₁ ≈⟨ refl⟩∘⟨ pb′.commute ⟩
            π₁ ∘ h ∘ pb′.p₂           ≈⟨ pullˡ project₁ ⟩
            pb.p₁ ∘ pb′.p₂            ∎
          helper₂ : pb′.p₁ ≈ pb.p₂ ∘ pb′.p₂
          helper₂    = begin
            pb′.p₁                    ≈˘⟨ cancelˡ project₂ ⟩
            π₂ ∘ ⟨ id , id ⟩ ∘ pb′.p₁ ≈⟨ refl⟩∘⟨ pb′.commute ⟩
            π₂ ∘ h ∘ pb′.p₂           ≈⟨ pullˡ project₂ ⟩
            pb.p₂ ∘ pb′.p₂            ∎


module Prods (car : Cartesian) where
  open Cartesian car

  -- for lists

  prod : List Obj → Obj
  prod objs = foldr _×_ ⊤ objs

  π[_] : ∀ {x xs} → x ∈ xs → prod xs ⇒ x
  π[ here refl ]  = π₁
  π[ there x∈xs ] = π[ x∈xs ] ∘ π₂

  data _⇒_* : Obj → List Obj → Set (o ⊔ ℓ) where
    _~[] : ∀ x → x ⇒ [] *
    _∷_  : ∀ {x y ys} → x ⇒ y → x ⇒ ys * → x ⇒ y ∷ ys *

  ⟨_⟩* : ∀ {x ys} (fs : x ⇒ ys *) → x ⇒ prod ys
  ⟨ x ~[] ⟩*  = !
  ⟨ f ∷ fs ⟩* = ⟨ f , ⟨ fs ⟩* ⟩

  ∈⇒mor : ∀ {x y ys} (fs : x ⇒ ys *) (y∈ys : y ∈ ys) → x ⇒ y
  ∈⇒mor (x ~[]) ()
  ∈⇒mor (f ∷ fs) (here refl)  = f
  ∈⇒mor (f ∷ fs) (there y∈ys) = ∈⇒mor fs y∈ys

  project* : ∀ {x y ys} (fs : x ⇒ ys *) (y∈ys : y ∈ ys) → π[ y∈ys ] ∘ ⟨ fs ⟩* ≈ ∈⇒mor fs y∈ys
  project* (x ~[]) ()
  project* (f ∷ fs) (here refl)  = project₁
  project* (f ∷ fs) (there y∈ys) = pullʳ project₂ ○ project* fs y∈ys

  uniqueness* : ∀ {x ys} {g h : x ⇒ prod ys} → (∀ {y} (y∈ys : y ∈ ys) → π[ y∈ys ] ∘ g ≈ π[ y∈ys ] ∘ h) → g ≈ h
  uniqueness* {x} {[]} uni     = !-unique₂
  uniqueness* {x} {y ∷ ys} uni = unique′ (uni (here ≡.refl)) (uniqueness* λ y∈ys → sym-assoc ○ uni (there y∈ys) ○ assoc)

  module _ {a} {A : Set a} (f : A → Obj) where

    uniqueness*′ : ∀ {x ys} {g h : x ⇒ prod (map f ys)} → (∀ {y} (y∈ys : y ∈ ys) → π[ ∈ₚ.∈-map⁺ f y∈ys ] ∘ g ≈ π[ ∈ₚ.∈-map⁺ f y∈ys ] ∘ h) → g ≈ h
    uniqueness*′ {x} {[]} uni = !-unique₂
    uniqueness*′ {x} {y ∷ ys} uni = unique′ (uni (here ≡.refl)) (uniqueness*′ λ y∈ys → sym-assoc ○ uni (there y∈ys) ○ assoc)

    module _ {x} (g : ∀ a → x ⇒ f a) where

      build-mors : (l : List A) → x ⇒ map f l *
      build-mors []      = _ ~[]
      build-mors (y ∷ l) = g y ∷ build-mors l

      build-proj≡ : ∀ {a l} (a∈l : a ∈ l) → g a ≡ ∈⇒mor (build-mors l) (∈ₚ.∈-map⁺ f a∈l)
      build-proj≡ (here refl) = ≡.refl
      build-proj≡ (there a∈l) = build-proj≡ a∈l

      build-proj : ∀ {a l} (a∈l : a ∈ l) → g a ≈ π[ ∈ₚ.∈-map⁺ f a∈l ] ∘ ⟨ build-mors l ⟩*
      build-proj {_} {l} a∈l = reflexive (build-proj≡ a∈l) ○ ⟺ (project* (build-mors l) _)

    build-⟨⟩*∘ : ∀ {x y} (g : ∀ a → x ⇒ f a) (h : y ⇒ x) → ∀ l → ⟨ build-mors g l ⟩* ∘ h ≈ ⟨ build-mors (λ a → g a ∘ h) l ⟩*
    build-⟨⟩*∘ g h []      = !-unique₂
    build-⟨⟩*∘ g h (x ∷ l) = begin
      ⟨ build-mors g (x ∷ l) ⟩* ∘ h                   ≈⟨ ⟨⟩∘ ⟩
      ⟨ g x ∘ h , ⟨ build-mors g l ⟩* ∘ h ⟩           ≈⟨ ⟨⟩-congˡ (build-⟨⟩*∘ g h l) ⟩
      ⟨ g x ∘ h , ⟨ build-mors (λ a → g a ∘ h) l ⟩* ⟩ ∎

    build-uniqueness* : ∀ {x} {g h : ∀ a → x ⇒ f a} → (∀ a → g a ≈ h a) → ∀ l → ⟨ build-mors g l ⟩* ≈ ⟨ build-mors h l ⟩*
    build-uniqueness* {x} {g} {h} uni []      = Equiv.refl
    build-uniqueness* {x} {g} {h} uni (y ∷ l) = ⟨⟩-cong₂ (uni y) (build-uniqueness* uni l)

  -- for vectors

  prodᵥ : ∀ {n} → Vec Obj (suc n) → Obj
  prodᵥ v = Vec.foldr₁ _×_ v

  π[_]ᵥ : ∀ {n x} {xs : Vec Obj (suc n)} → x ∈ᵥ xs → prodᵥ xs ⇒ x
  π[_]ᵥ {.0} {.x} {x ∷ []} (here refl)           = id
  π[_]ᵥ {.(suc _)} {.x} {x ∷ y ∷ xs} (here refl) = π₁
  π[_]ᵥ {.(suc _)} {x} {_ ∷ y ∷ xs} (there x∈xs) = π[ x∈xs ]ᵥ ∘ π₂

  data [_]_⇒ᵥ_* : ∀ n → Obj → Vec Obj n → Set (o ⊔ ℓ) where
    _~[] : ∀ x → [ 0 ] x ⇒ᵥ [] *
    _∷_  : ∀ {x y n} {ys : Vec Obj n} → x ⇒ y → [ n ] x ⇒ᵥ ys * → [ suc n ] x ⇒ᵥ y ∷ ys *

  ⟨_⟩ᵥ* : ∀ {n x ys} (fs : [ suc n ] x ⇒ᵥ ys *) → x ⇒ prodᵥ ys
  ⟨ f ∷ (x ~[]) ⟩ᵥ*  = f
  ⟨ f ∷ (g ∷ fs) ⟩ᵥ* = ⟨ f , ⟨ g ∷ fs ⟩ᵥ* ⟩

  ∈⇒morᵥ : ∀ {n x y ys} (fs : [ n ] x ⇒ᵥ ys *) (y∈ys : y ∈ᵥ ys) → x ⇒ y
  ∈⇒morᵥ (x ~[]) ()
  ∈⇒morᵥ (f ∷ fs) (here refl)  = f
  ∈⇒morᵥ (f ∷ fs) (there y∈ys) = ∈⇒morᵥ fs y∈ys

  projectᵥ* : ∀ {n x y ys} (fs : [ suc n ] x ⇒ᵥ ys *) (y∈ys : y ∈ᵥ ys) → π[ y∈ys ]ᵥ ∘ ⟨ fs ⟩ᵥ* ≈ ∈⇒morᵥ fs y∈ys
  projectᵥ* (f ∷ (x ~[])) (here ≡.refl) = identityˡ
  projectᵥ* (f ∷ g ∷ fs) (here ≡.refl)  = project₁
  projectᵥ* (f ∷ g ∷ fs) (there y∈ys)   = pullʳ project₂ ○ projectᵥ* (g ∷ fs) y∈ys

  uniquenessᵥ* : ∀ {x n ys} {g h : x ⇒ prodᵥ {n} ys} → (∀ {y} (y∈ys : y ∈ᵥ ys) → π[ y∈ys ]ᵥ ∘ g ≈ π[ y∈ys ]ᵥ ∘ h) → g ≈ h
  uniquenessᵥ* {x} {.0} {y ∷ []} uni           = ⟺ identityˡ ○ uni (here ≡.refl) ○ identityˡ
  uniquenessᵥ* {x} {.(suc _)} {y ∷ z ∷ ys} uni = unique′ (uni (here ≡.refl)) (uniquenessᵥ* (λ y∈ys → sym-assoc ○ uni (there y∈ys) ○ assoc))

  module _ {a} {A : Set a} (f : A → Obj) where

    uniquenessᵥ*′ : ∀ {x n ys} {g h : x ⇒ prodᵥ {n} (Vec.map f ys)} → (∀ {y} (y∈ys : y ∈ᵥ ys) → π[ ∈ᵥₚ.∈-map⁺ f y∈ys ]ᵥ ∘ g ≈ π[ ∈ᵥₚ.∈-map⁺ f y∈ys ]ᵥ ∘ h) → g ≈ h
    uniquenessᵥ*′ {x} {.0} {y ∷ []} uni           = ⟺ identityˡ ○ uni (here ≡.refl) ○ identityˡ
    uniquenessᵥ*′ {x} {.(suc _)} {y ∷ z ∷ ys} uni = unique′ (uni (here ≡.refl)) (uniquenessᵥ*′ (λ y∈ys → sym-assoc ○ uni (there y∈ys) ○ assoc))

    module _ {x} (g : ∀ a → x ⇒ f a) where

      buildᵥ-mors : ∀ {n} (l : Vec A n) → [ n ] x ⇒ᵥ Vec.map f l *
      buildᵥ-mors []          = _ ~[]
      buildᵥ-mors (y ∷ [])    = g y ∷ _ ~[]
      buildᵥ-mors (y ∷ z ∷ l) = g y ∷ buildᵥ-mors (z ∷ l)

      buildᵥ-proj≡ : ∀ {a n} {l : Vec A n} (a∈l : a ∈ᵥ l) → g a ≡ ∈⇒morᵥ (buildᵥ-mors l) (∈ᵥₚ.∈-map⁺ f a∈l)
      buildᵥ-proj≡ {_} {_} {y ∷ []} (here refl)    = ≡.refl
      buildᵥ-proj≡ {_} {_} {y ∷ z ∷ l} (here refl) = ≡.refl
      buildᵥ-proj≡ {_} {_} {y ∷ z ∷ l} (there a∈l) = buildᵥ-proj≡ a∈l

      buildᵥ-proj : ∀ {a n} {l : Vec A (suc n)} (a∈l : a ∈ᵥ l) → g a ≈ π[ ∈ᵥₚ.∈-map⁺ f a∈l ]ᵥ ∘ ⟨ buildᵥ-mors l ⟩ᵥ*
      buildᵥ-proj {_} {_} {l} a∈l = reflexive (buildᵥ-proj≡ a∈l) ○ ⟺ (projectᵥ* (buildᵥ-mors l) _)

    buildᵥ-⟨⟩*∘ : ∀ {x y} (g : ∀ a → x ⇒ f a) (h : y ⇒ x) → ∀ {n} (l : Vec A (suc n)) → ⟨ buildᵥ-mors g l ⟩ᵥ* ∘ h ≈ ⟨ buildᵥ-mors (λ a → g a ∘ h) l ⟩ᵥ*
    buildᵥ-⟨⟩*∘ g h (x ∷ [])        = Equiv.refl
    buildᵥ-⟨⟩*∘ g h (x ∷ y ∷ [])    = ⟨⟩∘
    buildᵥ-⟨⟩*∘ g h (x ∷ y ∷ z ∷ l) = begin
      ⟨ g x , ⟨ buildᵥ-mors g (y ∷ z ∷ l) ⟩ᵥ* ⟩ ∘ h                 ≈⟨ ⟨⟩∘ ⟩
      ⟨ g x ∘ h , ⟨ buildᵥ-mors g (y ∷ z ∷ l) ⟩ᵥ* ∘ h ⟩             ≈⟨ ⟨⟩-congˡ (buildᵥ-⟨⟩*∘ g h (y ∷ z ∷ l)) ⟩
      ⟨ g x ∘ h , ⟨ buildᵥ-mors (λ a₁ → g a₁ ∘ h) (y ∷ z ∷ l) ⟩ᵥ* ⟩ ∎

    buildᵥ-uniqueness* : ∀ {x} {g h : ∀ a → x ⇒ f a} → (∀ a → g a ≈ h a) → ∀ {n} (l : Vec A (suc n)) → ⟨ buildᵥ-mors g l ⟩ᵥ* ≈ ⟨ buildᵥ-mors h l ⟩ᵥ*
    buildᵥ-uniqueness* {x} {g} {h} uni (y ∷ []) = uni y
    buildᵥ-uniqueness* {x} {g} {h} uni (y ∷ z ∷ []) = ⟨⟩-cong₂ (uni y) (uni z)
    buildᵥ-uniqueness* {x} {g} {h} uni (y ∷ z ∷ w ∷ l) = ⟨⟩-cong₂ (uni y) (buildᵥ-uniqueness* uni (z ∷ w ∷ l))

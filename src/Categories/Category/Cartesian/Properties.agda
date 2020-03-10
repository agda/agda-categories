{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Category.Cartesian.Properties {o ℓ e} (C : Category o ℓ e) where

open import Function using (_$_)
open import Data.Nat
open import Data.Product using (Σ; _,_; proj₁)
open import Data.Product.Properties
open import Data.List as List
open import Data.List.Any as Any using (here; there)
open import Data.List.Membership.Propositional
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Vec.Any as AnyV using (here; there)
open import Data.Vec.Membership.Propositional renaming (_∈_ to _∈ᵥ_)

open import Relation.Binary.PropositionalEquality as ≡ using (refl)

open import Categories.Category.Cartesian C

open import Categories.Diagram.Pullback C
open import Categories.Diagram.Equalizer C
open import Categories.Morphism.Reasoning C

private
  open Category C
  open HomReasoning
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


module _ (car : Cartesian) where
  open Cartesian car
  private
    _⇒* : Obj → Set _
    x ⇒* = List (Σ Obj (x ⇒_))

    _⇒*[_]ᵥ : Obj → ℕ → Set _
    x ⇒*[ n ]ᵥ = Vec (Σ Obj (x ⇒_)) (suc n)

  -- for lists

  prod : List Obj → Obj
  prod objs = foldr _×_ ⊤ objs

  π[_] : ∀ {x xs} → x ∈ xs → prod xs ⇒ x
  π[ here refl ]  = π₁
  π[ there x∈xs ] = π[ x∈xs ] ∘ π₂

  ⟨_⟩* : ∀ {x} (fs : x ⇒*) → x ⇒ prod (map proj₁ fs)
  ⟨ [] ⟩*           = !
  ⟨ (_ , f) ∷ fs ⟩* = ⟨ f , ⟨ fs ⟩* ⟩

  f∈fs⇒x∈xs : ∀ {x y f} {fs : x ⇒*} → (y , f) ∈ fs → y ∈ map proj₁ fs
  f∈fs⇒x∈xs (here refl)  = here ≡.refl
  f∈fs⇒x∈xs (there f∈fs) = there (f∈fs⇒x∈xs f∈fs)

  project* : ∀ {x y f} {fs : x ⇒*} (f∈fs : (y , f) ∈ fs) → π[ f∈fs⇒x∈xs f∈fs ] ∘ ⟨ fs ⟩* ≈ f
  project* (here refl)                           = project₁
  project* {_} {_} {f} (there {_ , g} {fs} f∈fs) = begin
    (π[ f∈fs⇒x∈xs f∈fs ] ∘ π₂) ∘ ⟨ g , ⟨ fs ⟩* ⟩ ≈⟨ pullʳ project₂ ⟩
    π[ f∈fs⇒x∈xs f∈fs ] ∘ ⟨ fs ⟩*                ≈⟨ project* f∈fs ⟩
    f                                            ∎

  -- for vectors

  prodᵥ : ∀ {n} → Vec Obj (suc n) → Obj
  prodᵥ v = Vec.foldr₁ _×_ v

  π[_]ᵥ : ∀ {n x} {xs : Vec Obj (suc n)} → x ∈ᵥ xs → prodᵥ xs ⇒ x
  π[_]ᵥ {.0} {.x} {x ∷ []} (here refl)           = id
  π[_]ᵥ {.(suc _)} {.x} {x ∷ y ∷ xs} (here refl) = π₁
  π[_]ᵥ {.(suc _)} {x} {_ ∷ y ∷ xs} (there x∈xs) = π[ x∈xs ]ᵥ ∘ π₂

  ⟨_⟩*ᵥ : ∀ {x n} (fs : x ⇒*[ n ]ᵥ) → x ⇒ prodᵥ (Vec.map proj₁ fs)
  ⟨ (x , f) ∷ [] ⟩*ᵥ           = f
  ⟨ (x , f) ∷ (y , g) ∷ fs ⟩*ᵥ = ⟨ f , ⟨ (y , g) ∷ fs ⟩*ᵥ ⟩

  f∈fs⇒x∈xsᵥ : ∀ {x n y f} {fs : x ⇒*[ n ]ᵥ} → (y , f) ∈ᵥ fs → y ∈ᵥ Vec.map proj₁ fs
  f∈fs⇒x∈xsᵥ {_} {_} {_} {_} {_ ∷ []} (here refl)      = here ≡.refl
  f∈fs⇒x∈xsᵥ {_} {_} {_} {_} {_ ∷ x ∷ xs} (here refl)  = here ≡.refl
  f∈fs⇒x∈xsᵥ {_} {_} {_} {_} {_ ∷ x ∷ xs} (there f∈fs) = there (f∈fs⇒x∈xsᵥ f∈fs)

  project*ᵥ : ∀ {x n y f} {fs : x ⇒*[ n ]ᵥ} (f∈fs : (y , f) ∈ᵥ fs) → π[ f∈fs⇒x∈xsᵥ f∈fs ]ᵥ ∘ ⟨ fs ⟩*ᵥ ≈ f
  project*ᵥ {_} {_} {_} {_} {_ ∷ []} (here refl)      = identityˡ
  project*ᵥ {_} {_} {_} {_} {_ ∷ _ ∷ fs} (here refl)  = project₁
  project*ᵥ {_} {_} {_} {_} {_ ∷ _ ∷ fs} (there f∈fs) = pullʳ project₂ ○ project*ᵥ f∈fs

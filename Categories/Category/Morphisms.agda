{-# OPTIONS --without-K --safe #-}
open import Categories.Category

module Categories.Category.Morphisms {o ℓ e} (C : Category o ℓ e) where

open import Level
open import Data.Product using (_,_; _×_; map; zip)
open import Relation.Binary using (Rel)

open import Categories.Square C

open Category C hiding (dom; cod)
open HomReasoning

record Morphism : Set (o ⊔ ℓ) where
  field
    {dom} : Obj
    {cod} : Obj
    arr   : dom ⇒ cod

record Morphism⇒ (f g : Morphism) : Set (ℓ ⊔ e) where
  private
    module f = Morphism f
    module g = Morphism g

  field
    {dom⇒} : f.dom ⇒ g.dom
    {cod⇒} : f.cod ⇒ g.cod
    square : CommutativeSquare f.arr dom⇒ cod⇒ g.arr

Morphisms : Category _ _ _
Morphisms = record
  { Obj       = Morphism
  ; _⇒_       = Morphism⇒
  ; _≈_       = _≈′_
  ; id        = record { square = trans identityˡ (sym identityʳ) }
  ; _∘_       = _∘′_
  ; assoc     = assoc , assoc
  ; identityˡ = identityˡ , identityˡ
  ; identityʳ = identityʳ , identityʳ
  ; equiv     = record
    { refl  = refl , refl
    ; sym   = map sym sym
    ; trans = zip trans trans
    }
  ; ∘-resp-≈  = zip ∘-resp-≈ ∘-resp-≈
  }
  where _≈′_ : ∀ {f g} → Rel (Morphism⇒ f g) _
        f ≈′ g = f.dom⇒ ≈ g.dom⇒ × f.cod⇒ ≈ g.cod⇒
          where module f = Morphism⇒ f
                module g = Morphism⇒ g
                
        _∘′_ : ∀ {f g h} → Morphism⇒ g h → Morphism⇒ f g → Morphism⇒ f h
        m₁ ∘′ m₂ = record
          { square = glue m₁.square m₂.square
          }
          where module m₁ = Morphism⇒ m₁
                module m₂ = Morphism⇒ m₂

{-# OPTIONS --without-K --safe #-}

-- The category of Sets is Monoidal

module Categories.Category.Monoidal.Instance.Sets where

open import Level
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; uncurry; map; <_,_>)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core
open import Function.Related.TypeIsomorphisms
open import Function using (_$_)

open import Categories.Category.BinaryProducts using (BinaryProducts)
import Categories.Category.Cartesian as Cartesian
open import Categories.Category.Cartesian.Monoidal using (module CartesianMonoidal)
import Categories.Category.Cartesian.SymmetricMonoidal as CartesianSymmetric
import Categories.Category.Cocartesian as Cocartesian
open import Categories.Category.Instance.EmptySet
open import Categories.Category.Instance.Sets
open import Categories.Category.Instance.SingletonSet
import Categories.Morphism as Morphism
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.RigCategory using (RigCategory)
open import Categories.Functor.Bifunctor using (Bifunctor)

open import Data.Sum.Properties

-- Sets is a Monoidal Category with × as Bifunctor
module Product {o : Level} where
  private
    S = Sets o
    open Cartesian S

  Sets-has-all : BinaryProducts S
  Sets-has-all = record { product = λ {A} {B} → record
    { A×B = A × B
    ; π₁ = proj₁
    ; π₂ = proj₂
    ; ⟨_,_⟩ = <_,_>
    ; project₁ = λ _ → refl
    ; project₂ = λ _ → refl
    ; unique = λ p₁ p₂ x → sym (cong₂ _,_ (p₁ x) (p₂ x))
    } }

  Sets-is : Cartesian
  Sets-is = record { terminal = SingletonSet-⊤ ; products = Sets-has-all }

  Sets-Monoidal : Monoidal S
  Sets-Monoidal = CartesianMonoidal.monoidal Sets-is

  Sets-Symmetric : Symmetric Sets-Monoidal
  Sets-Symmetric = CartesianSymmetric.symmetric S Sets-is

module Coproduct {o : Level} where
  private
    S = Sets o
    open Cocartesian S

  Sets-has-all : BinaryCoproducts
  Sets-has-all = record { coproduct = λ {A} {B} → record
    { A+B = A ⊎ B
    ; i₁ = inj₁
    ; i₂ = inj₂
    ; [_,_] = [_,_]′
    ; inject₁ = λ _ → refl
    ; inject₂ = λ _ → refl
    ; unique = λ { i₁ i₂ (inj₁ x) → sym (i₁ x) ; i₁ i₂ (inj₂ y) → sym (i₂ y)} -- stdlib?
    } }

  Sets-is : Cocartesian
  Sets-is = record { initial = EmptySet-⊥ ; coproducts = Sets-has-all }

  Sets-Monoidal : Monoidal S
  Sets-Monoidal = Cocartesian.CocartesianMonoidal.+-monoidal S Sets-is

  Sets-Symmetric : Symmetric Sets-Monoidal
  Sets-Symmetric = Cocartesian.CocartesianSymmetricMonoidal.+-symmetric S Sets-is

module Rig {o : Level} where
  private
    S = Sets o
    module Sets⊎ = Coproduct
    module Sets× = Product

  Sets-Rig : RigCategory S Sets⊎.Sets-Symmetric Sets×.Sets-Symmetric
  Sets-Rig = record
    { annₗ = record
      { from = λ ()
      ; to   = λ ()
      ; iso  = record
        { isoˡ = λ ()
        ; isoʳ = λ ()
        }
      }
    ; annᵣ = record
      { from = λ ()
      ; to   = λ ()
      ; iso  = record
        { isoˡ = λ ()
        ; isoʳ = λ ()
        }
      }
    ; distribₗ = record
      { from = λ
        { (x , inj₁ y) → inj₁ (x , y)
        ; (x , inj₂ z) → inj₂ (x , z)
        }
      ; to   = λ
        { (inj₁ (x , y)) → x , inj₁ y
        ; (inj₂ (x , z)) → x , inj₂ z
        }
      ; iso  = record
        { isoˡ = λ
          { (x , inj₁ y) → refl
          ; (x , inj₂ z) → refl
          }
        ; isoʳ = λ
          { (inj₁ (x , y)) → refl
          ; (inj₂ (x , z)) → refl
          }
        }
      }
    ; distribᵣ = record
      { from = λ
        { (inj₁ x , z) → inj₁ (x , z)
        ; (inj₂ y , z) → inj₂ (y , z)
        }
      ; to   = λ
        { (inj₁ (x , z)) → inj₁ x , z
        ; (inj₂ (y , z)) → inj₂ y , z
        }
      ; iso  = record
        { isoˡ = λ
          { (inj₁ x , z) → refl
          ; (inj₂ y , z) → refl
          }
        ; isoʳ = λ
          { (inj₁ (x , z)) → refl
          ; (inj₂ (y , z)) → refl
          }
        }
      }
    ; annₗ-commute = λ ()
    ; annᵣ-commute = λ ()
    ; dl-commute = λ
      { (x , inj₁ y) → refl
      ; (x , inj₂ z) → refl
      }
    ; dr-commute = λ
      { (inj₁ x , z) → refl
      ; (inj₂ y , z) → refl
      }
    ; laplazaI     = λ
      { (a , inj₁ b) → refl
      ; (a , inj₂ c) → refl
      }
    ; laplazaII    = λ
      { (inj₁ a , c) → refl
      ; (inj₂ b , c) → refl
      }
    ; laplazaIV    = λ
      { (inj₁       a  , d) → refl
      ; (inj₂ (inj₁ b) , d) → refl
      ; (inj₂ (inj₂ c) , d) → refl
      }
    ; laplazaVI    = λ
      { (a , b , inj₁ c) → refl
      ; (a , b , inj₂ d) → refl
      }
    ; laplazaIX    = λ
      { (inj₁ a , inj₁ c) → refl
      ; (inj₁ a , inj₂ d) → refl
      ; (inj₂ b , inj₁ c) → refl
      ; (inj₂ b , inj₂ d) → refl
      }
    ; laplazaX     = λ ()
    ; laplazaXI    = λ ()
    ; laplazaXIII  = λ ()
    ; laplazaXV    = λ ()
    ; laplazaXVI   = λ ()
    ; laplazaXVII  = λ ()
    ; laplazaXIX   = λ
      { (a , inj₂ b) → refl
      }
    ; laplazaXXIII = λ
      { (lift tt , inj₁ a) → refl
      ; (lift tt , inj₂ b) → refl
      }
    }

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

  open RigCategory

  Sets-Rig : RigCategory S Sets⊎.Sets-Symmetric Sets×.Sets-Symmetric

  Sets-Rig .annₗ = record
    { from = λ ()
    ; to   = λ ()
    ; iso  = record
      { isoˡ = λ ()
      ; isoʳ = λ ()
      }
    }
  Sets-Rig .annᵣ = record
    { from = λ ()
    ; to   = λ ()
    ; iso  = record
      { isoˡ = λ ()
      ; isoʳ = λ ()
      }
    }

  Sets-Rig .distribₗ = record
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
  Sets-Rig .distribᵣ = record
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

  Sets-Rig .annₗ-commute ()
  Sets-Rig .annᵣ-commute ()

  Sets-Rig .dl-commute (x , inj₁ y) = refl
  Sets-Rig .dl-commute (x , inj₂ z) = refl
  Sets-Rig .dr-commute (inj₁ x , z) = refl
  Sets-Rig .dr-commute (inj₂ y , z) = refl

  Sets-Rig .laplazaI     (a , inj₁ b)        = refl
  Sets-Rig .laplazaI     (a , inj₂ c)        = refl
  Sets-Rig .laplazaII    (inj₁ a , c)        = refl
  Sets-Rig .laplazaII    (inj₂ b , c)        = refl
  Sets-Rig .laplazaIV    (inj₁       a  , d) = refl
  Sets-Rig .laplazaIV    (inj₂ (inj₁ b) , d) = refl
  Sets-Rig .laplazaIV    (inj₂ (inj₂ c) , d) = refl
  Sets-Rig .laplazaVI    (a , b , inj₁ c)    = refl
  Sets-Rig .laplazaVI    (a , b , inj₂ d)    = refl
  Sets-Rig .laplazaIX    (inj₁ a , inj₁ c)   = refl
  Sets-Rig .laplazaIX    (inj₁ a , inj₂ d)   = refl
  Sets-Rig .laplazaIX    (inj₂ b , inj₁ c)   = refl
  Sets-Rig .laplazaIX    (inj₂ b , inj₂ d)   = refl
  Sets-Rig .laplazaX     ()
  Sets-Rig .laplazaXI    ()
  Sets-Rig .laplazaXIII  ()
  Sets-Rig .laplazaXV    ()
  Sets-Rig .laplazaXVI   ()
  Sets-Rig .laplazaXVII  ()
  Sets-Rig .laplazaXIX   (a , inj₂ b)        = refl
  Sets-Rig .laplazaXXIII (lift tt , inj₁ a)  = refl
  Sets-Rig .laplazaXXIII (lift tt , inj₂ b)  = refl

{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Closed

module Categories.Category.Monoidal.Closed.IsClosed
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

open import Data.Product using (Σ; _,_)
open import Function using (_$_) renaming (_∘_ to _∙_)
open import Function.Equality as Π using (Π)

open import Categories.Category.Product
open import Categories.Category.Monoidal.Properties M
open import Categories.Morphism C
open import Categories.Morphism.Properties C
open import Categories.Morphism.Reasoning C
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Bifunctor
open import Categories.Functor.Bifunctor.Properties
open import Categories.NaturalTransformation hiding (id)
open import Categories.NaturalTransformation.Dinatural hiding (_∘ʳ_)
open import Categories.NaturalTransformation.NaturalIsomorphism as NI hiding (refl)
import Categories.Category.Closed as Cls

open Closed Cl

private
  module C = Category C
  open Category C
  open Commutation
  module ℱ = Functor

open HomReasoning
open Π.Π
open adjoint renaming (unit to η; counit to ε)

-- and here we use sub-modules in the hopes of making things go faster
open import Categories.Category.Monoidal.Closed.IsClosed.Identity Cl
open import Categories.Category.Monoidal.Closed.IsClosed.L Cl
open import Categories.Category.Monoidal.Closed.IsClosed.Dinatural Cl
open import Categories.Category.Monoidal.Closed.IsClosed.Diagonal Cl
open import Categories.Category.Monoidal.Closed.IsClosed.Pentagon Cl

private
  id² : {S T : Obj} → [ S , T ]₀ ⇒ [ S , T ]₀
  id² = [ id , id ]₁

  L-natural-comm : {X Y′ Z′ Y Z : Obj} {f : Y′ ⇒ Y} {g : Z ⇒ Z′} →
                  L X Y′ Z′ ∘ [ f , g ]₁ ≈ [ [ id , f ]₁ , [ id , g ]₁ ]₁ ∘ L X Y Z
  L-natural-comm {X} {Y′} {Z′} {Y} {Z} {f} {g} =
    let I = [-,-].identity in begin
    L X Y′ Z′ ∘ [ f , g ]₁                                     ≈⟨ refl⟩∘⟨ [ [-,-] ]-decompose₂ ⟩
    L X Y′ Z′ ∘ [ id , g ]₁ ∘ [ f , id ]₁                      ≈⟨ pullˡ L-g-swap ⟩
    ([ id² , [ id , g ]₁ ]₁ ∘ L X Y′ Z) ∘ [ f , id ]₁          ≈⟨ pullʳ L-f-swap ⟩
    [ id² , [ id , g ]₁ ]₁ ∘ [ [ id , f ]₁ , id² ]₁ ∘ L X Y Z  ≈˘⟨ pushˡ ([-,-].F-resp-≈ (introʳ I , introʳ I) ○ [-,-].homomorphism) ⟩
    [ [ id , f ]₁ , [ id , g ]₁ ]₁ ∘ L X Y Z
      ∎

closed : Cls.Closed C
closed = record
  { [-,-]            = [-,-]
  ; unit             = unit
  ; identity         = identity
  ; diagonal         = diagonal
  ; L                = L
  ; L-natural-comm   = L-natural-comm
  ; L-dinatural-comm = L-dinatural-comm
  ; Lj≈j             = Lj≈j
  ; jL≈i             = jL≈i
  ; iL≈i             = iL≈i
  ; pentagon         = pentagon′
  ; γ⁻¹              = λ {X Y} → record
    { _⟨$⟩_ = λ f → Radjunct f ∘ unitorˡ.to
    ; cong  = λ eq → ∘-resp-≈ˡ (∘-resp-≈ʳ (ℱ.F-resp-≈ (-⊗ X) eq))
    }
  ; γ-inverseOf-γ⁻¹  = λ {X Y} → record
    { left-inverse-of  = λ f → begin
      [ id , Radjunct f ∘ unitorˡ.to ]₁ ∘ [ id , unitorˡ.from ]₁ ∘ η.η unit
        ≈⟨ ℱ.homomorphism [ X ,-] ⟩∘⟨refl ⟩
      ([ id , Radjunct f ]₁ ∘ [ id , unitorˡ.to ]₁) ∘ [ id , unitorˡ.from ]₁ ∘ η.η unit
        ≈⟨ cancelInner (⟺ (ℱ.homomorphism [ X ,-]) ○ ℱ.F-resp-≈ [ X ,-] unitorˡ.isoˡ ○ [-,-].identity) ⟩
      Ladjunct (Radjunct f) ≈⟨ LRadjunct≈id ⟩
      f
        ∎
    ; right-inverse-of = λ f → begin
      Radjunct ([ id , f ]₁ ∘ [ id , unitorˡ.from ]₁ ∘ η.η unit) ∘ unitorˡ.to
        ≈˘⟨ ∘-resp-≈ʳ (ℱ.F-resp-≈ (-⊗ X) (pushˡ (ℱ.homomorphism [ X ,-]))) ⟩∘⟨refl ⟩
      Radjunct (Ladjunct (f ∘ unitorˡ.from)) ∘ unitorˡ.to
        ≈⟨ RLadjunct≈id ⟩∘⟨refl ⟩
      (f ∘ unitorˡ.from) ∘ unitorˡ.to
        ≈⟨ cancelʳ unitorˡ.isoʳ ⟩
      f
        ∎
    }
  }

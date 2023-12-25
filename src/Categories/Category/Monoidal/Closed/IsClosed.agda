{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)

module Categories.Category.Monoidal.Closed.IsClosed
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

open import Data.Product using (_,_)

open import Categories.Morphism.Reasoning C
open import Categories.Functor using (Functor) renaming (id to idF)
open import Categories.Functor.Bifunctor.Properties using ([_]-decompose₂)
import Categories.Category.Closed as Cls

open Closed Cl using (adjoint; [_,_]₀; [_,_]₁; [-,-]; unit; unitorˡ; -⊗_;
  module ⊗; [_,-]; [-,_])

private
  module C = Category C
  open Category C using (module HomReasoning; Obj; _⇒_; id; _∘_; _≈_;
    ∘-resp-≈ˡ; ∘-resp-≈ʳ)
  module ℱ = Functor

open HomReasoning
open adjoint using (Radjunct; Ladjunct; LRadjunct≈id; RLadjunct≈id; Radjunct-resp-≈) renaming (unit to η; counit to ε)

-- and here we use sub-modules in the hopes of making things go faster
open import Categories.Category.Monoidal.Closed.IsClosed.Identity Cl using (identity; diagonal)
open import Categories.Category.Monoidal.Closed.IsClosed.L Cl using (L; L-f-swap; L-g-swap)
open import Categories.Category.Monoidal.Closed.IsClosed.Dinatural Cl using (L-dinatural-comm)
open import Categories.Category.Monoidal.Closed.IsClosed.Diagonal Cl using (Lj≈j; jL≈i; iL≈i)
open import Categories.Category.Monoidal.Closed.IsClosed.Pentagon Cl using (pentagon′)

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
    { to = λ f → Radjunct f ∘ unitorˡ.to
    ; cong  = λ eq → ∘-resp-≈ˡ (∘-resp-≈ʳ (ℱ.F-resp-≈ (-⊗ X) eq))
    }
  ; γ-γ⁻¹-inverseᵇ  = λ {X Y} →
    (λ {f} {y} eq →  begin
      Radjunct y ∘ unitorˡ.to                                                    ≈⟨ Radjunct-resp-≈ eq ⟩∘⟨refl ⟩
      Radjunct ( [ id , f ]₁ ∘ [ id , unitorˡ.from ]₁ ∘ η.η unit) ∘ unitorˡ.to   ≈˘⟨ Radjunct-resp-≈ (pushˡ (ℱ.homomorphism [ X ,-])) ⟩∘⟨refl ⟩
      Radjunct (Ladjunct (f ∘ unitorˡ.from)) ∘ unitorˡ.to                        ≈⟨ RLadjunct≈id ⟩∘⟨refl ⟩
      (f ∘ unitorˡ.from) ∘ unitorˡ.to                                            ≈⟨ cancelʳ unitorˡ.isoʳ ⟩
      f ∎
      ) ,
    λ {y} {f} eq → begin
      [ id , f ]₁ ∘ [ id , unitorˡ.from ]₁ ∘ η.η unit                                   ≈⟨ [-,-].F-resp-≈ (C.Equiv.refl , eq) ⟩∘⟨refl ⟩
      [ id , Radjunct y ∘ unitorˡ.to ]₁ ∘ [ id , unitorˡ.from ]₁ ∘ η.η unit             ≈⟨ ℱ.homomorphism [ X ,-] ⟩∘⟨refl ⟩
      ([ id , Radjunct y ]₁ ∘ [ id , unitorˡ.to ]₁) ∘ [ id , unitorˡ.from ]₁ ∘ η.η unit ≈⟨ cancelInner (⟺ (ℱ.homomorphism [ X ,-]) ○ ℱ.F-resp-≈ [ X ,-] unitorˡ.isoˡ ○ [-,-].identity) ⟩
      Ladjunct (Radjunct y)                                                             ≈⟨ LRadjunct≈id ⟩
      y ∎
  }

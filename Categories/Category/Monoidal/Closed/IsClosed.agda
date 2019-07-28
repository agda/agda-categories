{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Closed

module Categories.Category.Monoidal.Closed.IsClosed
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} {Cl : Closed M} where

open import Data.Product using (Σ; _,_)
open import Function using (_$_) renaming (_∘_ to _∙_)
open import Function.Equality as Π using (Π)

open import Categories.Category.Product
open import Categories.Morphism C
open import Categories.Morphism.Properties C
open import Categories.Morphism.Reasoning C
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Bifunctor
open import Categories.Functor.Bifunctor.Properties
open import Categories.NaturalTransformation hiding (id)
open import Categories.NaturalTransformation.Dinatural hiding (_∘ʳ_)
open import Categories.NaturalTransformation.NaturalIsomorphism as NI hiding (_≅_; refl)
import Categories.Category.Closed as Cls

open Closed Cl

private
  module C = Category C
  open Category C
  module ℱ = Functor
  variable
    X X′ Y Y′ Z Z′ : Obj
    f g h i : X ⇒ Y

open HomReasoning
open Π.Π
open adjoint renaming (unit to η; counit to ε)

private
  identity : NaturalIsomorphism idF [ unit ,-]
  identity = record
    { F⇒G = F∘id⇒F ∘ᵥ ([ unit ,-] ∘ˡ unitorʳ-natural.F⇒G) ∘ᵥ η
    ; F⇐G = ε ∘ᵥ (unitorʳ-natural.F⇐G ∘ʳ [ unit ,-]) ∘ᵥ F⇒id∘F
    ; iso = λ X → Iso-resp-≈ (iso X)
                             (⟺ identityˡ) (⟺ (∘-resp-≈ʳ identityʳ))
    }
    where open Functor
          iso : ∀ X → Iso (Ladjunct unitorʳ.from)
                          (ε.η X ∘ unitorʳ.to)
          iso X = record
            { isoˡ = begin
              (ε.η X ∘ unitorʳ.to) ∘ Ladjunct unitorʳ.from
                ≈⟨ pullʳ unitorʳ-commute-to ⟩
              ε.η X ∘ Ladjunct unitorʳ.from ⊗₁ id ∘ unitorʳ.to
                ≈˘⟨ assoc ⟩
              Radjunct (Ladjunct unitorʳ.from) ∘ unitorʳ.to
                ≈⟨ RLadjunct≈id ⟩∘⟨refl ⟩
              unitorʳ.from ∘ unitorʳ.to
                ≈⟨ unitorʳ.isoʳ ⟩
              id
                ∎
            ; isoʳ = begin
              Ladjunct unitorʳ.from ∘ ε.η X ∘ unitorʳ.to
                ≈⟨ pullʳ (η.commute _) ⟩
              [ id , unitorʳ.from ]₁ ∘ Ladjunct ((ε.η X ∘ unitorʳ.to) ⊗₁ id)
                ≈˘⟨ pushˡ (homomorphism [ unit ,-]) ⟩
              Ladjunct (unitorʳ.from ∘ (ε.η X ∘ unitorʳ.to) ⊗₁ id)
                ≈⟨ F-resp-≈ [ unit ,-] unitorʳ-commute-from ⟩∘⟨refl ⟩
              Ladjunct ((ε.η X ∘ unitorʳ.to) ∘ unitorʳ.from)
                ≈⟨ F-resp-≈ [ unit ,-] (cancelʳ unitorʳ.isoˡ) ⟩∘⟨refl ⟩
              Ladjunct (ε.η X)
                ≈⟨ zag ⟩
              id
                ∎
            }

  diagonal : Extranaturalʳ unit [-,-]
  diagonal = extranaturalʳ (λ X → Ladjunct unitorˡ.from)
                         $ λ {X Y f} → begin
                           [ id , f ]₁ ∘ Ladjunct unitorˡ.from
                             ≈˘⟨ pushˡ (homomorphism [ X ,-]) ⟩
                           [ id , f ∘ unitorˡ.from ]₁ ∘ η.η unit
                             ≈˘⟨ F-resp-≈ [ X ,-] unitorˡ-commute-from ⟩∘⟨refl ⟩
                           [ id , unitorˡ.from ∘ id ⊗₁ f ]₁ ∘ η.η unit
                             ≈⟨ homomorphism [ X ,-] ⟩∘⟨refl ⟩
                           ([ id , unitorˡ.from ]₁ ∘ [ id , id ⊗₁ f ]₁) ∘ η.η unit
                             ≈⟨ pullʳ (mate.commute₁ f) ⟩
                           [ id , unitorˡ.from ]₁ ∘ [ f , id ]₁ ∘ η.η unit
                             ≈⟨ pullˡ [ [-,-] ]-commute ⟩
                           ([ f , id ]₁ ∘ [ id , unitorˡ.from ]₁) ∘ η.η unit
                             ≈⟨ assoc ⟩
                           [ f , id ]₁ ∘ Ladjunct unitorˡ.from
                             ∎
    where open Functor

  L : ∀ X Y Z → [ Y , Z ]₀ ⇒ [ [ X , Y ]₀ , [ X , Z ]₀ ]₀
  L X Y Z = Ladjunct (Ladjunct (ε.η Z ∘ (id ⊗₁ ε.η Y) ∘ associator.from))

  [[X,-],[X,-]] : Obj → Bifunctor C.op C C
  [[X,-],[X,-]] X = [-,-] ∘F (Functor.op [ X ,-] ⁂ [ X ,-])

  L-g-swap : L X Y Z′ ∘  [ id , g ]₁ ≈ [ [ id , id ]₁ , [ id , g ]₁ ]₁ ∘ L X Y Z
  L-g-swap {X = X} {Y = Y} {Z′ = Z′} {Z = Z} {g = g} = begin
    L X Y Z′ ∘  [ id , g ]₁
      ≈⟨ pullʳ (η.commute [ id , g ]₁) ⟩
    [ id , [ id , ε.η Z′ ∘ (id ⊗₁ ε.η Y) ∘ associator.from ]₁ ∘ η.η ([ Y , Z′ ]₀ ⊗₀ [ X , Y ]₀) ]₁
      ∘ [ id , [ id , g ]₁ ⊗₁ id ]₁ ∘ η.η [ Y , Z ]₀
      ≈˘⟨ pushˡ (ℱ.homomorphism [ XY ,-]) ⟩
    [ id , ([ id , ε.η Z′ ∘ (id ⊗₁ ε.η Y) ∘ associator.from ]₁ ∘ η.η ([ Y , Z′ ]₀ ⊗₀ [ X , Y ]₀))
         ∘ [ id , g ]₁ ⊗₁ id
    ]₁ ∘ η.η [ Y , Z ]₀
      ≈⟨ XY-resp-≈ (pullʳ (η.commute ([ id , g ]₁ ⊗₁ id))) ⟩∘⟨refl ⟩
    [ id , [ id , ε.η Z′ ∘ (id ⊗₁ ε.η Y) ∘ associator.from ]₁
          ∘ [ id , ([ id , g ]₁ ⊗₁ id) ⊗₁ id ]₁ ∘ η.η ([ Y , Z ]₀ ⊗₀ [ X , Y ]₀)
    ]₁ ∘ η.η [ Y , Z ]₀
      ≈˘⟨ XY-resp-≈ (pushˡ (ℱ.homomorphism [ X ,-])) ⟩∘⟨refl ⟩
    [ id , [ id , (ε.η Z′ ∘ (id ⊗₁ ε.η Y) ∘ associator.from) ∘ ([ id , g ]₁ ⊗₁ id) ⊗₁ id ]₁
          ∘ η.η ([ Y , Z ]₀ ⊗₀ [ X , Y ]₀)
    ]₁ ∘ η.η [ Y , Z ]₀
      ≈⟨ (XY-resp-≈ $ ∘-resp-≈ˡ $ X-resp-≈ $
           pull-last assoc-commute-from ○ (∘-resp-≈ʳ $ ∘-resp-≈ʳ $ ∘-resp-≈ˡ $ ℱ.F-resp-≈ ⊗ (refl , ⊗.identity))) ⟩∘⟨refl ⟩
    [ id , [ id , ε.η Z′ ∘ (id ⊗₁ ε.η Y) ∘ [ id , g ]₁ ⊗₁ id ∘ associator.from ]₁
          ∘ η.η ([ Y , Z ]₀ ⊗₀ [ X , Y ]₀)
    ]₁ ∘ η.η [ Y , Z ]₀
      ≈⟨ (XY-resp-≈ $ ∘-resp-≈ˡ $ X-resp-≈ $ ∘-resp-≈ʳ $ pullˡ [ ⊗ ]-commute) ⟩∘⟨refl ⟩
    [ id , [ id , ε.η Z′ ∘ ([ id , g ]₁ ⊗₁ id ∘ (id ⊗₁ ε.η Y)) ∘ associator.from ]₁
          ∘ η.η ([ Y , Z ]₀ ⊗₀ [ X , Y ]₀)
    ]₁ ∘ η.η [ Y , Z ]₀
      ≈⟨ (XY-resp-≈ $ ∘-resp-≈ˡ $ X-resp-≈ $ pull-first (ε.commute g)) ⟩∘⟨refl ⟩
    [ id , [ id , (g ∘ ε.η Z)  ∘ (id ⊗₁ ε.η Y) ∘ associator.from ]₁
          ∘ η.η ([ Y , Z ]₀ ⊗₀ [ X , Y ]₀)
    ]₁ ∘ η.η [ Y , Z ]₀
      ≈⟨ (XY-resp-≈ $ pushˡ $ X-resp-≈ assoc ○ ℱ.homomorphism [ X ,-]) ⟩∘⟨refl ⟩
    [ id , [ id , g ]₁
         ∘ ([ id , ε.η Z ∘ (id ⊗₁ ε.η Y) ∘ associator.from ]₁ ∘ η.η ([ Y , Z ]₀ ⊗₀ [ X , Y ]₀))
    ]₁ ∘ η.η [ Y , Z ]₀
      ≈⟨ pushˡ (ℱ.homomorphism [ XY ,-]) ⟩
    [ id , [ id , g ]₁ ]₁ ∘ L X Y Z
      ≈˘⟨ [-,-].F-resp-≈ ([-,-].identity , refl) ⟩∘⟨refl ⟩
    [ [ id , id ]₁ , [ id , g ]₁ ]₁ ∘ L X Y Z
      ∎
    where XY        = [ X , Y ]₀
          XY-resp-≈ = ℱ.F-resp-≈ [ XY ,-]
          X-resp-≈  = ℱ.F-resp-≈ [ X ,-]

--   L-f-swap : L X Y′ Z ∘ [ f , id ]₁ ≈ [ [ id , f ]₁ , [ id , id ]₁ ]₁ ∘ L X Y Z
--   L-f-swap = {!L-f-swap!}

--   L-natural-comm : L X Y′ Z′ ∘ [ f , g ]₁ ≈ [ [ id , f ]₁ , [ id , g ]₁ ]₁ ∘ L X Y Z
--   L-natural-comm {X = X} {Y′ = Y′} {Z′ = Z′} {Y = Y} {f = f} {Z = Z} {g = g} = begin
--     L X Y′ Z′ ∘ [ f , g ]₁
--       ≈⟨ refl⟩∘⟨ [ [-,-] ]-decompose₂ ⟩
--     L X Y′ Z′ ∘ [ id , g ]₁ ∘ [ f , id ]₁
--       ≈⟨ pullˡ L-g-swap ⟩
--     ([ [ id , id ]₁ , [ id , g ]₁ ]₁ ∘ L X Y′ Z) ∘ [ f , id ]₁
--       ≈⟨ pullʳ L-f-swap ⟩
--     [ [ id , id ]₁ , [ id , g ]₁ ]₁ ∘ [ [ id , f ]₁ , [ id , id ]₁ ]₁ ∘ L X Y Z
--       ≈˘⟨ pushˡ ([-,-].F-resp-≈ (introʳ [-,-].identity , introʳ [-,-].identity) ○ [-,-].homomorphism) ⟩
--     [ [ id , f ]₁ , [ id , g ]₁ ]₁ ∘ L X Y Z
--       ∎

-- closed : Cls.Closed C
-- closed = record
--   { [-,-]            = [-,-]
--   ; unit             = unit
--   ; identity         = identity
--   ; diagonal         = diagonal
--   ; L                = L
--   ; L-natural-comm   = L-natural-comm
--   ; L-dinatural-comm = {!L!}
--   ; Lj≈j             = {!!}
--   ; jL≈i             = {!!}
--   ; iL≈i             = {!!}
--   ; pentagon         = {!!}
--   ; γ⁻¹              = {!!}
--   ; γ-inverseOf-γ⁻¹  = {!!}
--   }

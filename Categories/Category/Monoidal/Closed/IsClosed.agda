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

  module identity = NaturalIsomorphism identity

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

  module diagonal = DinaturalTransformation diagonal

  L : ∀ X Y Z → [ Y , Z ]₀ ⇒ [ [ X , Y ]₀ , [ X , Z ]₀ ]₀
  L X Y Z = Ladjunct (Ladjunct (ε.η Z ∘ (id ⊗₁ ε.η Y) ∘ associator.from))

  L-g-swap : L X Y Z′ ∘  [ id , g ]₁ ≈ [ [ id , id ]₁ , [ id , g ]₁ ]₁ ∘ L X Y Z
  L-g-swap {X = X} {Y = Y} {Z′ = Z′} {Z = Z} {g = g} = begin
    L X Y Z′ ∘  [ id , g ]₁
      ≈˘⟨ Ladjunct-comm′ ⟩
    Ladjunct (Ladjunct (ε.η Z′ ∘ (id ⊗₁ ε.η Y) ∘ associator.from) ∘ [ id , g ]₁ ⊗₁ id)
      ≈˘⟨ XY-resp-≈ Ladjunct-comm′ ⟩∘⟨refl ⟩
    Ladjunct (Ladjunct ((ε.η Z′ ∘ (id ⊗₁ ε.η Y) ∘ associator.from) ∘ ([ id , g ]₁ ⊗₁ id) ⊗₁ id))
      ≈⟨ (XY-resp-≈ $ ∘-resp-≈ˡ $ X-resp-≈ $
           pull-last assoc-commute-from ○ (∘-resp-≈ʳ $ ∘-resp-≈ʳ $ ∘-resp-≈ˡ $ ℱ.F-resp-≈ ⊗ (refl , ⊗.identity))) ⟩∘⟨refl ⟩
    Ladjunct (Ladjunct $ ε.η Z′ ∘ (id ⊗₁ ε.η Y) ∘ [ id , g ]₁ ⊗₁ id ∘ associator.from)
      ≈⟨ (XY-resp-≈ $ ∘-resp-≈ˡ $ X-resp-≈ $ ∘-resp-≈ʳ $ pullˡ [ ⊗ ]-commute) ⟩∘⟨refl ⟩
    Ladjunct (Ladjunct $ ε.η Z′ ∘ ([ id , g ]₁ ⊗₁ id ∘ (id ⊗₁ ε.η Y)) ∘ associator.from)
      ≈⟨ (XY-resp-≈ $ ∘-resp-≈ˡ $ X-resp-≈ $ pull-first (ε.commute g)) ⟩∘⟨refl ⟩
    Ladjunct (Ladjunct $ (g ∘ ε.η Z)  ∘ (id ⊗₁ ε.η Y) ∘ associator.from)
      ≈⟨ (XY-resp-≈ $ pushˡ $ X-resp-≈ assoc ○ ℱ.homomorphism [ X ,-]) ⟩∘⟨refl ⟩
    Ladjunct ([ id , g ]₁ ∘ Ladjunct (ε.η Z ∘ (id ⊗₁ ε.η Y) ∘ associator.from))
      ≈⟨ pushˡ (ℱ.homomorphism [ XY ,-]) ⟩
    [ id , [ id , g ]₁ ]₁ ∘ L X Y Z
      ≈˘⟨ [-,-].F-resp-≈ ([-,-].identity , refl) ⟩∘⟨refl ⟩
    [ [ id , id ]₁ , [ id , g ]₁ ]₁ ∘ L X Y Z
      ∎
    where XY        = [ X , Y ]₀
          XY-resp-≈ = ℱ.F-resp-≈ [ XY ,-]
          X-resp-≈  = ℱ.F-resp-≈ [ X ,-]

  L-f-swap : L X Y′ Z ∘ [ f , id ]₁ ≈ [ [ id , f ]₁ , [ id , id ]₁ ]₁ ∘ L X Y Z
  L-f-swap {X = X} {Y′ = Y′} {Z = Z} {Y = Y} {f = f} = begin
    L X Y′ Z ∘ [ f , id ]₁
      ≈˘⟨ Ladjunct-comm′ ⟩
    Ladjunct (Ladjunct (ε.η Z ∘ (id ⊗₁ ε.η Y′) ∘ associator.from) ∘ [ f , id ]₁ ⊗₁ id)
      ≈˘⟨ XY′-resp-≈ Ladjunct-comm′ ⟩∘⟨refl ⟩
    Ladjunct (Ladjunct ((ε.η Z ∘ (id ⊗₁ ε.η Y′) ∘ associator.from) ∘ ([ f , id ]₁ ⊗₁ id) ⊗₁ id))
      ≈⟨ (XY′-resp-≈ $ ∘-resp-≈ˡ $ X-resp-≈ $ pull-last assoc-commute-from) ⟩∘⟨refl ⟩
    Ladjunct (Ladjunct $ ε.η Z ∘ (id ⊗₁ ε.η Y′) ∘ [ f , id ]₁ ⊗₁ id ⊗₁ id ∘ associator.from)
      ≈⟨ (XY′-resp-≈ $ ∘-resp-≈ˡ $ X-resp-≈ $ ∘-resp-≈ʳ $ pullˡ
         (∘-resp-≈ʳ (ℱ.F-resp-≈ ⊗ (refl , ⊗.identity)) ○ [ ⊗ ]-commute)) ⟩∘⟨refl ⟩
    Ladjunct (Ladjunct $ ε.η Z ∘ ([ f , id ]₁ ⊗₁ id ∘ id ⊗₁ ε.η Y′) ∘ associator.from)
      ≈⟨ (XY′-resp-≈ $ ∘-resp-≈ˡ $ X-resp-≈ $ pull-first (mate.commute₂ f)) ⟩∘⟨refl ⟩
    Ladjunct (Ladjunct $ (ε.η Z ∘ id ⊗₁ f) ∘ id ⊗₁ ε.η Y′ ∘ associator.from)
      ≈⟨ (XY′-resp-≈ $ ∘-resp-≈ˡ $ X-resp-≈ $ center $ ⟺ (ℱ.homomorphism ([ Y , Z ]₀ ⊗-))) ⟩∘⟨refl ⟩
    Ladjunct (Ladjunct $ ε.η Z ∘ id ⊗₁ (f ∘ ε.η Y′) ∘ associator.from)
      ≈⟨ (XY′-resp-≈ $ ∘-resp-≈ˡ $ X-resp-≈ $ ∘-resp-≈ʳ $ ∘-resp-≈ˡ $ ℱ.F-resp-≈ ([ Y , Z ]₀ ⊗-) $
         ⟺ (ε.commute f)) ⟩∘⟨refl ⟩
    Ladjunct (Ladjunct $ ε.η Z ∘ id ⊗₁ (ε.η Y ∘ [ id , f ]₁ ⊗₁ id) ∘ associator.from)
      ≈⟨ (XY′-resp-≈ $ ∘-resp-≈ˡ $ X-resp-≈ $ ∘-resp-≈ʳ $ ∘-resp-≈ˡ $ ℱ.homomorphism ([ Y , Z ]₀ ⊗-)) ⟩∘⟨refl ⟩
    Ladjunct (Ladjunct $ ε.η Z ∘ (id ⊗₁ ε.η Y ∘ id ⊗₁ [ id , f ]₁ ⊗₁ id) ∘ associator.from)
      ≈⟨ (XY′-resp-≈ $ ∘-resp-≈ˡ $ X-resp-≈ $ (center⁻¹ refl (⟺ assoc-commute-from)) ○ pullˡ assoc) ⟩∘⟨refl ⟩
    Ladjunct (Ladjunct $ (ε.η Z ∘ id ⊗₁ ε.η Y ∘ associator.from) ∘ (id ⊗₁ [ id , f ]₁) ⊗₁ id)
      ≈⟨ (XY′-resp-≈ $ ∘-resp-≈ˡ $ ℱ.homomorphism [ X ,-]) ⟩∘⟨refl ⟩
    Ladjunct (([ id , ε.η Z ∘ id ⊗₁ ε.η Y ∘ associator.from ]₁ ∘ [ id , (id ⊗₁ [ id , f ]₁) ⊗₁ id ]₁)
             ∘ η.η ([ Y , Z ]₀ ⊗₀ [ X , Y′ ]₀))
      ≈⟨ (XY′-resp-≈ $ pullʳ (⟺ (η.commute (id ⊗₁ [ id , f ]₁))) ○ (⟺ assoc)) ⟩∘⟨refl ⟩
    Ladjunct (Ladjunct (ε.η Z ∘ id ⊗₁ ε.η Y ∘ associator.from) ∘ id ⊗₁ [ id , f ]₁)
      ≈⟨ ℱ.homomorphism [ XY′ ,-] ⟩∘⟨refl ⟩
    ([ id , Ladjunct (ε.η Z ∘ id ⊗₁ ε.η Y ∘ associator.from) ]₁ ∘ [ id , id ⊗₁ [ id , f ]₁ ]₁) ∘ η.η [ Y , Z ]₀
      ≈⟨ pullʳ (mate.commute₁ [ id , f ]₁) ⟩
    [ id , Ladjunct (ε.η Z ∘ id ⊗₁ ε.η Y ∘ associator.from) ]₁ ∘ [ [ id , f ]₁ , id ]₁ ∘ η.η [ Y , Z ]₀
      ≈⟨ pullˡ [ [-,-] ]-commute ○ assoc ○ ∘-resp-≈ˡ ([-,-].F-resp-≈ (refl , ⟺ [-,-].identity)) ⟩
    [ [ id , f ]₁ , [ id , id ]₁ ]₁ ∘ L X Y Z
      ∎
    where XY′        = [ X , Y′ ]₀
          XY′-resp-≈ = ℱ.F-resp-≈ [ XY′ ,-]
          X-resp-≈   = ℱ.F-resp-≈ [ X ,-]

  L-natural-comm : L X Y′ Z′ ∘ [ f , g ]₁ ≈ [ [ id , f ]₁ , [ id , g ]₁ ]₁ ∘ L X Y Z
  L-natural-comm {X = X} {Y′ = Y′} {Z′ = Z′} {Y = Y} {f = f} {Z = Z} {g = g} = begin
    L X Y′ Z′ ∘ [ f , g ]₁
      ≈⟨ refl⟩∘⟨ [ [-,-] ]-decompose₂ ⟩
    L X Y′ Z′ ∘ [ id , g ]₁ ∘ [ f , id ]₁
      ≈⟨ pullˡ L-g-swap ⟩
    ([ [ id , id ]₁ , [ id , g ]₁ ]₁ ∘ L X Y′ Z) ∘ [ f , id ]₁
      ≈⟨ pullʳ L-f-swap ⟩
    [ [ id , id ]₁ , [ id , g ]₁ ]₁ ∘ [ [ id , f ]₁ , [ id , id ]₁ ]₁ ∘ L X Y Z
      ≈˘⟨ pushˡ ([-,-].F-resp-≈ (introʳ [-,-].identity , introʳ [-,-].identity) ○ [-,-].homomorphism) ⟩
    [ [ id , f ]₁ , [ id , g ]₁ ]₁ ∘ L X Y Z
      ∎

  L-dinatural-comm :  [ [ f , id ]₁ , [ id , id ]₁ ]₁ ∘ L X′ Y Z ≈ [ [ id , id ]₁ , [ f , id ]₁ ]₁ ∘ L X Y Z
  L-dinatural-comm {X′ = X′} {Y = Y} {Z = Z} {X = X} {f = f} = begin
    [ [ f , id ]₁ , [ id , id ]₁ ]₁ ∘ L X′ Y Z
      ≈⟨ [-,-].F-resp-≈ (refl , [-,-].identity) ⟩∘⟨refl ⟩
    [ [ f , id ]₁ , id ]₁ ∘ L X′ Y Z
      ≈˘⟨ pushˡ [ [-,-] ]-commute ⟩
    ([ id , Ladjunct (ε.η Z ∘ (id ⊗₁ ε.η Y) ∘ associator.from) ]₁ ∘ [ [ f , id ]₁ , id ]₁) ∘ η.η [ Y , Z ]₀
      ≈˘⟨ pushʳ (mate.commute₁ [ f , id ]₁) ⟩
    [ id , Ladjunct (ε.η Z ∘ (id ⊗₁ ε.η Y) ∘ associator.from) ]₁ ∘ Ladjunct (id ⊗₁ [ f , id ]₁)
      ≈˘⟨ pushˡ (ℱ.homomorphism [ XY ,-]) ⟩
    Ladjunct (Ladjunct (ε.η Z ∘ (id ⊗₁ ε.η Y) ∘ associator.from) ∘ id ⊗₁ [ f , id ]₁)
      ≈˘⟨ XY-resp-≈ Ladjunct-comm′ ⟩∘⟨refl ⟩
    Ladjunct (Ladjunct $ (ε.η Z ∘ (id ⊗₁ ε.η Y) ∘ associator.from) ∘ (id ⊗₁ [ f , id ]₁) ⊗₁ id)
      ≈⟨ (XY-resp-≈ $ ∘-resp-≈ˡ $ X′-resp-≈ $ pull-last assoc-commute-from) ⟩∘⟨refl ⟩
    Ladjunct (Ladjunct $ ε.η Z ∘ (id ⊗₁ ε.η Y) ∘ id ⊗₁ [ f , id ]₁ ⊗₁ id ∘ associator.from)
      ≈˘⟨ (XY-resp-≈ $ ∘-resp-≈ˡ $ X′-resp-≈ $ ∘-resp-≈ʳ $ pushˡ (ℱ.homomorphism (YZ ⊗-))) ⟩∘⟨refl ⟩
    Ladjunct (Ladjunct $ ε.η Z ∘ id ⊗₁ (ε.η Y ∘ [ f , id ]₁ ⊗₁ id) ∘ associator.from)
      ≈⟨ (XY-resp-≈ $ ∘-resp-≈ˡ $ X′-resp-≈ $ ∘-resp-≈ʳ $ ∘-resp-≈ˡ $
         ℱ.F-resp-≈ (YZ ⊗-) (mate.commute₂ f)) ⟩∘⟨refl ⟩
    Ladjunct (Ladjunct $ ε.η Z ∘ id ⊗₁ (ε.η Y ∘ id ⊗₁ f) ∘ associator.from)
      ≈⟨ (XY-resp-≈ $ ∘-resp-≈ˡ $ X′-resp-≈ $ ∘-resp-≈ʳ $ ∘-resp-≈ˡ $ ℱ.homomorphism (YZ ⊗-)) ⟩∘⟨refl ⟩
    Ladjunct (Ladjunct $ ε.η Z ∘ (id ⊗₁ ε.η Y ∘ id ⊗₁ id ⊗₁ f) ∘ associator.from)
      ≈⟨ (XY-resp-≈ $ ∘-resp-≈ˡ $ X′-resp-≈ $ center⁻¹ refl (⟺ assoc-commute-from) ○ pullˡ assoc) ⟩∘⟨refl ⟩
    Ladjunct (Ladjunct $ (ε.η Z ∘ id ⊗₁ ε.η Y ∘ associator.from) ∘ (id ⊗₁ id) ⊗₁ f)
      ≈⟨ (XY-resp-≈ $ pushˡ (ℱ.homomorphism [ X′ ,-])) ⟩∘⟨refl ⟩
    Ladjunct ([ id , ε.η Z ∘ id ⊗₁ ε.η Y ∘ associator.from ]₁ ∘ Ladjunct ((id ⊗₁ id) ⊗₁ f))
      ≈⟨ (XY-resp-≈ $ ∘-resp-≈ʳ (∘-resp-≈ˡ (X′-resp-≈ (⊗.F-resp-≈ (⊗.identity , refl))) ○ mate.commute₁ f)) ⟩∘⟨refl ⟩
    Ladjunct ([ id , ε.η Z ∘ id ⊗₁ ε.η Y ∘ associator.from ]₁ ∘ [ f , id ]₁ ∘ η.η ([ Y , Z ]₀ ⊗₀ [ X , Y ]₀))
      ≈⟨ (XY-resp-≈ $ pullˡ [ [-,-] ]-commute ○ assoc) ⟩∘⟨refl ⟩
    Ladjunct ([ f , id ]₁ ∘ Ladjunct (ε.η Z ∘ id ⊗₁ ε.η Y ∘ associator.from))
      ≈⟨ ∘-resp-≈ˡ (ℱ.homomorphism [ XY ,-]) ○ assoc ⟩
    [ id , [ f , id ]₁ ]₁ ∘ L X Y Z
      ≈˘⟨ [-,-].F-resp-≈ ([-,-].identity , refl) ⟩∘⟨refl ⟩
    [ [ id , id ]₁ , [ f , id ]₁ ]₁ ∘ L X Y Z
      ∎
    where XY        = [ X , Y ]₀
          YZ        = [ Y , Z ]₀
          XY-resp-≈ = ℱ.F-resp-≈ [ XY ,-]
          YZ-resp-≈ = ℱ.F-resp-≈ [ YZ ,-]
          X′-resp-≈ = ℱ.F-resp-≈ [ X′ ,-]

-- closed : Cls.Closed C
-- closed = record
--   { [-,-]            = [-,-]
--   ; unit             = unit
--   ; identity         = identity
--   ; diagonal         = diagonal
--   ; L                = L
--   ; L-natural-comm   = L-natural-comm
--   ; L-dinatural-comm = L-dinatural-comm
--   ; Lj≈j             = {!!}
--   ; jL≈i             = {!!}
--   ; iL≈i             = {!!}
--   ; pentagon         = {!!}
--   ; γ⁻¹              = λ {X Y} → record
--     { _⟨$⟩_ = λ f → Radjunct f ∘ unitorˡ.to
--     ; cong  = λ eq → ∘-resp-≈ˡ (∘-resp-≈ʳ (ℱ.F-resp-≈ (-⊗ X) eq))
--     }
--   ; γ-inverseOf-γ⁻¹  = λ {X Y} → record
--     { left-inverse-of  = λ f → begin
--       [ id , Radjunct f ∘ unitorˡ.to ]₁ ∘ [ id , unitorˡ.from ]₁ ∘ η.η unit
--         ≈⟨ ℱ.homomorphism [ X ,-] ⟩∘⟨ refl ⟩∘⟨ refl ⟩
--       ([ id , Radjunct f ]₁ ∘ [ id , unitorˡ.to ]₁) ∘ [ id , unitorˡ.from ]₁ ∘ η.η unit
--         ≈⟨ cancelInner (⟺ (ℱ.homomorphism [ X ,-]) ○ ℱ.F-resp-≈ [ X ,-] unitorˡ.isoˡ ○ [-,-].identity) ⟩
--       Ladjunct (Radjunct f) ≈⟨ LRadjunct≈id ⟩
--       f
--         ∎
--     ; right-inverse-of = λ f → begin
--       Radjunct ([ id , f ]₁ ∘ [ id , unitorˡ.from ]₁ ∘ η.η unit) ∘ unitorˡ.to
--         ≈˘⟨ ∘-resp-≈ʳ (ℱ.F-resp-≈ (-⊗ X) (pushˡ (ℱ.homomorphism [ X ,-]))) ⟩∘⟨refl ⟩
--       Radjunct (Ladjunct (f ∘ unitorˡ.from)) ∘ unitorˡ.to
--         ≈⟨ RLadjunct≈id ⟩∘⟨refl ⟩
--       (f ∘ unitorˡ.from) ∘ unitorˡ.to
--         ≈⟨ cancelʳ unitorˡ.isoʳ ⟩
--       f
--         ∎
--     }
--   }

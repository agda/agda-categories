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
{-
  pentagon′ : [ [ U , V ]₀ ⇒ [ [ Y , U ]₀ , [ [ X , Y ]₀ , [ X , V ]₀ ]₀ ]₀ ]⟨
               L X U V                            ⇒⟨ [ [ X , U ]₀ , [ X , V ]₀ ]₀ ⟩
               L [ X , Y ]₀ [ X , U ]₀ [ X , V ]₀ ⇒⟨ [ [ [ X , Y ]₀ , [ X , U ]₀ ]₀ , [ [ X , Y ]₀ , [ X , V ]₀ ]₀ ]₀ ⟩
               [ L X Y U , id ]₁
             ≈ L Y U V                            ⇒⟨ [ [ Y , U ]₀ , [ Y , V ]₀ ]₀ ⟩
               [ id , L X Y V ]₁
             ⟩
  pentagon′ {U = U} {V = V} {Y = Y} {X = X} = begin
    [ L X Y U , id ]₁ ∘ L [ X , Y ]₀ [ X , U ]₀ [ X , V ]₀ ∘ L X U V
      ≈˘⟨ refl ⟩∘⟨ Ladjunct-comm′ ⟩
    [ L X Y U , id ]₁ ∘ Ladjunct (Ladjunct (ε.η [ X , V ]₀ ∘ id ⊗₁ ε.η [ X , U ]₀ ∘ associator.from) ∘ L X U V ⊗₁ id)
      ≈˘⟨ pushˡ [ [-,-] ]-commute ⟩
    ([ id , Ladjunct (ε.η [ X , V ]₀ ∘ id ⊗₁ ε.η [ X , U ]₀ ∘ associator.from) ∘ L X U V ⊗₁ id ]₁ ∘ [ L X Y U , id ]₁) ∘ η.η [ U , V ]₀
      ≈˘⟨ pushʳ (mate.commute₁ (L X Y U)) ⟩
    [ id , Ladjunct (ε.η [ X , V ]₀ ∘ id ⊗₁ ε.η [ X , U ]₀ ∘ associator.from) ∘ L X U V ⊗₁ id ]₁ ∘ [ id , id ⊗₁ L X Y U ]₁ ∘ η.η [ U , V ]₀
      ≈˘⟨ pushˡ (ℱ.homomorphism [ [ Y , U ]₀ ,-]) ⟩
    Ladjunct ((Ladjunct (ε.η [ X , V ]₀ ∘ id ⊗₁ ε.η [ X , U ]₀ ∘ associator.from) ∘ L X U V ⊗₁ id) ∘ id ⊗₁ L X Y U)
      ≈˘⟨ Ladjunct-resp-≈ $ pushʳ [ ⊗ ]-decompose₁ ⟩
    Ladjunct (Ladjunct (ε.η [ X , V ]₀ ∘ id ⊗₁ ε.η [ X , U ]₀ ∘ associator.from) ∘ L X U V ⊗₁ L X Y U)
      ≈˘⟨ Ladjunct-resp-≈ $ Ladjunct-comm′ ⟩
    Ladjunct (Ladjunct $ (ε.η [ X , V ]₀ ∘ id ⊗₁ ε.η [ X , U ]₀ ∘ associator.from) ∘ (L X U V ⊗₁ L X Y U) ⊗₁ id)
      ≈⟨ Ladjunct-resp-≈ $ Ladjunct-resp-≈ $ pull-last assoc-commute-from ⟩
    Ladjunct (Ladjunct $ ε.η [ X , V ]₀ ∘ id ⊗₁ ε.η [ X , U ]₀ ∘ L X U V ⊗₁ L X Y U ⊗₁ id ∘ associator.from)
      ≈⟨ Ladjunct-resp-≈ $ Ladjunct-resp-≈ $ ∘-resp-≈ʳ $ pullˡ (⟺ ⊗.homomorphism ○ ⊗.F-resp-≈ (identityˡ , refl)) ⟩
    Ladjunct (Ladjunct $ ε.η [ X , V ]₀ ∘ L X U V ⊗₁ (ε.η [ X , U ]₀ ∘ L X Y U ⊗₁ id) ∘ associator.from)
      ≈⟨ Ladjunct-resp-≈ $ Ladjunct-resp-≈ $ ∘-resp-≈ʳ $ ∘-resp-≈ˡ $ [ ⊗ ]-decompose₁ ⟩
    Ladjunct (Ladjunct $ ε.η [ X , V ]₀ ∘ (L X U V ⊗₁ id ∘ id ⊗₁ (ε.η [ X , U ]₀ ∘ L X Y U ⊗₁ id)) ∘ associator.from)
      ≈⟨ Ladjunct-resp-≈ $ Ladjunct-resp-≈ $ center⁻¹ RLadjunct≈id (∘-resp-≈ˡ (ℱ.F-resp-≈ ([ U , V ]₀ ⊗-) RLadjunct≈id)) ⟩
    Ladjunct (Ladjunct $ Ladjunct (ε.η V ∘ id ⊗₁ ε.η U ∘ associator.from) ∘ id ⊗₁ Ladjunct (ε.η U ∘ id ⊗₁ ε.η Y ∘ associator.from) ∘ associator.from)
      ≈˘⟨ Ladjunct-resp-≈ $ Ladjunct-resp-≈ $ Ladjunct-comm′ ⟩
    Ladjunct (Ladjunct $ Ladjunct $ (ε.η V ∘ id ⊗₁ ε.η U ∘ associator.from) ∘ (id ⊗₁ Ladjunct (ε.η U ∘ id ⊗₁ ε.η Y ∘ associator.from) ∘ associator.from) ⊗₁ id)
      ≈⟨ Ladjunct-resp-≈ $ Ladjunct-resp-≈ $ Ladjunct-resp-≈ $ pushʳ $ ℱ.homomorphism (-⊗ X) ⟩
    Ladjunct (Ladjunct $ Ladjunct $ ((ε.η V ∘ id ⊗₁ ε.η U ∘ associator.from) ∘ (id ⊗₁ Ladjunct (ε.η U ∘ id ⊗₁ ε.η Y ∘ associator.from)) ⊗₁ id) ∘ associator.from ⊗₁ id)
      ≈⟨ Ladjunct-resp-≈ $ Ladjunct-resp-≈ $ Ladjunct-resp-≈ $ ∘-resp-≈ˡ $ pull-last assoc-commute-from ⟩
    Ladjunct (Ladjunct $ Ladjunct $ (ε.η V ∘ id ⊗₁ ε.η U ∘ id ⊗₁ Ladjunct (ε.η U ∘ id ⊗₁ ε.η Y ∘ associator.from) ⊗₁ id ∘ associator.from) ∘ associator.from ⊗₁ id)
      ≈⟨ Ladjunct-resp-≈ $ Ladjunct-resp-≈ $ Ladjunct-resp-≈ $ (∘-resp-≈ˡ $ ∘-resp-≈ʳ $ pullˡ $ ⟺ (ℱ.homomorphism ([ U , V ]₀ ⊗-))) ○ ∘-resp-≈ˡ (⟺ assoc) ○ assoc ⟩
    Ladjunct (Ladjunct $ Ladjunct $ (ε.η V ∘ id ⊗₁ (ε.η U ∘ Ladjunct (ε.η U ∘ id ⊗₁ ε.η Y ∘ associator.from) ⊗₁ id)) ∘ (associator.from ∘ associator.from ⊗₁ id))
      ≈⟨ Ladjunct-resp-≈ $ Ladjunct-resp-≈ $ Ladjunct-resp-≈ $ ∘-resp-≈ˡ $ ∘-resp-≈ʳ $ ℱ.F-resp-≈ ([ U , V ]₀ ⊗-) (RLadjunct≈id ○ ⟺ assoc) ⟩
    Ladjunct (Ladjunct $ Ladjunct $ (ε.η V ∘ id ⊗₁ ((ε.η U ∘ id ⊗₁ ε.η Y) ∘ associator.from)) ∘ (associator.from ∘ associator.from ⊗₁ id))
      ≈⟨ Ladjunct-resp-≈ $ Ladjunct-resp-≈ $ Ladjunct-resp-≈ $ ∘-resp-≈ˡ $ ∘-resp-≈ʳ $ ℱ.homomorphism ([ U , V ]₀ ⊗-) ⟩
    Ladjunct (Ladjunct $ Ladjunct $ (ε.η V ∘ id ⊗₁ (ε.η U ∘ id ⊗₁ ε.η Y) ∘ id ⊗₁ associator.from) ∘ (associator.from ∘ associator.from ⊗₁ id))
      ≈⟨ Ladjunct-resp-≈ $ Ladjunct-resp-≈ $ Ladjunct-resp-≈ $ pull-last refl ⟩
    Ladjunct (Ladjunct $ Ladjunct $ ε.η V ∘ id ⊗₁ (ε.η U ∘ id ⊗₁ ε.η Y) ∘ (id ⊗₁ associator.from ∘ associator.from ∘ associator.from ⊗₁ id))
      ≈⟨ Ladjunct-resp-≈ $ Ladjunct-resp-≈ $ Ladjunct-resp-≈ $ ∘-resp-≈ʳ $ ∘-resp-≈ (ℱ.homomorphism ([ U , V ]₀ ⊗-)) pentagon ⟩
    Ladjunct (Ladjunct $ Ladjunct $ ε.η V ∘ (id ⊗₁ ε.η U ∘ id ⊗₁ (id ⊗₁ ε.η Y)) ∘ (associator.from ∘ associator.from))
      ≈⟨ Ladjunct-resp-≈ $ Ladjunct-resp-≈ $ Ladjunct-resp-≈ $ ⟺ assoc ○ ⟺ assoc ○ ∘-resp-≈ˡ (pull-last (⟺ assoc-commute-from)) ○ assoc ○ ∘-resp-≈ʳ (∘-resp-≈ˡ (⟺ assoc)) ○ ⟺ (center refl) ⟩
    Ladjunct (Ladjunct $ Ladjunct $ (ε.η V ∘ id ⊗₁ ε.η U ∘ associator.from) ∘ (id ⊗₁ id) ⊗₁ ε.η Y ∘ associator.from)
      ≈⟨ Ladjunct-resp-≈ $ Ladjunct-resp-≈ $ Ladjunct-resp-≈ $ ∘-resp-≈ʳ $ ∘-resp-≈ˡ $ ⊗.F-resp-≈ (⊗.identity , refl) ⟩
    Ladjunct (Ladjunct $ Ladjunct $ (ε.η V ∘ id ⊗₁ ε.η U ∘ associator.from) ∘ id ⊗₁ ε.η Y ∘ associator.from)
      ≈˘⟨ Ladjunct-resp-≈ $ Ladjunct-resp-≈ $ Ladjunct-resp-≈ $ center⁻¹ RLadjunct≈id refl ⟩
    Ladjunct (Ladjunct $ Ladjunct $ ε.η V ∘ (Ladjunct (ε.η V ∘ id ⊗₁ ε.η U ∘ associator.from) ⊗₁ id ∘ id ⊗₁ ε.η Y) ∘ associator.from)
      ≈⟨ Ladjunct-resp-≈ $ Ladjunct-resp-≈ $ Ladjunct-resp-≈ $ ∘-resp-≈ʳ $ pushˡ (⟺ [ ⊗ ]-commute) ⟩
    Ladjunct (Ladjunct $ Ladjunct $ ε.η V ∘ id ⊗₁ ε.η Y ∘ Ladjunct (ε.η V ∘ id ⊗₁ ε.η U ∘ associator.from) ⊗₁ id ∘ associator.from)
      ≈˘⟨ Ladjunct-resp-≈ $ Ladjunct-resp-≈ $ Ladjunct-resp-≈ $ pull-last assoc-commute-from ○ (∘-resp-≈ʳ $ ∘-resp-≈ʳ $ ∘-resp-≈ˡ (⊗.F-resp-≈ (refl , ⊗.identity))) ⟩
    Ladjunct (Ladjunct $ Ladjunct $ (ε.η V ∘ id ⊗₁ ε.η Y ∘ associator.from) ∘ (Ladjunct (ε.η V ∘ id ⊗₁ ε.η U ∘ associator.from) ⊗₁ id) ⊗₁ id)
      ≈⟨ Ladjunct-resp-≈ $ Ladjunct-resp-≈ $ Ladjunct-comm′ ⟩
    Ladjunct (Ladjunct $ Ladjunct (ε.η V ∘ id ⊗₁ ε.η Y ∘ associator.from) ∘ Ladjunct (ε.η V ∘ id ⊗₁ ε.η U ∘ associator.from) ⊗₁ id)
      ≈⟨ Ladjunct-resp-≈ Ladjunct-comm′ ⟩
    Ladjunct (L X Y V ∘ Ladjunct (ε.η V ∘ id ⊗₁ ε.η U ∘ associator.from))
      ≈⟨ pushˡ (ℱ.homomorphism [ [ Y , U ]₀ ,-]) ⟩
    [ id , L X Y V ]₁ ∘ L Y U V
      ∎
-}
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
  ; pentagon         = {!!} -- pentagon′
  ; γ⁻¹              = λ {X Y} → record
    { _⟨$⟩_ = λ f → Radjunct f ∘ unitorˡ.to
    ; cong  = λ eq → ∘-resp-≈ˡ (∘-resp-≈ʳ (ℱ.F-resp-≈ (-⊗ X) eq))
    }
  ; γ-inverseOf-γ⁻¹  = λ {X Y} → record
    { left-inverse-of  = λ f → begin
      [ id , Radjunct f ∘ unitorˡ.to ]₁ ∘ [ id , unitorˡ.from ]₁ ∘ η.η unit
        ≈⟨ ℱ.homomorphism [ X ,-] ⟩∘⟨ refl ⟩∘⟨ refl ⟩
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

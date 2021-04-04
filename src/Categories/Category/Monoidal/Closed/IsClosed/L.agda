{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)

module Categories.Category.Monoidal.Closed.IsClosed.L
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

open import Data.Product using (_,_)
open import Function using (_$_) renaming (_∘_ to _∙_)
open import Function.Equality as Π using (Π)

open import Categories.Morphism.Reasoning C
  using (pull-last; pull-first; pullˡ; pushˡ; center; center⁻¹; pullʳ)
open import Categories.Functor using (Functor)
open import Categories.Functor.Bifunctor.Properties

open Closed Cl
open Category C
open HomReasoning
open Equiv

private
  module ℱ = Functor
  α⇒ = associator.from
  α⇐ = associator.to

open Π.Π
open adjoint renaming (unit to η; counit to ε; Ladjunct to 𝕃; Ladjunct-comm′ to 𝕃-comm′;
 Ladjunct-resp-≈ to 𝕃-resp-≈)

L : (X Y Z : Obj) → [ Y , Z ]₀ ⇒ [ [ X , Y ]₀ , [ X , Z ]₀ ]₀
L X Y Z = 𝕃 (𝕃 (ε.η Z ∘ (id ⊗₁ ε.η Y) ∘ α⇒))

private
  [g]₁         : {W Z Z′ : Obj} {g : Z ⇒ Z′} → [ W , Z ]₀ ⇒ [ W , Z′ ]₀
  [g]₁ {g = g} = [ id , g ]₁

  push-α⇒-right : {X Y Z Z′ : Obj} {g : Z ⇒ Z′} → (ε.η Z′ ∘ (id ⊗₁ ε.η {X} Y) ∘ α⇒) ∘ ([g]₁ ⊗₁ id) ⊗₁ id ≈ (g ∘ ε.η Z) ∘ (id ⊗₁ ε.η Y) ∘ α⇒
  push-α⇒-right {X} {Y} {Z} {Z′} {g} = begin
   (ε.η Z′ ∘ (id ⊗₁ ε.η {X} Y) ∘ α⇒) ∘ ([g]₁ ⊗₁ id) ⊗₁ id ≈⟨ pull-last assoc-commute-from ⟩
   ε.η Z′ ∘ (id ⊗₁ ε.η {X} Y) ∘ ([g]₁ ⊗₁ (id ⊗₁ id)) ∘ α⇒ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ℱ.F-resp-≈ ⊗ (refl , ⊗.identity) ⟩∘⟨refl ⟩
   ε.η Z′ ∘ (id ⊗₁ ε.η Y) ∘ [g]₁ ⊗₁ id ∘ α⇒               ≈⟨ refl⟩∘⟨ pullˡ [ ⊗ ]-commute ⟩
   ε.η Z′ ∘ ([g]₁ ⊗₁ id ∘ (id ⊗₁ ε.η Y)) ∘ α⇒             ≈⟨ pull-first (ε.commute g) ⟩
   (g ∘ ε.η Z) ∘ (id ⊗₁ ε.η Y) ∘ α⇒                       ∎

L-g-swap : {X Y Z Z′ : Obj} {g : Z ⇒ Z′} → L X Y Z′ ∘  [ id , g ]₁ ≈ [ [ id , id ]₁ , [ id , g ]₁ ]₁ ∘ L X Y Z
L-g-swap {X} {Y} {Z} {Z′} {g} = begin
  L X Y Z′ ∘  [g]₁                                           ≈˘⟨ 𝕃-comm′ ⟩
  𝕃 (𝕃 (ε.η Z′ ∘ (id ⊗₁ ε.η Y) ∘ α⇒) ∘ [g]₁ ⊗₁ id)           ≈˘⟨ 𝕃-resp-≈ 𝕃-comm′ ⟩
  𝕃 (𝕃 $ (ε.η Z′ ∘ (id ⊗₁ ε.η Y) ∘ α⇒) ∘ ([g]₁ ⊗₁ id) ⊗₁ id) ≈⟨ 𝕃-resp-≈ $ 𝕃-resp-≈ push-α⇒-right ⟩
  𝕃 (𝕃 $ (g ∘ ε.η Z) ∘ (id ⊗₁ ε.η Y) ∘ α⇒)                   ≈⟨ 𝕃-resp-≈ $ pushˡ $ X-resp-≈ assoc ○ ℱ.homomorphism [ X ,-] ⟩
  𝕃 ([ id , g ]₁ ∘ 𝕃 (ε.η Z ∘ (id ⊗₁ ε.η Y) ∘ α⇒))           ≈⟨ pushˡ (ℱ.homomorphism [ XY ,-]) ⟩
  [ id , [g]₁ ]₁ ∘ L X Y Z                                   ≈˘⟨ [-,-].F-resp-≈ ([-,-].identity , refl) ⟩∘⟨refl ⟩
  [ [ id , id ]₁ , [g]₁ ]₁ ∘ L X Y Z                         ∎
  where
  XY        = [ X , Y ]₀
  X-resp-≈  = ℱ.F-resp-≈ [ X ,-]

L-f-swap : {X Y Y′ Z : Obj} {f : Y′ ⇒ Y} → L X Y′ Z ∘ [ f , id ]₁ ≈ [ [ id , f ]₁ , [ id , id ]₁ ]₁ ∘ L X Y Z
L-f-swap {X} {Y} {Y′} {Z} {f} = begin
  L X Y′ Z ∘ [fˡ]₁                                       ≈˘⟨ 𝕃-comm′ ⟩
  𝕃 (𝕃 inner-L ∘ [fˡ]₁ ⊗₁ id)                            ≈˘⟨ 𝕃-resp-≈ 𝕃-comm′ ⟩
  𝕃 (𝕃 (inner-L ∘ ([fˡ]₁ ⊗₁ id) ⊗₁ id))                  ≈⟨ 𝕃-resp-≈ $ 𝕃-resp-≈ fˡ⇒fʳ ⟩
  𝕃 (𝕃 $ inner-L ∘ (id ⊗₁ [fʳ]₁) ⊗₁ id)                  ≈⟨ 𝕃-resp-≈ $ ∘-resp-≈ˡ $ ℱ.homomorphism [ X ,-] ⟩
  𝕃 (([ id , inner-L ]₁ ∘ [ id , (id ⊗₁ [fʳ]₁) ⊗₁ id ]₁)
           ∘ η.η (YZ ⊗₀ XY′))                            ≈⟨ 𝕃-resp-≈ $ pullʳ (⟺ (η.commute _)) ○ sym-assoc ⟩
  𝕃 (𝕃 inner-L ∘ id ⊗₁ [fʳ]₁)                            ≈⟨ ℱ.homomorphism [ XY′ ,-] ⟩∘⟨refl ⟩
  ([ id , 𝕃 inner-L ]₁ ∘ [ id , id ⊗₁ [fʳ]₁ ]₁) ∘ η.η YZ ≈⟨ pullʳ (mate.commute₁ [fʳ]₁) ⟩
  [ id , 𝕃 inner-L ]₁ ∘ [ [fʳ]₁ , id ]₁ ∘ η.η YZ         ≈⟨ pullˡ [ [-,-] ]-commute ○ assoc ○ ∘-resp-≈ˡ ([-,-].F-resp-≈ (refl , ⟺ [-,-].identity)) ⟩
  [ [fʳ]₁ , [ id , id ]₁ ]₁ ∘ L X Y Z                    ∎
  where
  XY′         = [ X , Y′ ]₀
  YZ          = [ Y , Z ]₀
  [fʳ]₁   : ∀ {W} → [ W , Y′ ]₀ ⇒ [ W , Y ]₀
  [fʳ]₁       = [ id , f ]₁
  [fˡ]₁   : ∀ {W} → [ Y , W ]₀ ⇒ [ Y′ , W ]₀
  [fˡ]₁       = [ f , id ]₁
  inner-L : ∀ {W} → ([ W , Z ]₀ ⊗₀ [ X , W ]₀) ⊗₀ X ⇒ Z
  inner-L {W} = ε.η Z ∘ id ⊗₁ ε.η {X} W ∘ α⇒

  fˡ⇒fʳ : inner-L {Y′} ∘ ([fˡ]₁ ⊗₁ id) ⊗₁ id ≈ inner-L {Y} ∘ (id ⊗₁ [fʳ]₁) ⊗₁ id
  fˡ⇒fʳ = begin
    inner-L ∘ ([fˡ]₁ ⊗₁ id) ⊗₁ id                   ≈⟨ pull-last assoc-commute-from ⟩
    ε.η Z ∘ (id ⊗₁ ε.η Y′) ∘ [fˡ]₁ ⊗₁ id ⊗₁ id ∘ α⇒ ≈⟨ ∘-resp-≈ʳ $ pullˡ
                                                       (∘-resp-≈ʳ (ℱ.F-resp-≈ ⊗ (refl , ⊗.identity)) ○ [ ⊗ ]-commute) ⟩
    ε.η Z ∘ ([fˡ]₁ ⊗₁ id ∘ id ⊗₁ ε.η Y′) ∘ α⇒       ≈⟨ pull-first (mate.commute₂ f) ⟩
    (ε.η Z ∘ id ⊗₁ f) ∘ id ⊗₁ ε.η Y′ ∘ α⇒           ≈⟨ center $ ⟺ (ℱ.homomorphism (YZ ⊗-)) ⟩
    ε.η Z ∘ id ⊗₁ (f ∘ ε.η Y′) ∘ α⇒                 ≈⟨ ∘-resp-≈ʳ $ ∘-resp-≈ˡ $ ℱ.F-resp-≈ (YZ ⊗-) $ ⟺ (ε.commute f) ⟩
    ε.η Z ∘ id ⊗₁ (ε.η Y ∘ [fʳ]₁ ⊗₁ id) ∘ α⇒        ≈⟨ ∘-resp-≈ʳ $ ∘-resp-≈ˡ $ ℱ.homomorphism (YZ ⊗-) ⟩
    ε.η Z ∘ (id ⊗₁ ε.η Y ∘ id ⊗₁ [fʳ]₁ ⊗₁ id) ∘ α⇒  ≈⟨ (center⁻¹ refl (⟺ assoc-commute-from)) ○ pullˡ assoc ⟩
    inner-L ∘ (id ⊗₁ [fʳ]₁) ⊗₁ id                   ∎

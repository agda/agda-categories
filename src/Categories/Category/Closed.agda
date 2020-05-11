{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Category.Closed {o ℓ e} (C : Category o ℓ e) where

private
  module C = Category C
  open C
  variable
    A B X X′ Y Y′ Z Z′ U V : Obj
    f g : A ⇒ B

  open Commutation C

open import Level
open import Data.Product using (Σ; _,_)
open import Function.Equality using (_⟶_)
open import Function.Inverse using (_InverseOf_; Inverse)

open import Categories.Category.Product
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Bifunctor
open import Categories.Functor.Construction.Constant
open import Categories.NaturalTransformation
open import Categories.NaturalTransformation.NaturalIsomorphism
open import Categories.NaturalTransformation.Dinatural

record Closed : Set (levelOfTerm C) where
  field
    -- internal hom
    [-,-] : Bifunctor C.op C C
    unit  : Obj

  [_,-] : Obj → Functor C C
  [_,-] = appˡ [-,-]

  [-,_] : Obj → Functor C.op C
  [-,_] = appʳ [-,-]

  module [-,-] = Functor [-,-]

  [_,_]₀ : Obj → Obj → Obj
  [ X , Y ]₀ = [-,-].F₀ (X , Y)

  [_,_]₁ : A ⇒ B → X ⇒ Y → [ B , X ]₀ ⇒ [ A , Y ]₀
  [ f , g ]₁ = [-,-].F₁ (f , g)

  field
    -- i
    identity : NaturalIsomorphism idF [ unit ,-]
    -- j
    diagonal : Extranaturalʳ unit [-,-]

  module identity = NaturalIsomorphism identity
  module diagonal = DinaturalTransformation diagonal

  [[X,-],[X,-]] : Obj → Bifunctor C.op C C
  [[X,-],[X,-]] X = [-,-] ∘F (Functor.op [ X ,-] ⁂ [ X ,-])

  [[-,Y],[-,Z]] : Obj → Obj → Bifunctor C C.op C
  [[-,Y],[-,Z]] Y Z = [-,-] ∘F ((Functor.op [-, Y ]) ⁂ [-, Z ])

  -- L needs to be natural in Y and Z while extranatural in Z.
  -- it is better to spell out the conditions and then prove that indeed
  -- the naturality conditions hold.
  field
    L : ∀ X Y Z → [ Y , Z ]₀ ⇒ [ [ X , Y ]₀ , [ X , Z ]₀ ]₀
    L-natural-comm : [ [ Y , Z ]₀ ⇒  [ [ X , Y′ ]₀ , [ X , Z′ ]₀ ]₀ ]⟨
                       [ f , g ]₁                                   ⇒⟨ [ Y′ , Z′ ]₀ ⟩
                       L X Y′ Z′
                     ≈ L X Y Z                                      ⇒⟨ [ [ X , Y ]₀ , [ X , Z ]₀ ]₀ ⟩
                       [ [ C.id , f ]₁ , [ C.id , g ]₁ ]₁
                     ⟩
    L-dinatural-comm : [ [ Y , Z ]₀ ⇒  [ [ X , Y ]₀ , [ X′ , Z ]₀ ]₀ ]⟨
                         L X′ Y Z                                      ⇒⟨ [ [ X′ , Y ]₀ , [ X′ , Z ]₀ ]₀ ⟩
                         [ [ f , C.id ]₁ , [ C.id , C.id ]₁ ]₁
                       ≈ L X Y Z                                       ⇒⟨ [ [ X , Y ]₀ , [ X , Z ]₀ ]₀ ⟩
                         [ [ C.id , C.id ]₁ , [ f , C.id ]₁ ]₁
                       ⟩

  L-natural : NaturalTransformation [-,-] ([[X,-],[X,-]] X)
  L-natural {X} = ntHelper record
    { η       = λ where
      (Y , Z) → L X Y Z
    ; commute = λ _ → L-natural-comm
    }

  L-dinatural : Extranaturalʳ [ Y , Z ]₀ (flip-bifunctor ([[-,Y],[-,Z]] Y Z))
  L-dinatural {Y} {Z} = extranaturalʳ (λ X → L X Y Z) L-dinatural-comm

  module L-natural {X}     = NaturalTransformation (L-natural {X})
  module L-dinatural {Y Z} = DinaturalTransformation (L-dinatural {Y} {Z})

  -- other required diagrams
  field
    Lj≈j : [ unit ⇒ [ [ X , Y ]₀ , [ X , Y ]₀ ]₀ ]⟨
             diagonal.α Y                        ⇒⟨ [ Y , Y ]₀ ⟩
             L X Y Y
           ≈ diagonal.α [ X , Y ]₀
           ⟩
    jL≈i : [ [ X , Y ]₀ ⇒ [ unit , [ X , Y ]₀ ]₀ ]⟨
             L X X Y                             ⇒⟨ [ [ X , X ]₀ , [ X , Y ]₀ ]₀ ⟩
             [ diagonal.α X , C.id ]₁
           ≈ identity.⇒.η [ X , Y ]₀
           ⟩
    iL≈i : [ [ Y , Z ]₀ ⇒ [ Y , [ unit , Z ]₀ ]₀ ]⟨
             L unit Y Z                          ⇒⟨ [ [ unit , Y ]₀ , [ unit , Z ]₀ ]₀ ⟩
             [ identity.⇒.η Y , C.id ]₁
           ≈ [ C.id , identity.⇒.η Z ]₁
           ⟩

    pentagon : [ [ U , V ]₀ ⇒ [ [ Y , U ]₀ , [ [ X , Y ]₀ , [ X , V ]₀ ]₀ ]₀ ]⟨
                 L X U V                            ⇒⟨ [ [ X , U ]₀ , [ X , V ]₀ ]₀ ⟩
                 L [ X , Y ]₀ [ X , U ]₀ [ X , V ]₀ ⇒⟨ [ [ [ X , Y ]₀ , [ X , U ]₀ ]₀ , [ [ X , Y ]₀ , [ X , V ]₀ ]₀ ]₀ ⟩
                 [ L X Y U , C.id ]₁
               ≈ L Y U V                            ⇒⟨ [ [ Y , U ]₀ , [ Y , V ]₀ ]₀ ⟩
                 [ C.id , L X Y V ]₁
               ⟩

  open Functor

  γ : hom-setoid {X} {Y} ⟶ hom-setoid {unit} {[ X , Y ]₀}
  γ {X} = record
    { _⟨$⟩_ = λ f → [ C.id , f ]₁ ∘ diagonal.α _
    ; cong  = λ eq → ∘-resp-≈ˡ (F-resp-≈ [ X ,-] eq)
    }

  field
    γ⁻¹             : hom-setoid {unit} {[ X , Y ]₀} ⟶ hom-setoid {X} {Y}
    γ-inverseOf-γ⁻¹ : γ {X} {Y} InverseOf γ⁻¹

  γ-inverse : Inverse (hom-setoid {unit} {[ X , Y ]₀}) (hom-setoid {X} {Y})
  γ-inverse = record
    { to         = γ⁻¹
    ; from       = γ
    ; inverse-of = γ-inverseOf-γ⁻¹
    }

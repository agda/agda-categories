{-# OPTIONS --without-K --safe #-}
module Categories.Adjoint where

open import Level using (Level; _⊔_)

open import Categories.Category
open import Categories.Category.Product
open import Categories.Category.Sets
open import Categories.Functor.Bifunctor renaming (id to idF)
open import Categories.Functor.Hom
open import Categories.NaturalTransformation renaming (id to idN)
import Categories.Square as Square

private
  variable
    o ℓ e : Level
    C D : Category o ℓ e

record Adjoint (L : Functor C D) (R : Functor D C) : Set (levelOf C ⊔ levelOf D) where
  private
    module C = Category C
    module D = Category D
    module L = Functor L
    module R = Functor R

  field
    unit   : NaturalTransformation idF (R ∘F L)
    counit : NaturalTransformation (L ∘F R) idF

  module unit = NaturalTransformation unit
  module counit = NaturalTransformation counit

  field
    zig : ∀ {A : C.Obj} → counit.η (L.F₀ A) D.∘ L.F₁ (unit.η A) D.≈ D.id
    zag : ∀ {B : D.Obj} → R.F₁ (counit.η B) C.∘ unit.η (R.F₀ B) C.≈ C.id

  private
    variable
      A : C.Obj
      B : D.Obj

  Ladjunct : L.F₀ A D.⇒ B → A C.⇒ R.F₀ B
  Ladjunct f = R.F₁ f C.∘ unit.η _

  Radjunct : A C.⇒ R.F₀ B → L.F₀ A D.⇒ B
  Radjunct f = counit.η _ D.∘ L.F₁ f

  RLadjunct≈id : ∀ {f : L.F₀ A D.⇒ B} → Radjunct (Ladjunct f) D.≈ f
  RLadjunct≈id {f = f} = begin
    Radjunct (Ladjunct f)                            ≈⟨ refl⟩∘⟨ L.homomorphism ⟩
    counit.η _ D.∘ L.F₁ (R.F₁ f) D.∘ L.F₁ (unit.η _) ≈⟨ pullˡ (counit.commute f) ⟩
    (f D.∘ counit.η _) D.∘ L.F₁ (unit.η _)           ≈⟨ pullʳ zig ⟩
    f D.∘ D.id                                       ≈⟨ D.identityʳ ⟩
    f                                                ∎
    where open D.HomReasoning
          open Square D

  LRadjunct≈id : ∀ {f : A C.⇒ R.F₀ B} → Ladjunct (Radjunct f) C.≈ f
  LRadjunct≈id {f = f} = begin
    Ladjunct (Radjunct f)                              ≈⟨ R.homomorphism ⟩∘⟨ refl ⟩
    (R.F₁ (counit.η _) C.∘ R.F₁ (L.F₁ f)) C.∘ unit.η _ ≈˘⟨ pushʳ (unit.commute f) ⟩
    R.F₁ (counit.η _) C.∘ unit.η _ C.∘ f               ≈⟨ pullˡ zag ⟩
    C.id C.∘ f                                         ≈⟨ C.identityˡ ⟩
    f                                                  ∎
    where open C.HomReasoning
          open Square C

  Hom[L-,-] : Bifunctor C.op D (Setoids _ _)
  Hom[L-,-] = Hom[ D ][-,-] ∘F (L.op ⁂ idF)

  Hom[-,R-] : Bifunctor C.op D (Setoids _ _)
  Hom[-,R-] = Hom[ C ][-,-] ∘F (idF ⁂ R)

  op : Adjoint R.op L.op
  op = record
    { unit   = counit.op
    ; counit = unit.op
    ; zig    = zag
    ; zag    = zig
    }

infix 5 _⊣_
_⊣_ = Adjoint
  

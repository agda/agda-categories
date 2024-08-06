{-# OPTIONS --without-K --safe #-}

open import Categories.Category

-- Various properties of Slice Categories
-- 1. Given a Product in a Slice cat, we cat get the pullback of the arrows
-- 2. Given that same pullback, can extract a Product
module Categories.Category.Slice.Properties {o ℓ e} (C : Category o ℓ e) where

open import Categories.Category.Equivalence using (StrongEquivalence)
open import Categories.Functor
open import Categories.Object.Product
open import Categories.Diagram.Pullback
open import Categories.Morphism.Reasoning C
open import Categories.Object.Terminal C
import Categories.Category.Slice as S

private
  module C = Category C

module _ {A : C.Obj} where
  open S C
  open Category (Slice A)
  open SliceObj
  open Slice⇒
  open C.HomReasoning
  open C.Equiv

  product⇒pullback : ∀ {X Y : Obj} → Product (Slice A) X Y → Pullback C (arr X) (arr Y)
  product⇒pullback {X} p = record
    { p₁              = h π₁
    ; p₂              = h π₂
    ; isPullback = record
      { commute         = △ π₁ ○ ⟺ (△ π₂)
      ; universal       = λ eq → h ⟨ slicearr eq , slicearr refl ⟩
      ; p₁∘universal≈h₁ = project₁
      ; p₂∘universal≈h₂ = project₂
      ; unique-diagram  = λ {D j i} eq₁ eq₂ →
          let D′ : SliceObj A
              D′ = sliceobj (arr A×B C.∘ i)
              arr∘j≈arr∘i : arr A×B C.∘ j C.≈ arr A×B C.∘ i
              arr∘j≈arr∘i = begin
                arr A×B C.∘ j        ≈⟨ pushˡ (⟺ (△ π₁)) ⟩
                arr X C.∘ h π₁ C.∘ j ≈⟨ refl⟩∘⟨ eq₁ ⟩
                arr X C.∘ h π₁ C.∘ i ≈⟨ pullˡ (△ π₁) ⟩
                arr A×B C.∘ i        ∎
              j′ : D′ ⇒ A×B
              j′ = slicearr {h = j} arr∘j≈arr∘i
              i′ : D′ ⇒ A×B
              i′ = slicearr {h = i} refl
          in unique′ {h = j′} {i = i′} eq₁ eq₂
      }
    }
    where open Product (Slice A) p

  pullback⇒product : ∀ {X Y : Obj} → Pullback C (arr X) (arr Y) → Product (Slice A) X Y
  pullback⇒product {X} {Y} p = record
    { A×B      = sliceobj (arr Y C.∘ p₂)
    ; π₁       = slicearr commute
    ; π₂       = slicearr refl
    ; ⟨_,_⟩    = λ f g → slicearr (pullʳ (p₂∘universal≈h₂ {eq = △ f ○ ⟺ (△ g)}) ○ △ g)
    ; project₁ = p₁∘universal≈h₁
    ; project₂ = p₂∘universal≈h₂
    ; unique   = λ eq eq′ → ⟺ (unique eq eq′)
    }
    where open Pullback p

module _ (t : Terminal) where
  open S C
  open Terminal t
  open Category (Slice ⊤)
  open SliceObj
  open Slice⇒
  open C.HomReasoning

  lift : ∀ {A B : C.Obj} (f : A C.⇒ B) → Slice⇒ (sliceobj (! {A})) (sliceobj (! {B}))
  lift f = slicearr {h = f} !-unique₂

  pullback⇒product′ : ∀ {X Y : Obj} → Pullback C (arr X) (arr Y) → Product (Slice ⊤) X Y
  pullback⇒product′ {X} {Y} p = record
    { A×B      = sliceobj !
    ; π₁       = slicearr {h = p₁} !-unique₂
    ; π₂       = slicearr {h = p₂} !-unique₂
    ; ⟨_,_⟩    = λ f g → slicearr {h = universal (△ f ○ ⟺ (△ g))} !-unique₂
    ; project₁ = p₁∘universal≈h₁
    ; project₂ = p₂∘universal≈h₂
    ; unique   = λ eq eq′ → ⟺ (unique eq eq′)
    }
    where open Pullback p

-- slice of slice
module _ {A B} (f : A C.⇒ B) where
  private
    C/B : Category _ _ _
    C/B = S.Slice C B
    module C/B = Category C/B

    C/A : Category _ _ _
    C/A = S.Slice C A
    module C/A = Category C/A

    open C.HomReasoning
    open C.Equiv

  slice-slice⇒slice : Functor (S.Slice C/B (S.sliceobj f)) C/A
  slice-slice⇒slice = record
    { F₀           = λ { (S.sliceobj (S.slicearr {h} △)) → S.sliceobj h }
    ; F₁           = λ { (S.slicearr △) → S.slicearr △ }
    ; identity     = refl
    ; homomorphism = refl
    ; F-resp-≈     = λ eq → eq
    }

  slice⇒slice-slice : Functor C/A (S.Slice C/B (S.sliceobj f))
  slice⇒slice-slice = record
    { F₀           = λ { (S.sliceobj arr) → S.sliceobj (S.slicearr {h = arr} refl) }
    ; F₁           = λ { (S.slicearr △) → S.slicearr {h = S.slicearr (pullʳ △)} △ }
    ; identity     = refl
    ; homomorphism = refl
    ; F-resp-≈     = λ eq → eq
    }

  slice-slice≃slice : StrongEquivalence C/A (S.Slice C/B (S.sliceobj f))
  slice-slice≃slice = record
    { F            = slice⇒slice-slice
    ; G            = slice-slice⇒slice
    ; weak-inverse = record
      { F∘G≈id = record
        { F⇒G = record
          { η           = λ { (S.sliceobj (S.slicearr △)) → S.slicearr {h = S.slicearr (C.identityʳ ○ ⟺ △)} C.identityʳ }
          ; commute     = λ _ → id-comm-sym
          ; sym-commute = λ _ → id-comm
          }
        ; F⇐G           = record
          { η           = λ { (S.sliceobj (S.slicearr △)) → S.slicearr {h = S.slicearr (C.identityʳ ○ △)} C.identityʳ }
          ; commute     = λ _ → id-comm-sym
          ; sym-commute = λ _ → id-comm
          }
        ; iso = λ _ → record
          { isoˡ = C.identity²
          ; isoʳ = C.identity²
          }
        }
      ; G∘F≈id = record
        { F⇒G = record
          { η           = λ { (S.sliceobj arr) → S.slicearr C.identityʳ }
          ; commute     = λ _ → id-comm-sym
          ; sym-commute = λ _ → id-comm
          }
        ; F⇐G           = record
          { η           = λ { (S.sliceobj arr) → S.slicearr C.identityʳ }
          ; commute     = λ _ → id-comm-sym
          ; sym-commute = λ _ → id-comm
          }
        ; iso = λ _ → record
          { isoˡ = C.identity²
          ; isoʳ = C.identity²
          }
        }
      }
    }

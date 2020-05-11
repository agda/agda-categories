{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)

module Categories.Category.CartesianClosed.Locally {o ℓ e} (C : Category o ℓ e) where

open import Level using (levelOfTerm)

open import Categories.Category.CartesianClosed
open import Categories.Category.Cartesian
open import Categories.Category.Cartesian.Properties C
open import Categories.Category.Complete.Finitely C
open import Categories.Category.Slice C
open import Categories.Category.Slice.Properties C

open import Categories.Object.Product
open import Categories.Object.Exponential
open import Categories.Object.Terminal C
import Categories.Diagram.Pullback as P
import Categories.Diagram.Pullback.Properties C as Pₚ
import Categories.Morphism.Reasoning as MR

open Category C

record Locally : Set (levelOfTerm C) where
  field
    sliceCCC : ∀ A → CartesianClosed (Slice A)

  -- only populate this module with some stuff, for space reasons
  module sliceCCC A = CartesianClosed (sliceCCC A) using (product; products; exp)

  pullbacks : ∀ {X A B} (f : A ⇒ X) (g : B ⇒ X) → P.Pullback C f g
  pullbacks {X} _ _ = product⇒pullback (sliceCCC.product X)

  -- the slice categories also have pullbacks, because slice of slice is slice.
  slice-pullbacks : ∀ {A} {B X Y : SliceObj A} (f : Slice⇒ X B) (g : Slice⇒ Y B) → P.Pullback (Slice A) f g
  slice-pullbacks {A} {B} {X} {Y} f g = record
    { P               = sliceobj (X.arr ∘ p.p₁)
    ; p₁              = slicearr refl
    ; p₂              = slicearr comm
    ; commute         = p.commute
    ; universal       = λ {Z} {h i} eq → slicearr {h = p.universal eq} (pullʳ p.p₁∘universal≈h₁ ○ Slice⇒.△ h)
    ; unique          = λ eq₁ eq₂ → p.unique eq₁ eq₂
    ; p₁∘universal≈h₁ = p.p₁∘universal≈h₁
    ; p₂∘universal≈h₂ = p.p₂∘universal≈h₂
    }
    where open HomReasoning
          open Equiv
          module X = SliceObj X
          module Y = SliceObj Y
          module B = SliceObj B
          module f = Slice⇒ f
          module g = Slice⇒ g
          module p = P.Pullback (pullbacks f.h g.h) using (p₁; p₂; commute; universal;
                                 p₁∘universal≈h₁; p₂∘universal≈h₂; unique)
          open MR C

          comm : Y.arr ∘ p.p₂ ≈ X.arr ∘ p.p₁
          comm = begin
            Y.arr ∘ p.p₂         ≈˘⟨ g.△ ⟩∘⟨refl ⟩
            (B.arr ∘ g.h) ∘ p.p₂ ≈˘⟨ pushʳ p.commute ⟩
            B.arr ∘ f.h ∘ p.p₁   ≈⟨ pullˡ f.△ ⟩
            X.arr ∘ p.p₁         ∎

module _ (LCCC : Locally) (t : Terminal) where
  open Locally LCCC
  open Terminal t
  open HomReasoning
  open Equiv

  cartesian : Cartesian C
  cartesian = record
    { terminal = t
    ; products = record { product = Pₚ.pullback-⊤⇒product t (product⇒pullback (sliceCCC.product ⊤)) }
    }

  cartesianClosed : CartesianClosed C
  cartesianClosed = record
    { cartesian = cartesian
    ; exp       = λ {A B} →
      let open Exponential (exp {sliceobj (! {A})} {sliceobj (! {B})})
      in record
      { B^A      = Y B^A
      ; product  =
        -- this is tricky. how product is implemented requires special care. for example, the following
        -- code also gives a product that type checks, but it is impossible to work with.
        -- Pₚ.pullback-⊤⇒product t (Pₚ.pullback-resp-≈ (product⇒pullback product) !-unique₂ refl)
        --
        -- another quirk of proof relevance.
        let open Product (Slice ⊤) (exp.product {sliceobj (! {A})} {sliceobj (! {B})})
        in record
           { A×B      = Y A×B
           ; π₁       = h π₁
           ; π₂       = h π₂
           ; ⟨_,_⟩    = λ f g → h ⟨ slicearr {h = f} (⟺ (!-unique _)) , slicearr {h = g} (⟺ (!-unique _)) ⟩
           ; project₁ = project₁
           ; project₂ = project₂
           ; unique   = unique {h = slicearr (⟺ (!-unique _))}
           }
      ; eval     = h eval
      ; λg       = λ {X} p f → h (λg (pullback⇒product′ t (Pₚ.product⇒pullback-⊤ t p)) (lift t f))
                         -- what looks like an identity proof below is not quite, as it is not
                         -- "proof relevant", the 2 underlying arrows contain different proofs.
      ; β        = λ p → ∘-resp-≈ʳ (exp.product.⟨⟩-cong₂ refl refl) ○
                         β (pullback⇒product′ t (Pₚ.product⇒pullback-⊤ t p))
      ; λ-unique = λ p eq → λ-unique (pullback⇒product′ t (Pₚ.product⇒pullback-⊤ t p))
                                     {h = slicearr (⟺ (!-unique _))}
                                     (∘-resp-≈ʳ (exp.product.⟨⟩-cong₂ refl refl) ○ eq)
      }
    }
    where open sliceCCC ⊤ using (exp)
          open SliceObj
          open Slice⇒

  finitelyComplete : FinitelyComplete
  finitelyComplete = record
    { cartesian = cartesian
    ; equalizer = λ f g → prods×pullbacks⇒equalizers (Cartesian.products cartesian)
                                                     (λ {_ _ X} h i → product⇒pullback (sliceCCC.product X))
    }

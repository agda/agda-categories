{-# OPTIONS --without-K --safe #-}

open import Categories.Category

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
open import Categories.Diagram.Pullback C
import Categories.Diagram.Pullback.Properties C as Pₚ

open Category C

record Locally : Set (levelOfTerm C) where
  field
    sliceCCC : ∀ A → CartesianClosed (Slice A)

  module sliceCCC A = CartesianClosed (sliceCCC A)


module _ (LCCC : Locally) (t : Terminal) where
  open Locally LCCC
  open Terminal t
  open HomReasoning
  
  cartesian : Cartesian C
  cartesian = record
    { terminal = t
    ; products = record
      { product = λ {A B} → Pₚ.pullback-⊤⇒product t (product⇒pullback product)
      }
    }
    where open sliceCCC ⊤ using (product)

  private
    module cartesian = Cartesian cartesian

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
           ; unique   = λ eq eq′ → unique {h = slicearr (⟺ (!-unique _))} eq eq′
           }
      ; eval     = h eval
      ; λg       = λ {X} p f → h (λg (pullback⇒product′ t (Pₚ.product⇒pullback-⊤ t p)) (lift t f))
      ; β        = λ p → ∘-resp-≈ʳ (exp.product.⟨⟩-cong₂ refl refl) ○ β (pullback⇒product′ t (Pₚ.product⇒pullback-⊤ t p))
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
    ; equalizer = λ f g → prods×pullbacks⇒equalizers cartesian.products
                                                     (λ {_ _ X} h i → product⇒pullback (sliceCCC.product X))
    }

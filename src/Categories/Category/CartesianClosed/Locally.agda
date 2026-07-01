{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)

module Categories.Category.CartesianClosed.Locally {o ℓ e} (C : Category o ℓ e) where

open import Level using (levelOfTerm)

open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Category.CartesianClosed
open import Categories.Category.Cartesian
open import Categories.Category.Cartesian.Properties C
open import Categories.Category.Complete.Finitely C
open import Categories.Category.Slice C
open import Categories.Category.Slice.Properties C

open import Categories.Object.Product
import Categories.Object.Exponential.Canonical as Exponentials
open import Categories.Object.Terminal
import Categories.Diagram.Pullback as P
import Categories.Diagram.Pullback.Properties C as Pₚ
import Categories.Morphism.Reasoning as MR

open Category C

record Locally : Set (levelOfTerm C) where
  field
    sliceCCC : (A : Obj) → CartesianClosed (Slice A)

  -- only populate this module with some stuff, for space reasons
  module sliceCCC A = CartesianClosed (sliceCCC A) using (exp; cartesian)
  module sliceProd A = BinaryProducts (Cartesian.products (sliceCCC.cartesian A))
  module sliceTerm A = Terminal (Cartesian.terminal (sliceCCC.cartesian A))

  pullbacks : ∀ {X A B} (f : A ⇒ X) (g : B ⇒ X) → P.Pullback C f g
  pullbacks {X} _ _ = product⇒pullback (sliceProd.product X)

  -- the slice categories also have pullbacks, because slice of slice is slice.
  slice-pullbacks : ∀ {A} {B X Y : SliceObj A} (f : Slice⇒ X B) (g : Slice⇒ Y B) → P.Pullback (Slice A) f g
  slice-pullbacks {A} {B} {X} {Y} f g = record
    { P               = sliceobj (X.arr ∘ p.p₁)
    ; p₁              = slicearr refl
    ; p₂              = slicearr comm
    ; isPullback = record
      { commute         = p.commute
      ; universal       = λ {Z} {h i} eq → slicearr {h = p.universal eq} (pullʳ p.p₁∘universal≈h₁ ○ Slice⇒.△ h)
      ; p₁∘universal≈h₁ = p.p₁∘universal≈h₁
      ; p₂∘universal≈h₂ = p.p₂∘universal≈h₂
      ; unique-diagram  = p.unique-diagram
      }
    }
    where open HomReasoning
          open Equiv
          module X = SliceObj X
          module Y = SliceObj Y
          module B = SliceObj B
          module f = Slice⇒ f
          module g = Slice⇒ g
          module p = P.Pullback (pullbacks f.h g.h) using (p₁; p₂; commute; universal;
                                 p₁∘universal≈h₁; p₂∘universal≈h₂; unique-diagram)
          open MR C

          comm : Y.arr ∘ p.p₂ ≈ X.arr ∘ p.p₁
          comm = begin
            Y.arr ∘ p.p₂         ≈˘⟨ g.△ ⟩∘⟨refl ⟩
            (B.arr ∘ g.h) ∘ p.p₂ ≈˘⟨ pushʳ p.commute ⟩
            B.arr ∘ f.h ∘ p.p₁   ≈⟨ pullˡ f.△ ⟩
            X.arr ∘ p.p₁         ∎

module _ (LCCC : Locally) (t : Terminal C) where
  open Locally LCCC
  open HomReasoning
  open Equiv

  cartesian : Cartesian C
  cartesian = record
    { terminal = t
    ; products = record { product = Pₚ.pullback-⊤⇒product t (product⇒pullback (sliceProd.product (Terminal.⊤ t))) }
    }

  open Cartesian cartesian

  cartesianClosed : CartesianClosed C
  cartesianClosed = record
    { cartesian = cartesian
    ; exp       = λ {A B} →
      let open Exponential (exp {sliceobj (! {A})} {sliceobj (! {B})})
               renaming (eval to slice-eval; λg to slice-λg; β to slice-β)
      in record
      { B^A      = Y B^A
      ; eval     = h (slice-eval ∘ˢ ⟨ slicearr {h = π₁} (⟺ (!-unique _)) , slicearr {h = π₂} (⟺ (!-unique _)) ⟩ˢ)
      ; λg       = λ {X} f → h (slice-λg (slicearr {h = f} (Terminal.!-unique₂ t))) 
      ; β        = λ {g = g} → begin 
        h (slice-eval ∘ˢ ⟨ slicearr {h = π₁} (⟺ (!-unique _)) , slicearr {h = π₂} (⟺ (!-unique _)) ⟩ˢ) ∘ (h (slice-λg (slicearr (Terminal.!-unique₂ t))) ×₁ id) 
          ≈⟨ refl ⟩ 
        (h slice-eval ∘ h ⟨ slicearr {h = π₁} (⟺ (!-unique _)) , slicearr {h = π₂} (⟺ (!-unique _)) ⟩ˢ) ∘ (h (slice-λg (slicearr (Terminal.!-unique₂ t))) ×₁ id) 
          ≈⟨ pullʳ (sym (uniqueˢ {h = slicearr !-unique₂} (pullˡ project₁ˢ ○ project₁) (pullˡ project₂ˢ ○ project₂))) ⟩ 
        h slice-eval ∘ h (slice-λg (slicearr (Terminal.!-unique₂ t)) ×₁ˢ idˢ) ≈⟨ slice-β ⟩ 
        g ∎
      ; λ-unique = λ {g = f} {g} eq → λ-unique (begin
        h slice-eval ∘ h (slicearr {h = g} !-unique₂ ×₁ˢ idˢ) 
          ≈˘⟨ pullʳ (⟨⟩∘ˢ {h = slicearr !-unique₂} ○ ⟨⟩-cong₂ˢ project₁ project₂) ⟩ 
        h (slice-eval ∘ˢ ⟨ slicearr {h = π₁} (⟺ (!-unique _)) , slicearr {h = π₂} (⟺ (!-unique _)) ⟩ˢ) ∘ (g ×₁ id) 
          ≈⟨ eq ⟩ 
        f ∎)
      }
    }
    where open sliceCCC ⊤ using (exp) renaming (cartesian to sliceCartesian)
          open Exponentials sliceCartesian
          open SliceObj
          open Slice⇒
          open MR C
          open Cartesian sliceCartesian renaming 
            (π₁ to π₁ˢ; π₂ to π₂ˢ; ⟨_,_⟩ to ⟨_,_⟩ˢ; _×₁_ to _×₁ˢ_; unique to uniqueˢ
            ; project₁ to project₁ˢ; project₂ to project₂ˢ; ⟨⟩∘ to ⟨⟩∘ˢ; ⟨⟩-cong₂ to ⟨⟩-cong₂ˢ) 
            using ()
          open Category (Slice _) renaming (_∘_ to _∘ˢ_; id to idˢ) using ()

  finitelyComplete : FinitelyComplete
  finitelyComplete = Pₚ.pullback-⊤⇒FinitelyComplete pullbacks t

{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Properties.Setoids.LCCC where

open import Level
open import Function.Equality as Func using (Π; _⟶_)
open import Relation.Binary using (Setoid)
import Relation.Binary.PropositionalEquality as ≡

open import Categories.Category
open import Categories.Category.Slice
open import Categories.Category.Slice.Properties
open import Categories.Category.CartesianClosed
open import Categories.Category.CartesianClosed.Canonical
  using (module Equivalence)
  renaming (CartesianClosed to Canonical)
open import Categories.Category.CartesianClosed.Locally
open import Categories.Category.Instance.Span
open import Categories.Category.Instance.Setoids
open import Categories.Category.Instance.Properties.Setoids.Complete
open import Categories.Category.Monoidal.Instance.Setoids
open import Categories.Functor

open import Categories.Object.Terminal
open import Categories.Diagram.Pullback
open import Categories.Diagram.Pullback.Limit
import Categories.Object.Product as Prod

open Π using (_⟨$⟩_)

module _ {o ℓ} where

  module _ {A X : Setoid o ℓ} where
    private
      module A = Setoid A
      module X = Setoid X

    record InverseImage (a : Setoid.Carrier A) (f : X ⟶ A) : Set (o ⊔ ℓ) where
      constructor pack

      field
        x    : X.Carrier
        fx≈a : f ⟨$⟩ x A.≈ a

    inverseImage-transport : ∀ {a a′} {f : X ⟶ A} → a A.≈ a′ → InverseImage a f → InverseImage a′ f
    inverseImage-transport eq img = pack x (A.trans fx≈a eq)
      where open InverseImage img

  module _ {A X Y : Setoid o ℓ} where
    private
      module A = Setoid A
      module X = Setoid X
      module Y = Setoid Y

    -- the inverse image part of an exponential object the slice category of Setoids
    -- it's a morphism from f to g, which in set theory is
    --   f⁻¹(a) ⟶ g⁻¹(a)
    -- here, we need to take care of some coherence condition.
    record InverseImageMap (a : Setoid.Carrier A)
                           (f : X ⟶ A)
                           (g : Y ⟶ A) : Set (o ⊔ ℓ) where
      field
        f⇒g  : InverseImage a f → InverseImage a g
        cong : ∀ (x x′ : InverseImage a f) →
                 InverseImage.x x X.≈ InverseImage.x x′ →
                 InverseImage.x (f⇒g x) Y.≈ InverseImage.x (f⇒g x′)

    inverseImageMap-transport : ∀ {a a′} {f : X ⟶ A} {g : Y ⟶ A} → a A.≈ a′ →
                                  InverseImageMap a f g → InverseImageMap a′ f g
    inverseImageMap-transport eq h = record
      { f⇒g  = λ img → inverseImage-transport eq (f⇒g (inverseImage-transport (A.sym eq) img))
      ; cong = λ x x′ eq′ → cong (inverseImage-transport (A.sym eq) x) (inverseImage-transport (A.sym eq) x′) eq′
      }
      where open InverseImageMap h

    record SlExp (f : X ⟶ A)
                 (g : Y ⟶ A) : Set (o ⊔ ℓ) where

      field
        idx : A.Carrier
        map : InverseImageMap idx f g

      open InverseImageMap map public

    record SlExp≈ {f : X ⟶ A}
                  {g : Y ⟶ A}
                  (h i : SlExp f g) : Set (o ⊔ ℓ) where
      private
        module h = SlExp h
        module i = SlExp i

      field
        idx≈  : h.idx A.≈ i.idx
        map≈  : ∀ (img : InverseImage h.idx f) → InverseImage.x (h.f⇒g img) Y.≈ InverseImage.x (i.f⇒g (inverseImage-transport idx≈ img))
        -- map≈′ : ∀ (img : InverseImage i.idx f) → InverseImage.x (i.f⇒g img) Y.≈ InverseImage.x (h.f⇒g (inverseImage-transport idx≈ img))

  SlExp-Setoid : ∀ {A X Y : Setoid o ℓ}
                   (f : X ⟶ A) (g : Y ⟶ A) → Setoid (o ⊔ ℓ) (o ⊔ ℓ)
  SlExp-Setoid {A} {X} {Y} f g = record
    { Carrier       = SlExp f g
    ; _≈_           = SlExp≈
    ; isEquivalence = record
      { refl  = λ {h} → record
        { idx≈ = A.refl
        ; map≈ = λ img → SlExp.cong h img (inverseImage-transport A.refl img) X.refl
        }
      ; sym   = λ {h i} eq →
        let open SlExp≈ eq
        in record
        { idx≈ = A.sym idx≈
        ; map≈ = λ img → Y.trans (SlExp.cong i img (inverseImage-transport idx≈ (inverseImage-transport (A.sym idx≈) img)) X.refl)
                                 (Y.sym (map≈ (inverseImage-transport (A.sym idx≈) img)))
        }
      ; trans = λ {h i j} eq eq′ →
        let module eq = SlExp≈ eq
            module eq′ = SlExp≈ eq′
        in record
        { idx≈ = A.trans eq.idx≈ eq′.idx≈
        ; map≈ = λ img → Y.trans  (eq.map≈ img)
                         (Y.trans (eq′.map≈ (inverseImage-transport eq.idx≈ img))
                                  (SlExp.cong j (inverseImage-transport eq′.idx≈ (inverseImage-transport eq.idx≈ img))
                                                (inverseImage-transport (A.trans eq.idx≈ eq′.idx≈) img)
                                                X.refl))
        }
      }
    }
    where module A = Setoid A
          module X = Setoid X
          module Y = Setoid Y

module _ {o} where
  private
    S : Category (suc o) o o
    S = Setoids o o
    
    module S = Category S

    module _ (A : S.Obj) where
      private
        Sl = Slice S A
        module Sl = Category Sl

      open Setoid A
      open Prod (Slice S A)

      slice-terminal : Terminal Sl
      slice-terminal = record
        { ⊤        = sliceobj {Y = A} record
          { _⟨$⟩_ = λ x → x
          ; cong  = λ eq → eq
          }
        ; !        = λ { {sliceobj f} → slicearr {h = f} (Π.cong f) }
        ; !-unique = λ { {X} (slicearr △) eq →
                         let module X = SliceObj X
                         in sym (△ (Setoid.sym X.Y eq)) }
        }

      slice-product : (X Y : Sl.Obj) → Product X Y
      slice-product X Y = pullback⇒product S XY-pullback
        where module X = SliceObj X
              module Y = SliceObj Y

              F₀ : SpanObj → Setoid o o
              F₀ = λ { center → A
                     ; left   → X.Y
                     ; right  → Y.Y
                     }

              F : Functor (Category.op Span) (Setoids o o)
              F = record
                { F₀           = F₀
                ; F₁           = λ { span-id   → Func.id
                                   ; span-arrˡ → X.arr
                                   ; span-arrʳ → Y.arr
                                   }
                ; identity     = λ {Z} → S.Equiv.refl {F₀ Z} {F₀ Z} {Func.id}
                ; homomorphism = λ { {_} {_} {_} {span-id}   {span-id}   eq → eq
                                   ; {_} {_} {_} {span-id}   {span-arrˡ}    → Π.cong X.arr
                                   ; {_} {_} {_} {span-id}   {span-arrʳ}    → Π.cong Y.arr
                                   ; {_} {_} {_} {span-arrˡ} {span-id}      → Π.cong X.arr
                                   ; {_} {_} {_} {span-arrʳ} {span-id}      → Π.cong Y.arr
                                   }
                ; F-resp-≈     = λ { {_} {_} {span-id}   ≡.refl eq → eq
                                   ; {_} {_} {span-arrˡ} ≡.refl    → Π.cong X.arr
                                   ; {_} {_} {span-arrʳ} ≡.refl    → Π.cong Y.arr
                                   }
                }
              
              XY-pullback : Pullback S X.arr Y.arr
              XY-pullback = limit⇒pullback S {F = F} (Setoids-Complete 0ℓ 0ℓ 0ℓ o o F)

      module slice-terminal = Terminal slice-terminal
      module slice-product X Y = Product (slice-product X Y)

      _^_ : Sl.Obj → Sl.Obj → Sl.Obj
      f ^ g = sliceobj {Y = SlExp-Setoid g.arr f.arr} record
        { _⟨$⟩_ = SlExp.idx
        ; cong  = SlExp≈.idx≈
        }
        where module f = SliceObj f
              module g = SliceObj g

  --     slice-canonical : Canonical Sl
  --     slice-canonical = record
  --       { ⊤            = slice-terminal.⊤
  --       ; _×_          = slice-product.A×B
  --       ; !            = slice-terminal.!
  --       ; π₁           = slice-product.π₁ _ _
  --       ; π₂           = slice-product.π₂ _ _
  --       ; ⟨_,_⟩        = slice-product.⟨_,_⟩ _ _
  --       ; !-unique     = slice-terminal.!-unique
  --       ; π₁-comp      = λ {_ _ f _ g} → slice-product.project₁ _ _ {_} {f} {g}
  --       ; π₂-comp      = λ {_ _ f _ g} → slice-product.project₂ _ _ {_} {f} {g}
  --       ; ⟨,⟩-unique   = λ {_ _ _ f g h} → slice-product.unique _ _ {_} {h} {f} {g}
  --       ; _^_          = _^_
  --       ; eval         = {!!}
  --       ; curry        = {!!}
  --       ; eval-comp    = {!!}
  --       ; curry-resp-≈ = {!!}
  --       ; curry-unique = {!!}
  --       }

  -- --     Setoids-sliceCCC : CartesianClosed (Slice S A)
  -- --     Setoids-sliceCCC = Equivalence.fromCanonical (Slice S A) slice-canonical

  -- -- Setoids-LCCC : Locally S
  -- -- Setoids-LCCC = record
  -- --   { sliceCCC = Setoids-sliceCCC
  -- --   }

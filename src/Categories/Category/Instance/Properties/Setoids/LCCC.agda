{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Properties.Setoids.LCCC where

open import Level
open import Data.Product using (Σ; _,_)
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
open import Categories.Category.CartesianClosed.Locally using (Locally)
open import Categories.Category.Cartesian
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
        { ⊤             = sliceobj {Y = A} record
          { _⟨$⟩_ = λ x → x
          ; cong  = λ eq → eq
          }
        ; ⊤-is-terminal = record
          { !        = λ { {sliceobj f} → slicearr {h = f} (Π.cong f) }
          ; !-unique = λ { {X} (slicearr △) eq →
                         let module X = SliceObj X
                         in sym (△ (Setoid.sym X.Y eq)) }
          }
        }

      F₀ : Sl.Obj → Sl.Obj → SpanObj → Setoid o o
      F₀ X Y center = A
      F₀ X Y left   = SliceObj.Y X
      F₀ X Y right  = SliceObj.Y Y

      slice-product : (X Y : Sl.Obj) → Product X Y
      slice-product X Y = pullback⇒product S XY-pullback
        where module X = SliceObj X
              module Y = SliceObj Y

              F : Functor (Category.op Span) (Setoids o o)
              F = record
                { F₀           = F₀ X Y
                ; F₁           = λ { span-id   → Func.id
                                   ; span-arrˡ → X.arr
                                   ; span-arrʳ → Y.arr
                                   }
                ; identity     = λ {Z} → S.Equiv.refl {F₀ X Y Z} {F₀ X Y Z} {Func.id}
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

      cartesian : Cartesian Sl
      cartesian = record
        { terminal = slice-terminal
        ; products = record
          { product = slice-product _ _
          }
        }

      module cartesian = Cartesian cartesian

      _^_ : Sl.Obj → Sl.Obj → Sl.Obj
      f ^ g = sliceobj {Y = SlExp-Setoid g.arr f.arr} record
        { _⟨$⟩_ = SlExp.idx
        ; cong  = SlExp≈.idx≈
        }
        where module f = SliceObj f
              module g = SliceObj g

      prod = slice-product.A×B

      eval : {f g : Sl.Obj} → prod (f ^ g) g Sl.⇒ f
      eval {f} {g} = slicearr {h = h} λ { {J₁ , arr₁} {J₂ , arr₂} eq →
        let open SlExp (J₁ left)
        in trans (InverseImage.fx≈a (f⇒g (pack (J₁ right) _)))
          (trans (arr₁ span-arrˡ)
          (trans (eq center)
                 (sym (arr₂ span-arrʳ)))) }
        where module f  = SliceObj f
              module g  = SliceObj g
              module fY = Setoid f.Y

              h : SliceObj.Y (prod (f ^ g) g) S.⇒ f.Y
              h = record
                { _⟨$⟩_ = λ { (J , arr) →
                  let module exp = SlExp (J left)
                  in InverseImage.x (exp.f⇒g (pack (J right) (trans (arr span-arrʳ) (sym (arr span-arrˡ))))) }
                ; cong  = λ { {J₁ , arr₁} {J₂ , arr₂} eq →
                  let open SlExp≈ (eq left)
                      open SlExp (J₂ left)
                  in fY.trans (map≈ _) (cong _ _ (eq right)) }
                }

      module _ {f g : Sl.Obj} where
        private
          module f  = SliceObj f
          module g  = SliceObj g
          module fY = Setoid f.Y
          module gY = Setoid g.Y

        Jpb : ∀ x → InverseImage (f.arr ⟨$⟩ x) g.arr → ∀ j → Setoid.Carrier (F₀ f g j)
        Jpb x img center = f.arr ⟨$⟩ x
        Jpb x img left   = x
        Jpb x img right  = InverseImage.x img

        xypb : ∀ x → InverseImage (f.arr ⟨$⟩ x) g.arr → Setoid.Carrier (SliceObj.Y (prod f g))
        xypb x img = Jpb x img
                   , λ { {center} span-id → refl
                       ; {left} span-id   → fY.refl
                       ; {right} span-id  → gY.refl
                       ; span-arrˡ        → refl
                       ; span-arrʳ        → fx≈a }
          where open InverseImage img renaming (x to y)

        module _ {h : Sl.Obj} (α : prod f g Sl.⇒ h) where
          private
            module α  = Slice⇒ α
            module h  = SliceObj h
            module hY = Setoid h.Y

            βmap : fY.Carrier → SlExp g.arr h.arr
            βmap x = record
              { idx = f.arr ⟨$⟩ x
              ; map = record
                { f⇒g  = λ img →
                  let open InverseImage img renaming (x to y)
                  in pack (α.h ⟨$⟩ xypb x img)
                          (trans (α.△ {xypb x img} {xypb x img} (Setoid.refl (SliceObj.Y (prod f g)) {xypb x img}))
                                 fx≈a)
                ; cong = λ img img′ eq →
                  let module img  = InverseImage img
                      module img′ = InverseImage img′
                  in Π.cong α.h λ { center → refl
                                  ; left   → fY.refl
                                  ; right  → eq }
                }
              }

            βcong : {i j : fY.Carrier} → i fY.≈ j → SlExp≈ (βmap i) (βmap j)
            βcong {i} {j} eq = record
              { idx≈ = Π.cong f.arr eq
              ; map≈ = λ img →
                let open InverseImage img
                in Π.cong α.h λ { center → Π.cong f.arr eq
                                ; left   → eq
                                ; right  → gY.refl }
              }

            β : f.Y S.⇒ SliceObj.Y (h ^ g)
            β = record
              { _⟨$⟩_ = βmap
              ; cong  = βcong
              }

          curry : f Sl.⇒ (h ^ g)
          curry = slicearr {h = β} (Π.cong f.arr)

      module _ {f g h : Sl.Obj} {α β : prod f g Sl.⇒ h} where
        private
          module f  = SliceObj f
          module g  = SliceObj g
          module gY = Setoid g.Y

        curry-resp-≈ : α Sl.≈ β → curry α Sl.≈ curry β
        curry-resp-≈ eq eq′ = record
          { idx≈ = Π.cong f.arr eq′
          ; map≈ = λ img →
            let open InverseImage img
            in eq λ { center → Π.cong f.arr eq′
                    ; left   → eq′
                    ; right  → gY.refl }
          }

      module _ {f g h : Sl.Obj} {α : f Sl.⇒ (g ^ h)} {β : prod f h Sl.⇒ g} where
        private
          module f  = SliceObj f
          module g  = SliceObj g
          module h  = SliceObj h
          module α  = Slice⇒ α
          module β  = Slice⇒ β
          module fY = Setoid f.Y
          module gY = Setoid g.Y
          module hY = Setoid h.Y

        curry-unique : eval Sl.∘ (α cartesian.⁂ Sl.id) Sl.≈ β → α Sl.≈ curry β
        curry-unique eq {z} {w} eq′ = record
          { idx≈ = α.△ eq′
          ; map≈ = λ img →
            let open InverseImage img
            in gY.trans (InverseImageMap.cong (SlExp.map (α.h ⟨$⟩ z)) img _ hY.refl)
                        (eq {xypb z (inverseImage-transport (trans (α.△ eq′) (Π.cong f.arr (fY.sym eq′))) img)}
                            {xypb w (inverseImage-transport (α.△ eq′) img)}
                            λ { center → Π.cong f.arr eq′
                              ; left   → eq′
                              ; right  → hY.refl })
          }

      slice-canonical : Canonical Sl
      slice-canonical = record
        { ⊤            = slice-terminal.⊤
        ; _×_          = slice-product.A×B
        ; !            = slice-terminal.!
        ; π₁           = slice-product.π₁ _ _
        ; π₂           = slice-product.π₂ _ _
        ; ⟨_,_⟩        = slice-product.⟨_,_⟩ _ _
        ; !-unique     = slice-terminal.!-unique
        ; π₁-comp      = λ {_ _ f _ g} → slice-product.project₁ _ _ {_} {f} {g}
        ; π₂-comp      = λ {_ _ f _ g} → slice-product.project₂ _ _ {_} {f} {g}
        ; ⟨,⟩-unique   = λ {_ _ _ f g h} → slice-product.unique _ _ {_} {h} {f} {g}
        ; _^_          = _^_
        ; eval         = eval
        ; curry        = curry
        ; eval-comp    = λ { {_} {_} {_} {α} {J , arr₁} eq →
          let module α = Slice⇒ α
          in Π.cong α.h λ { center → trans (arr₁ span-arrˡ) (eq center)
                          ; left   → eq left
                          ; right  → eq right } }
        ; curry-resp-≈ = λ {_ _ _} {α β} → curry-resp-≈ {_} {_} {_} {α} {β}
        ; curry-unique = λ {_ _ _} {α β} → curry-unique {_} {_} {_} {α} {β}
        }

      Setoids-sliceCCC : CartesianClosed (Slice S A)
      Setoids-sliceCCC = Equivalence.fromCanonical (Slice S A) slice-canonical

  Setoids-LCCC : Locally S
  Setoids-LCCC = record
    { sliceCCC = Setoids-sliceCCC
    }

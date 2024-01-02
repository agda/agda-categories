{-# OPTIONS --without-K --safe #-}

module Categories.Category.Instance.Properties.Setoids.LCCC where

open import Level using (Level; _⊔_; 0ℓ; suc)
open import Data.Product using (_,_)
open import Function.Bundles using (Func; _⟨$⟩_)
import Function.Construct.Identity as FId
open import Relation.Binary using (Setoid)
import Relation.Binary.PropositionalEquality.Core as ≡
import  Relation.Binary.Reasoning.Setoid as SetoidR

open import Categories.Category.Core using (Category)
open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Category.CartesianClosed using (CartesianClosed)
open import Categories.Category.CartesianClosed.Canonical
  using (module Equivalence)
  renaming (CartesianClosed to Canonical)
open import Categories.Category.CartesianClosed.Locally using (Locally)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Instance.Span
  using (SpanObj; Span; span-id; left; right; span-arrʳ; span-arrˡ; center)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Instance.Properties.Setoids.Complete
  using (Setoids-Complete)
open import Categories.Category.Slice using (Slice; sliceobj; slicearr; SliceObj; Slice⇒)
open import Categories.Category.Slice.Properties using (pullback⇒product)
open import Categories.Functor.Core using (Functor)
open import Categories.Object.Terminal using (Terminal)
open import Categories.Diagram.Pullback using (Pullback)
open import Categories.Diagram.Pullback.Limit using (limit⇒pullback)
import Categories.Object.Product as Prod

module _ {o ℓ} where

  module _ {A X : Setoid o ℓ} where
    private
      module A = Setoid A
      module X = Setoid X

    record InverseImage (a : Setoid.Carrier A) (f : Func X A) : Set (o ⊔ ℓ) where
      constructor pack

      field
        x    : X.Carrier
        fx≈a : f ⟨$⟩ x A.≈ a

    inverseImage-transport : ∀ {a a′} {f : Func X A} → a A.≈ a′ → InverseImage a f → InverseImage a′ f
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
                           (f : Func X A)
                           (g : Func Y A) : Set (o ⊔ ℓ) where
      field
        f⇒g  : InverseImage a f → InverseImage a g
        cong : ∀ (x x′ : InverseImage a f) →
                 InverseImage.x x X.≈ InverseImage.x x′ →
                 InverseImage.x (f⇒g x) Y.≈ InverseImage.x (f⇒g x′)

    inverseImageMap-transport : ∀ {a a′} {f : Func X A} {g : Func Y A} → a A.≈ a′ →
                                  InverseImageMap a f g → InverseImageMap a′ f g
    inverseImageMap-transport eq h = record
      { f⇒g  = λ img → inverseImage-transport eq (f⇒g (inverseImage-transport (A.sym eq) img))
      ; cong = λ x x′ eq′ → cong (inverseImage-transport (A.sym eq) x) (inverseImage-transport (A.sym eq) x′) eq′
      }
      where open InverseImageMap h

    record SlExp (f : Func X A)
                 (g : Func Y A) : Set (o ⊔ ℓ) where

      field
        idx : A.Carrier
        map : InverseImageMap idx f g

      open InverseImageMap map public

    record SlExp≈ {f : Func X A}
                  {g : Func Y A}
                  (h i : SlExp f g) : Set (o ⊔ ℓ) where
      private
        module h = SlExp h
        module i = SlExp i

      field
        idx≈  : h.idx A.≈ i.idx
        map≈  : ∀ (img : InverseImage h.idx f) → InverseImage.x (h.f⇒g img) Y.≈ InverseImage.x (i.f⇒g (inverseImage-transport idx≈ img))
        -- map≈′ : ∀ (img : InverseImage i.idx f) → InverseImage.x (i.f⇒g img) Y.≈ InverseImage.x (h.f⇒g (inverseImage-transport idx≈ img))

  SlExp-Setoid : ∀ {A X Y : Setoid o ℓ}
                   (f : Func X A) (g : Func Y A) → Setoid (o ⊔ ℓ) (o ⊔ ℓ)
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
          { to = λ x → x
          ; cong  = λ eq → eq
          }
        ; ⊤-is-terminal = record
          { !        = λ { {sliceobj f} → slicearr {h = f} refl }
          ; !-unique = λ { {X} (slicearr △) →
                         let module X = SliceObj X
                         in sym △ }
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

              f : SpanObj → Setoid o o
              f = F₀ X Y
              F : Functor (Category.op Span) (Setoids o o)
              F = record
                { F₀           = f
                ; F₁           = λ { (span-id {B}) → FId.function (f B)
                                   ; span-arrˡ → X.arr
                                   ; span-arrʳ → Y.arr
                                   }
                ; identity     = λ {Z} → S.Equiv.refl {f Z} {f Z} {FId.function _}
                ; homomorphism = λ { {Z} {_} {_} {span-id}   {span-id}    → Setoid.refl (f Z)
                                   ; {_} {_} {_} {span-id}   {span-arrˡ}  → refl
                                   ; {_} {_} {_} {span-id}   {span-arrʳ}  → refl
                                   ; {_} {_} {_} {span-arrˡ} {span-id}    → refl
                                   ; {_} {_} {_} {span-arrʳ} {span-id}    → refl
                                   }
                ; F-resp-≈     = λ { {Z} {_} {span-id}   ≡.refl    → Setoid.refl (f Z)
                                   ; {_} {_} {span-arrˡ} ≡.refl    → refl
                                   ; {_} {_} {span-arrʳ} ≡.refl    → refl
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
      module products = BinaryProducts cartesian.products

      _^_ : Sl.Obj → Sl.Obj → Sl.Obj
      f ^ g = sliceobj {Y = SlExp-Setoid g.arr f.arr} record
        { to = SlExp.idx
        ; cong  = SlExp≈.idx≈
        }
        where module f = SliceObj f
              module g = SliceObj g

      prod = slice-product.A×B

      eval : {f g : Sl.Obj} → prod (f ^ g) g Sl.⇒ f
      eval {f} {g} = slicearr {h = h} λ { {J₁ , arr₁} →
        let open SlExp (J₁ left)
        in trans (InverseImage.fx≈a (f⇒g (pack (J₁ right) _)))
          (trans (arr₁ span-arrˡ)
          (sym (arr₁ span-arrʳ))) }
        where module f  = SliceObj f
              module g  = SliceObj g
              module fY = Setoid f.Y

              h : SliceObj.Y (prod (f ^ g) g) S.⇒ f.Y
              h = record
                { to = λ { (J , arr) →
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
                          (trans (α.△ {xypb x img})
                                 fx≈a)
                ; cong = λ img img′ eq →
                  let module img  = InverseImage img
                      module img′ = InverseImage img′
                  in Func.cong α.h λ { center → refl
                                  ; left   → fY.refl
                                  ; right  → eq }
                }
              }

            βcong : {i j : fY.Carrier} → i fY.≈ j → SlExp≈ (βmap i) (βmap j)
            βcong {i} {j} eq = record
              { idx≈ = Func.cong f.arr eq
              ; map≈ = λ img →
                let open InverseImage img
                in Func.cong α.h λ { center → Func.cong f.arr eq
                                ; left   → eq
                                ; right  → gY.refl }
              }

            β : f.Y S.⇒ SliceObj.Y (h ^ g)
            β = record
              { to = βmap
              ; cong  = βcong
              }

          curry : f Sl.⇒ (h ^ g)
          curry = slicearr {h = β} refl

      module _ {f g h : Sl.Obj} {α β : prod f g Sl.⇒ h} where
        private
          module f  = SliceObj f
          module g  = SliceObj g
          module h  = SliceObj h
          module gY = Setoid g.Y

        curry-resp-≈ : α Sl.≈ β → curry α Sl.≈ curry β
        curry-resp-≈ hα≈hβ {z} = record
          { idx≈ = refl
          ; map≈ = λ img →
            let open InverseImage img in
            let open SetoidR h.Y
            in begin
              InverseImage.x (SlExp.f⇒g (Slice⇒.h (curry α) ⟨$⟩ z) img) ≈⟨ hα≈hβ ⟩
              InverseImage.x (SlExp.f⇒g (Slice⇒.h (curry β) ⟨$⟩ z) img) ≈⟨ Func.cong (Slice⇒.h β) (
                λ { center → refl
                  ; left → Setoid.refl f.Y
                  ; right → gY.refl
                  }) ⟩
              InverseImage.x (SlExp.f⇒g (Slice⇒.h (curry β) ⟨$⟩ z) (inverseImage-transport refl img)) ∎
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

        curry-unique : eval Sl.∘ (α products.⁂ Sl.id) Sl.≈ β → α Sl.≈ curry β
        curry-unique eq {z} = record
          { idx≈ = α.△
          ; map≈ = λ img →
            let open InverseImage img
            in gY.trans (InverseImageMap.cong (SlExp.map (α.h ⟨$⟩ z)) img _ hY.refl)
                        (eq {xypb z (inverseImage-transport α.△  img)}
                            {-λ { center → Func.cong f.arr eq′
                              ; left   → eq′
                              ; right  → hY.refl }-})
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
        ; eval-comp    = λ { {_} {A1} {A2} {α} {J , arr₁} →
          let module α = Slice⇒ α
          in Func.cong α.h λ { center → arr₁ span-arrˡ
                             ; left → Setoid.refl (SliceObj.Y A2)
                             ; right → Setoid.refl (SliceObj.Y A1)
                             } }
        ; curry-unique = λ {_ _ _} {α β} → curry-unique {_} {_} {_} {α} {β}
        }

      Setoids-sliceCCC : CartesianClosed (Slice S A)
      Setoids-sliceCCC = Equivalence.fromCanonical (Slice S A) slice-canonical

  Setoids-LCCC : Locally S
  Setoids-LCCC = record
    { sliceCCC = Setoids-sliceCCC
    }

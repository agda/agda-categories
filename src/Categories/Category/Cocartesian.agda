{-# OPTIONS --without-K --safe #-}

open import Categories.Category

-- BinaryCoproducts -- a category with all binary coproducts
-- Cocartesian -- a category with all coproducts

-- since most of the work is dual to Categories.Category.Cartesian, so the idea
-- in this module is to make use of duality
module Categories.Category.Cocartesian {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level

private
  module 𝒞 = Category 𝒞
  open Category 𝒞
  open HomReasoning
  variable
    A B C D : Obj
    f g h i : A ⇒ B

open import Categories.Object.Initial 𝒞
open import Categories.Object.Coproduct 𝒞
open import Categories.Object.Duality 𝒞
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Symmetric
open import Categories.Category.Cartesian 𝒞.op
open import Categories.Morphism 𝒞
open import Categories.Morphism.Properties 𝒞
open import Categories.Morphism.Duality 𝒞
open import Categories.Morphism.Reasoning 𝒞

open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Properties
open import Categories.Functor.Bifunctor

record BinaryCoproducts : Set (levelOfTerm 𝒞) where

  infixr 6 _+_
  infixr 7 _+₁_

  field
    coproduct : ∀ {A B} → Coproduct A B

  module coproduct {A} {B} = Coproduct (coproduct {A} {B})

  _+_ : Obj → Obj → Obj
  A + B = coproduct.A+B {A} {B}

  open coproduct
    using (i₁; i₂; [_,_]; inject₁; inject₂; []-cong₂)
    renaming (unique to +-unique; η to +-η; g-η to +-g-η)
    public

  module Dual where
    op-binaryProducts : BinaryProducts
    op-binaryProducts = record { product = Coproduct⇒coProduct coproduct }
    
    module op-binaryProducts = BinaryProducts op-binaryProducts

  open Dual

  +-comm : A + B ≅ B + A
  +-comm = op-≅⇒≅ (op-binaryProducts.×-comm)

  +-assoc : A + B + C ≅ (A + B) + C
  +-assoc = op-≅⇒≅ (op-binaryProducts.×-assoc)

  _+₁_ : A ⇒ B → C ⇒ D → A + C ⇒ B + D
  _+₁_ = op-binaryProducts._⁂_

  open op-binaryProducts
    using ()
    renaming ( ⟨⟩-congʳ     to []-congʳ
             ; ⟨⟩-congˡ     to []-congˡ
             ; assocˡ       to +-assocʳ
             ; assocʳ       to +-assocˡ
             ; swap         to +-swap
             ; first        to +-first
             ; second       to +-second
             ; π₁∘⁂         to +₁∘i₁
             ; π₂∘⁂         to +₁∘i₂
             ; ⁂-cong₂      to +₁-cong₂
             ; ⁂∘⟨⟩         to []∘+₁
             ; ⁂∘⁂          to +₁∘+₁
             ; ⟨⟩∘          to ∘[]
             ; first↔second to +-second↔first
             ; swap∘⁂       to +₁∘+-swap
             ; swap∘swap    to +-swap∘swap
             )
    public

  -- since op-×- has type Bifunctor 𝒞.op 𝒞.op 𝒞.op,
  -- need to rewrap in order to type check
  -+- : Bifunctor 𝒞 𝒞 𝒞
  -+- = record
    { F₀           = op-×-.F₀
    ; F₁           = op-×-.F₁
    ; identity     = op-×-.identity
    ; homomorphism = op-×-.homomorphism
    ; F-resp-≈     = op-×-.F-resp-≈
    }
    where op-×- = op-binaryProducts.-×-
          module op-×- = Functor op-×-

  -+_ : Obj → Functor 𝒞 𝒞
  -+_ = appʳ -+-

  _+- : Obj → Functor 𝒞 𝒞
  _+- = appˡ -+-


record Cocartesian : Set (levelOfTerm 𝒞) where
  field
    initial    : Initial
    coproducts : BinaryCoproducts

  module initial    = Initial initial
  module coproducts = BinaryCoproducts coproducts

  open initial
    renaming (! to ¡; !-unique to ¡-unique; !-unique₂ to ¡-unique₂)
    public
  open coproducts hiding (module Dual) public

  module Dual where
    open coproducts.Dual public
    
    op-cartesian : Cartesian
    op-cartesian = record
      { terminal = ⊥⇒op⊤ initial
      ; products = op-binaryProducts
      }

    module op-cartesian = Cartesian op-cartesian

  open Dual

  ⊥+A≅A : ⊥ + A ≅ A
  ⊥+A≅A = op-≅⇒≅ (op-cartesian.⊤×A≅A)

  A+⊥≅A : A + ⊥ ≅ A
  A+⊥≅A = op-≅⇒≅ (op-cartesian.A×⊤≅A)

  open op-cartesian
    using ()
    -- both are natural isomorphism
    renaming (⊤×--id to ⊥+--id; -×⊤-id to -+⊥-id)
    public

  +-monoidal : Monoidal 𝒞
  +-monoidal = record
    { ⊗                    = -+-
    ; unit                 = unit
    ; unitorˡ              = ⊥+A≅A
    ; unitorʳ              = A+⊥≅A
    ; associator           = ≅.sym +-assoc
    ; unitorˡ-commute-from = ⟺ unitorˡ-commute-to
    ; unitorˡ-commute-to   = ⟺ unitorˡ-commute-from
    ; unitorʳ-commute-from = ⟺ unitorʳ-commute-to
    ; unitorʳ-commute-to   = ⟺ unitorʳ-commute-from
    ; assoc-commute-from   = ⟺ assoc-commute-to
    ; assoc-commute-to     = ⟺ assoc-commute-from
    -- the proof idea of triangle is that the opposite triangle is obtained for free,
    -- but notice that triangle and the opposite triangle form isomorphism.
    ; triangle             = λ {X Y} →
                               Iso-≈ triangle
                                     (Iso-∘ ([ X +- ]-resp-Iso (Iso-swap (iso ⊥+A≅A)))
                                            (iso +-assoc))
                                     ([ -+ Y ]-resp-Iso (Iso-swap (iso A+⊥≅A)))
    ; pentagon             = λ {X Y Z W} →
                               Iso-≈ pentagon
                                     (Iso-∘ ([ X +- ]-resp-Iso (iso +-assoc))
                                     (Iso-∘ (iso +-assoc)
                                            ([ -+ W ]-resp-Iso (iso +-assoc))))
                                     (Iso-∘ (iso +-assoc) (iso +-assoc))
    }
    where op-monoidal = op-cartesian.monoidal
          open Monoidal op-monoidal
          open _≅_

  module +-monoidal = Monoidal +-monoidal

  +-symmetric : Symmetric +-monoidal
  +-symmetric = record
    { braided     = record
      { braiding = record
        { F⇒G = record
          { η           = λ _ → +-swap
          ; commute     = λ _ → ⟺ +₁∘+-swap
          ; sym-commute = λ _ → +₁∘+-swap
          }
        ; F⇐G = record
          { η           = λ _ → +-swap
          ; commute     = λ _ → ⟺ +₁∘+-swap
          ; sym-commute = λ _ → +₁∘+-swap
          }
        ; iso = λ _ → iso +-comm
        }
      ; hexagon₁ = braided.hexagon₂
      ; hexagon₂ = braided.hexagon₁
      }
    ; commutative = commutative
    }
    where op-symmetric = op-cartesian.symmetric
          open Symmetric op-symmetric
          open _≅_

  -- we don't open this module publicly in order to prevent introducing conflicts
  -- with Cartesian category
  module +-symmetric = Symmetric +-symmetric

{-# OPTIONS --without-K --safe #-}
open import Categories.Category

module Categories.Category.CartesianClosed {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level
open import Function using (_$_; flip)
open import Data.Product using (Σ; _,_; uncurry)

open import Categories.Category.BinaryProducts 𝒞
open import Categories.Category.Cartesian 𝒞
open import Categories.Category.Cartesian.Monoidal using (module CartesianMonoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Bifunctor
open import Categories.NaturalTransformation hiding (id)
open import Categories.NaturalTransformation.Properties
open import Categories.Object.Product 𝒞
  hiding (repack≡id; repack∘; repack-cancel; up-to-iso; transport-by-iso)
open import Categories.Object.Terminal using (Terminal)
open import Categories.Morphism 𝒞
open import Categories.Morphism.Reasoning 𝒞

import Categories.Object.Exponential.Canonical as Exponentials

private
  module 𝒞 = Category 𝒞
  open Category 𝒞
  open HomReasoning
  open Equiv
  variable
    A B C   : Obj
    f g h i : A ⇒ B

-- Cartesian closed category
--   is a category with all products and exponentials
record CartesianClosed : Set (levelOfTerm 𝒞) where
  infixr 9 _^_
  -- an alternative notation for exponential, which emphasizes its internal hom natural
  infixr 5 _⇨_

  field
    cartesian : Cartesian

  open Exponentials cartesian hiding (repack)

  field
    exp       : Exponential A B

  private
    module exp {A B} = Exponential (exp {A} {B})

  _^_ : Obj → Obj → Obj
  B ^ A = exp.B^A {A} {B}

  _⇨_ : Obj → Obj → Obj
  _⇨_ = flip _^_

  private
    module cartesian = Cartesian cartesian

  open CartesianMonoidal cartesian using (A×⊤≅A)
  open Cartesian cartesian using (_×_; product; π₁; π₂; ⟨_,_⟩;
    project₁; project₂; η; ⟨⟩-cong₂; ⟨⟩∘; _×₁_; ⟨⟩-congˡ; ⟨⟩-congʳ; id×₁id;
    first∘first; firstid; first; second; first↔second; second∘second; ×₁-cong₂; -×_;
    ⊤; !; !-unique₂; ⊤-id)
    renaming (unique to ×-unique)

  open exp public renaming (η to η-exp)

  ⊤^A≅⊤ : ⊤ ^ A ≅ ⊤
  ⊤^A≅⊤ = record
    { from = !
    ; to   = λg !
    ; iso  = record
      { isoˡ = λ-unique′ !-unique₂
      ; isoʳ = ⊤-id _
      }
    }

  A^⊤≅A : A ^ ⊤ ≅ A
  A^⊤≅A = record
    { from = let open _≅_ A×⊤≅A in eval ∘ to
    ; to   = let open _≅_ A×⊤≅A in λg from
    ; iso  = record
      { isoˡ = λ-unique′ $ begin
        eval ∘ ((λg π₁ ∘ eval ∘ ⟨ id , ! ⟩) ×₁ id)           ≈˘⟨ refl⟩∘⟨ first∘first ⟩
        eval ∘ ((λg π₁ ×₁ id) ∘ ((eval ∘ ⟨ id , ! ⟩) ×₁ id)) ≈⟨ pullˡ β ⟩
        π₁ ∘ ((eval ∘ ⟨ id , ! ⟩) ×₁ id)                     ≈⟨ helper ⟩
        eval ∘ (id ×₁ id)                                    ∎
      ; isoʳ = firstid ! $ begin
        ((eval ∘ ⟨ id , ! ⟩) ∘ λg π₁) ×₁ id       ≈˘⟨ first∘first ⟩
        (eval ∘ ⟨ id , ! ⟩ ×₁ id) ∘ (λg π₁ ×₁ id) ≈⟨ helper′ ⟩∘⟨refl ⟩
        (⟨ id , ! ⟩ ∘ eval) ∘ (λg π₁ ×₁ id)       ≈⟨ pullʳ β ⟩
        ⟨ id , ! ⟩ ∘ π₁                           ≈⟨ ⟨⟩∘ ⟩
        ⟨ id ∘ π₁ , ! ∘ π₁ ⟩                      ≈⟨ ⟨⟩-cong₂ identityˡ !-unique₂ ⟩
        ⟨ π₁ , π₂ ⟩                               ≈⟨ η ⟩
        id                                        ∎
      }
    }
    where helper = begin
            π₁ ∘ ((eval ∘ ⟨ id , ! ⟩) ×₁ id) ≈⟨ project₁ ⟩
            (eval ∘ ⟨ id , ! ⟩) ∘ π₁         ≈⟨ pullʳ ⟨⟩∘ ⟩
            eval ∘ ⟨ id ∘ π₁ , ! ∘ π₁ ⟩      ≈⟨ refl⟩∘⟨ ⟨⟩-congˡ !-unique₂ ⟩
            eval ∘ (id ×₁ id)                ∎
          helper′ = let open _≅_ A×⊤≅A in begin
            (eval ∘ ⟨ id , ! ⟩) ×₁ id                       ≈⟨ introˡ isoˡ ⟩
            (⟨ id , ! ⟩ ∘ π₁) ∘ ((eval ∘ ⟨ id , ! ⟩) ×₁ id) ≈⟨ pullʳ helper ⟩
            ⟨ id , ! ⟩ ∘ (eval ∘ (id ×₁ id))                ≈⟨ refl⟩∘⟨ elimʳ id×₁id ⟩
            ⟨ id , ! ⟩ ∘ eval                               ∎

  -- we use -⇨- to represent the bifunctor.
  -- -^- would generate a bifunctor of type Bifunctor 𝒞 𝒞.op 𝒞 which is not very typical.
  -⇨- : Bifunctor 𝒞.op 𝒞 𝒞
  -⇨- = record
    { F₀           = uncurry _⇨_
    ; F₁           = λ where
      (f , g) → λg (g ∘ eval ∘ second f)
    ; identity     = λ-cong (identityˡ ○ (elimʳ id×₁id)) ○ η-id
    ; homomorphism = λ-unique′ helper
    ; F-resp-≈     = λ where
      (eq₁ , eq₂) → λ-cong (∘-resp-≈ eq₂ (∘-resp-≈ʳ (×₁-cong₂ refl eq₁)))
    }
    where helper : eval ∘ first (λg ((g ∘ f) ∘ eval ∘ second (h ∘ i)))
                 ≈ eval ∘ first (λg (g ∘ eval ∘ second i) ∘ λg (f ∘ eval ∘ second h))
          helper {g = g} {f = f} {h = h} {i = i} = begin
            eval ∘ first (λg ((g ∘ f) ∘ eval ∘ second (h ∘ i)))                        ≈⟨ β ⟩
            (g ∘ f) ∘ eval ∘ second (h ∘ i)                                            ≈˘⟨ refl⟩∘⟨ pullʳ second∘second ⟩
            (g ∘ f) ∘ (eval ∘ second h) ∘ second i                                     ≈⟨ center refl ⟩
            g ∘ (f ∘ eval ∘ second h) ∘ second i                                       ≈˘⟨ refl⟩∘⟨ pullˡ β ⟩
            g ∘ eval ∘ first (λg (f ∘ eval ∘ second h)) ∘ second i                     ≈⟨ refl⟩∘⟨ pushʳ first↔second ⟩
            g ∘ (eval ∘ second i) ∘ first (λg (f ∘ eval ∘ second h))                   ≈⟨ sym-assoc ⟩
            (g ∘ eval ∘ second i) ∘ first (λg (f ∘ eval ∘ second h))                   ≈˘⟨ pullˡ β ⟩
            eval ∘ first (λg (g ∘ eval ∘ second i)) ∘ first (λg (f ∘ eval ∘ second h)) ≈⟨ refl⟩∘⟨ first∘first ⟩
            eval ∘ first (λg (g ∘ eval ∘ second i) ∘ λg (f ∘ eval ∘ second h))         ∎

  _⇨- : Obj → Endofunctor 𝒞
  _⇨- = appˡ -⇨-

  -⇨_ : Obj → Functor 𝒞.op 𝒞
  -⇨_ = appʳ -⇨-

-- The cartesian closed structure induces a monoidal closed one:
-- 𝒞 is cartesian monoidal closed.

module CartesianMonoidalClosed (cartesianClosed : CartesianClosed) where
  open CartesianClosed cartesianClosed
  open CartesianMonoidal cartesian using (monoidal)
  open BinaryProducts (Cartesian.products cartesian)
    using (-×_; first; first∘first; second; first↔second; product; id×₁id)

  private
    A⇨[-×A] : Obj → Endofunctor 𝒞
    A⇨[-×A] A = A ⇨- ∘F -× A

    module A⇨[-×A] {A} = Functor (A⇨[-×A] A)

    [A⇨-]×A : Obj → Endofunctor 𝒞
    [A⇨-]×A A = -× A ∘F A ⇨-

    module [A⇨-]×A {A} = Functor ([A⇨-]×A A)

  closedMonoidal : Closed monoidal
  closedMonoidal = record
    { [-,-]   = -⇨-
    ; adjoint = λ {A} → record
      { unit   = ntHelper record
        { η       = λ _ → λg id
        ; commute = λ f → λ-unique′ $ begin
          eval ∘ first (λg id ∘ f)                     ≈˘⟨ refl⟩∘⟨ first∘first ⟩
          eval ∘ first (λg id) ∘ first f               ≈⟨ cancelˡ β ⟩
          first f                                      ≈˘⟨ cancelʳ β ⟩
          (first f ∘ eval) ∘ first (λg id)             ≈˘⟨ ∘-resp-≈ʳ (elimʳ (id×id product)) ⟩∘⟨refl ⟩
          (first f ∘ eval ∘ first id)  ∘ first (λg id) ≈˘⟨ pullˡ β ⟩
          eval ∘ first (A⇨[-×A].F₁ f) ∘ first (λg id)  ≈⟨ refl⟩∘⟨ first∘first ⟩
          eval ∘ first (A⇨[-×A].F₁ f ∘ λg id)          ∎
        }
      ; counit = ntHelper record
        { η       = λ _ → eval
        ; commute = λ f → begin
          eval ∘ [A⇨-]×A.F₁ f ≈⟨ β ⟩
          f ∘ eval ∘ first id ≈⟨ refl⟩∘⟨ elimʳ (id×id product) ⟩
          f ∘ eval            ∎
        }
      ; zig    = β
      ; zag    = λ-unique′ $ begin
        eval ∘ first (λg (eval ∘ eval ∘ second id) ∘ λg id)
          ≈˘⟨ refl⟩∘⟨ first∘first ⟩
        eval ∘ first (λg (eval ∘ eval ∘ second id)) ∘ first (λg id)
          ≈⟨ pullˡ β ⟩
        (eval ∘ eval ∘ second id) ∘ first (λg id)
          ≈⟨ ∘-resp-≈ʳ (elimʳ id×₁id) ⟩∘⟨refl ⟩
        (eval ∘ eval) ∘ first (λg id) 
          ≈⟨ cancelʳ β ⟩
        eval
          ≈˘⟨ elimʳ (id×id product) ⟩
        eval ∘ first id
          ∎
      }
    ; mate    = λ {X Y} f → record
      { commute₁ = λ-unique′ $ begin
        eval ∘ first (λg (second f ∘ eval ∘ second id) ∘ λg id)         ≈˘⟨ refl⟩∘⟨ first∘first ⟩
        eval ∘ first (λg (second f ∘ eval ∘ second id)) ∘ first (λg id) ≈⟨ pullˡ β ⟩
        (second f ∘ eval ∘ second id) ∘ first (λg id)                   ≈⟨ ∘-resp-≈ʳ (elimʳ (id×id product)) ⟩∘⟨refl ⟩
        (second f ∘ eval) ∘ first (λg id)                               ≈⟨ cancelʳ β ⟩
        second f                                                        ≈˘⟨ cancelˡ β ⟩
        eval ∘ first (λg id) ∘ second f                                 ≈⟨ pushʳ first↔second ⟩
        (eval ∘ second f) ∘ first (λg id)                               ≈˘⟨ identityˡ ⟩∘⟨refl ⟩
        (id ∘ eval ∘ second f) ∘ first (λg id)                          ≈˘⟨ pullˡ β ⟩
        eval ∘ first (λg (id ∘ eval ∘ second f)) ∘ first (λg id)        ≈⟨ refl⟩∘⟨ first∘first ⟩
        eval ∘ first (λg (id ∘ eval ∘ second f) ∘ λg id)                ∎
      ; commute₂ = begin
        eval ∘ first (λg (id ∘ eval ∘ second f)) ≈⟨ β ⟩
        id ∘ eval ∘ second f                     ≈⟨ identityˡ ⟩
        eval ∘ second f                          ∎
      }
    }

  open Closed closedMonoidal public

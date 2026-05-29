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
open import Categories.Object.Exponential 𝒞 hiding (repack)
open import Categories.Object.Terminal using (Terminal)
open import Categories.Morphism 𝒞
open import Categories.Morphism.Reasoning 𝒞

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
    exp       : Exponential A B

  module exp {A B} = Exponential (exp {A} {B})

  _^_ : Obj → Obj → Obj
  B ^ A = exp.B^A {A} {B}

  _⇨_ : Obj → Obj → Obj
  _⇨_ = flip _^_

  private
    module cartesian = Cartesian cartesian

  open CartesianMonoidal cartesian using (A×⊤≅A)
  open BinaryProducts cartesian.products using (_×_; product; π₁; π₂; ⟨_,_⟩;
    project₁; project₂; η; ⟨⟩-cong₂; ⟨⟩∘; _×₁_; ⟨⟩-congˡ; ⟨⟩-congʳ;
    first∘first; firstid; first; second; first↔second; second∘second; ×₁-cong₂; -×_)
  open Terminal cartesian.terminal using (⊤; !; !-unique₂; ⊤-id)

  B^A×A : ∀ B A → Product (B ^ A) A
  B^A×A B A = exp.product {A} {B}

  eval : Product.A×B (B^A×A B A) ⇒ B
  eval = exp.eval

  λg : C × A ⇒ B → C ⇒ B ^ A
  λg f = exp.λg product f

  λ-cong : f ≈ g → λg f ≈ λg g
  λ-cong eq = exp.λ-cong product eq

  λ-inj : λg f ≈ λg g → f ≈ g
  λ-inj = exp.λ-inj product

  _×id : (f : C ⇒ B ^ A) → C × A ⇒ [[ B^A×A B A ]]
  f ×id = [ product ⇒ exp.product ] f ×id

  β : eval ∘ λg f ×id ≈ f
  β = exp.β product

  subst : λg f ∘ g ≈ λg (f ∘ (g ×₁ id))
  subst = exp.subst product product

  η-exp : λg (eval ∘ f ×id) ≈ f
  η-exp = exp.η product

  λ-unique : eval ∘ f ×id ≈ g → f ≈ λg g
  λ-unique = exp.λ-unique product

  λ-unique₂ : eval ∘ f ×id ≈ eval ∘ g ×id → f ≈ g
  λ-unique₂ = exp.λ-unique′ product

  -- the annoying detail is that B^A×A is NOT the same as B ^ A × A, but they are isomorphic.
  -- make some infra so that the latter (which is more intuitive) can be used.

  B^A×A-iso : Product.A×B (B^A×A B A) ≅ B ^ A × A
  B^A×A-iso {B = B} {A = A} = record
    { from = repack exp.product product
    ; to   = repack product exp.product
    ; iso  = record
      { isoˡ = begin
        repack product exp.product ∘ repack exp.product product
          ≈⟨ [ exp.product ]⟨⟩∘ ⟩
        [ exp.product ]⟨ π₁ ∘ repack exp.product product , π₂ ∘ repack exp.product product ⟩
          ≈⟨ Product.⟨⟩-cong₂ exp.product project₁ project₂ ⟩
        [ exp.product ]⟨ [ exp.product ]π₁ , [ exp.product ]π₂ ⟩
          ≈⟨ Product.η exp.product ⟩
        id
          ∎
      ; isoʳ = begin
        repack exp.product product ∘ repack product exp.product
          ≈⟨ ⟨⟩∘ ⟩
        ⟨ [ exp.product ]π₁ ∘ repack product exp.product , [ exp.product ]π₂ ∘ repack product exp.product ⟩
          ≈⟨ ⟨⟩-cong₂ (Product.project₁ exp.product) (Product.project₂ exp.product) ⟩
        ⟨ π₁ , π₂ ⟩
          ≈⟨ η ⟩
        id
          ∎
      }
    }

  eval′ : B ^ A × A ⇒ B
  eval′ = eval ∘ to
    where open _≅_ B^A×A-iso

  λ-unique′ : eval′ ∘ (f ×₁ id) ≈ g → f ≈ λg g
  λ-unique′ eq = exp.λ-unique product (⟺ (pullʳ [ product ⇒ product ⇒ exp.product ]repack∘×) ○ eq)

  λ-unique₂′ : eval′ ∘ (f ×₁ id) ≈ eval′ ∘ (g ×₁ id) → f ≈ g
  λ-unique₂′ eq = (λ-unique′ eq) ○ ⟺ (λ-unique′ refl)

  β′ : eval′ ∘ (λg f ×₁ id) ≈ f
  β′ {f = f} = begin
    eval′ ∘ (λg f ×₁ id) ≈⟨ pullʳ [ product ⇒ product ⇒ exp.product ]repack∘× ⟩
    eval ∘ λg f ×id     ≈⟨ β ⟩
    f                   ∎

  η-exp′ : λg (eval′ ∘ (f ×₁ id)) ≈ f
  η-exp′ = sym (λ-unique′ refl)

  η-id′ : λg (eval′ {B = B} {A = A}) ≈ id
  η-id′ = sym (λ-unique′ (elimʳ (id×id product)))

  ⊤^A≅⊤ : ⊤ ^ A ≅ ⊤
  ⊤^A≅⊤ = record
    { from = !
    ; to   = λg !
    ; iso  = record
      { isoˡ = λ-unique₂ !-unique₂
      ; isoʳ = ⊤-id _
      }
    }

  A^⊤≅A : A ^ ⊤ ≅ A
  A^⊤≅A = record
    { from = let open _≅_ A×⊤≅A in eval′ ∘ to
    ; to   = let open _≅_ A×⊤≅A in λg from
    ; iso  = record
      { isoˡ = λ-unique₂′ $ begin
        eval′ ∘ ((λg π₁ ∘ eval′ ∘ ⟨ id , ! ⟩) ×₁ id)          ≈˘⟨ refl⟩∘⟨ first∘first ⟩
        eval′ ∘ ((λg π₁ ×₁ id) ∘ ((eval′ ∘ ⟨ id , ! ⟩) ×₁ id)) ≈⟨ pullˡ β′ ⟩
        π₁ ∘ ((eval′ ∘ ⟨ id , ! ⟩) ×₁ id)                     ≈⟨ helper ⟩
        eval′ ∘ (id ×₁ id)                                    ∎
      ; isoʳ = firstid ! $ begin
        ((eval′ ∘ ⟨ id , ! ⟩) ∘ λg π₁) ×₁ id                  ≈˘⟨ first∘first ⟩
        (eval′ ∘ ⟨ id , ! ⟩ ×₁ id) ∘ (λg π₁ ×₁ id)             ≈⟨ helper′ ⟩∘⟨refl ⟩
        (⟨ id , ! ⟩ ∘ eval′) ∘ (λg π₁ ×₁ id)                  ≈⟨ pullʳ β′ ⟩
        ⟨ id , ! ⟩ ∘ π₁                                      ≈⟨ ⟨⟩∘ ⟩
        ⟨ id ∘ π₁ , ! ∘ π₁ ⟩                                 ≈⟨ ⟨⟩-cong₂ identityˡ !-unique₂ ⟩
        ⟨ π₁ , π₂ ⟩                                          ≈⟨ η ⟩
        id                                                   ∎
      }
    }
    where helper = begin
            π₁ ∘ ((eval′ ∘ ⟨ id , ! ⟩) ×₁ id)                 ≈⟨ project₁ ⟩
            (eval′ ∘ ⟨ id , ! ⟩) ∘ π₁                        ≈⟨ pullʳ ⟨⟩∘ ⟩
            eval′ ∘ ⟨ id ∘ π₁ , ! ∘ π₁ ⟩                     ≈⟨ refl⟩∘⟨ ⟨⟩-congˡ !-unique₂ ⟩
            eval′ ∘ (id ×₁ id)                                ∎
          helper′ = let open _≅_ A×⊤≅A in begin
            (eval′ ∘ ⟨ id , ! ⟩) ×₁ id                        ≈⟨ introˡ isoˡ ⟩
            (⟨ id , ! ⟩ ∘ π₁) ∘ ((eval′ ∘ ⟨ id , ! ⟩) ×₁ id)  ≈⟨ pullʳ helper ⟩
            ⟨ id , ! ⟩ ∘ (eval′ ∘ (id ×₁ id))                 ≈⟨ refl⟩∘⟨ elimʳ (id×id product) ⟩
            ⟨ id , ! ⟩ ∘ eval′                               ∎

  -- we use -⇨- to represent the bifunctor.
  -- -^- would generate a bifunctor of type Bifunctor 𝒞 𝒞.op 𝒞 which is not very typical.
  -⇨- : Bifunctor 𝒞.op 𝒞 𝒞
  -⇨- = record
    { F₀           = uncurry _⇨_
    ; F₁           = λ where
      (f , g) → λg (g ∘ eval′ ∘ second f)
    ; identity     = λ-cong (identityˡ ○ (elimʳ (id×id product))) ○ η-id′
    ; homomorphism = λ-unique₂′ helper
    ; F-resp-≈     = λ where
      (eq₁ , eq₂) → λ-cong (∘-resp-≈ eq₂ (∘-resp-≈ʳ (×₁-cong₂ refl eq₁)))
    }
    where helper : eval′ ∘ first (λg ((g ∘ f) ∘ eval′ ∘ second (h ∘ i)))
                 ≈ eval′ ∘ first (λg (g ∘ eval′ ∘ second i) ∘ λg (f ∘ eval′ ∘ second h))
          helper {g = g} {f = f} {h = h} {i = i} = begin
            eval′ ∘ first (λg ((g ∘ f) ∘ eval′ ∘ second (h ∘ i)))                         ≈⟨ β′ ⟩
            (g ∘ f) ∘ eval′ ∘ second (h ∘ i)                                              ≈˘⟨ refl⟩∘⟨ pullʳ second∘second ⟩
            (g ∘ f) ∘ (eval′ ∘ second h) ∘ second i                                       ≈⟨ center refl ⟩
            g ∘ (f ∘ eval′ ∘ second h) ∘ second i                                         ≈˘⟨ refl⟩∘⟨ pullˡ β′ ⟩
            g ∘ eval′ ∘ first (λg (f ∘ eval′ ∘ second h)) ∘ second i                      ≈⟨ refl⟩∘⟨ pushʳ first↔second ⟩
            g ∘ (eval′ ∘ second i) ∘ first (λg (f ∘ eval′ ∘ second h))                    ≈⟨ sym-assoc ⟩
            (g ∘ eval′ ∘ second i) ∘ first (λg (f ∘ eval′ ∘ second h))                    ≈˘⟨ pullˡ β′ ⟩
            eval′ ∘ first (λg (g ∘ eval′ ∘ second i)) ∘ first (λg (f ∘ eval′ ∘ second h)) ≈⟨ refl⟩∘⟨ first∘first ⟩
            eval′ ∘ first (λg (g ∘ eval′ ∘ second i) ∘ λg (f ∘ eval′ ∘ second h))         ∎

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
    using (-×_; first; first∘first; second; first↔second; product)

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
        ; commute = λ f → λ-unique₂′ $ begin
          eval′ ∘ first (λg id ∘ f)                     ≈˘⟨ refl⟩∘⟨ first∘first ⟩
          eval′ ∘ first (λg id) ∘ first f               ≈⟨ cancelˡ β′ ⟩
          first f                                       ≈˘⟨ cancelʳ β′ ⟩
          (first f ∘ eval′)  ∘ first (λg id)            ≈˘⟨ ∘-resp-≈ʳ (elimʳ (id×id product)) ⟩∘⟨refl ⟩
          (first f ∘ eval′ ∘ first id)  ∘ first (λg id) ≈˘⟨ pullˡ β′ ⟩
          eval′ ∘ first (A⇨[-×A].F₁ f) ∘ first (λg id)  ≈⟨ refl⟩∘⟨ first∘first ⟩
          eval′ ∘ first (A⇨[-×A].F₁ f ∘ λg id)          ∎
        }
      ; counit = ntHelper record
        { η       = λ _ → eval′
        ; commute = λ f → begin
          eval′ ∘ [A⇨-]×A.F₁ f ≈⟨ β′ ⟩
          f ∘ eval′ ∘ first id ≈⟨ refl⟩∘⟨ elimʳ (id×id product) ⟩
          f ∘ eval′            ∎
        }
      ; zig    = β′
      ; zag    = λ-unique₂′ $ begin
        eval′ ∘ first (λg (eval′ ∘ eval′ ∘ second id) ∘ λg id)
                                        ≈˘⟨ refl⟩∘⟨ first∘first ⟩
        eval′ ∘ first (λg (eval′ ∘ eval′ ∘ second id)) ∘ first (λg id)
                                        ≈⟨ pullˡ β′ ⟩
        (eval′ ∘ eval′ ∘ second id) ∘ first (λg id)
                                        ≈⟨ ∘-resp-≈ʳ (elimʳ (id×id product)) ⟩∘⟨refl ⟩
        (eval′ ∘ eval′) ∘ first (λg id) ≈⟨ cancelʳ β′ ⟩
        eval′                           ≈˘⟨ elimʳ (id×id product) ⟩
        eval′ ∘ first id                ∎
      }
    ; mate    = λ {X Y} f → record
      { commute₁ = λ-unique₂′ $ begin
        eval′ ∘ first (λg (second f ∘ eval′ ∘ second id) ∘ λg id)         ≈˘⟨ refl⟩∘⟨ first∘first ⟩
        eval′ ∘ first (λg (second f ∘ eval′ ∘ second id)) ∘ first (λg id) ≈⟨ pullˡ β′ ⟩
        (second f ∘ eval′ ∘ second id) ∘ first (λg id)                    ≈⟨ ∘-resp-≈ʳ (elimʳ (id×id product)) ⟩∘⟨refl ⟩
        (second f ∘ eval′) ∘ first (λg id)                                ≈⟨ cancelʳ β′ ⟩
        second f                                                          ≈˘⟨ cancelˡ β′ ⟩
        eval′ ∘ first (λg id) ∘ second f                                  ≈⟨ pushʳ first↔second ⟩
        (eval′ ∘ second f) ∘ first (λg id)                                ≈˘⟨ identityˡ ⟩∘⟨refl ⟩
        (id ∘ eval′ ∘ second f) ∘ first (λg id)                           ≈˘⟨ pullˡ β′ ⟩
        eval′ ∘ first (λg (id ∘ eval′ ∘ second f)) ∘ first (λg id)        ≈⟨ refl⟩∘⟨ first∘first ⟩
        eval′ ∘ first (λg (id ∘ eval′ ∘ second f) ∘ λg id)                ∎
      ; commute₂ = begin
        eval′ ∘ first (λg (id ∘ eval′ ∘ second f)) ≈⟨ β′ ⟩
        id ∘ eval′ ∘ second f                      ≈⟨ identityˡ ⟩
        eval′ ∘ second f                           ∎
      }
    }

  open Closed closedMonoidal public

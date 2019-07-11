{-# OPTIONS --without-K --safe #-}
open import Categories.Category

module Categories.Category.CatesianClosed {o ℓ e} (𝒞 : Category o ℓ e) where

open Category 𝒞

open import Level
open import Function using (_$_)
open import Data.Product using (Σ; _,_; uncurry)

open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Bifunctor
open import Categories.Category.Catesian 𝒞
open import Categories.Object.Product 𝒞
  hiding (repack≡id; repack∘; repack-cancel; up-to-iso; transport-by-iso)
open import Categories.Object.Exponential 𝒞 hiding (repack)
open import Categories.Morphism 𝒞
open import Categories.Square 𝒞

open HomReasoning

private
  module 𝒞 = Category 𝒞
  variable
    A B C   : Obj
    f g h i : A ⇒ B

-- Catesian closed category
--   is a category with all products and exponentials
record CatesianClosed : Set (levelOf 𝒞) where
  infixl 7 _^_
  
  field
    catesian : Catesian
    exp      : Exponential A B

  module exp {A B} = Exponential (exp {A} {B})

  _^_ : Obj → Obj → Obj
  B ^ A = exp.B^A {A} {B}

  module catesian = Catesian catesian

  open catesian public

  B^A×A : ∀ B A → Product (B ^ A) A
  B^A×A B A = exp.product {A} {B}

  eval : Product.A×B (B^A×A B A) ⇒ B
  eval = exp.eval

  λg : C × A ⇒ B → C ⇒ B ^ A
  λg f = exp.λg product f

  λ-cong : f ≈ g → λg f ≈ λg g
  λ-cong eq = exp.λ-cong product eq

  _×id : (f : C ⇒ B ^ A) → C × A ⇒ [[ B^A×A B A ]]
  f ×id = [ product ⇒ exp.product ] f ×id

  β : eval ∘ λg f ×id ≈ f
  β = exp.β product

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

  λ-unique′ : eval′ ∘ (f ⁂ id) ≈ g → f ≈ λg g
  λ-unique′ eq = exp.λ-unique product (⟺ (pullʳ [ product ⇒ product ⇒ exp.product ]repack∘×) ○ eq)

  λ-unique₂′ : eval′ ∘ (f ⁂ id) ≈ eval′ ∘ (g ⁂ id) → f ≈ g
  λ-unique₂′ eq = (λ-unique′ eq) ○ ⟺ (λ-unique′ refl) 

  β′ : eval′ ∘ (λg f ⁂ id) ≈ f
  β′ {f = f} = begin
    eval′ ∘ (λg f ⁂ id) ≈⟨ pullʳ [ product ⇒ product ⇒ exp.product ]repack∘× ⟩
    eval ∘ λg f ×id     ≈⟨ β ⟩
    f                   ∎

  η-exp′ : λg (eval′ ∘ (f ⁂ id)) ≈ f
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
        eval′ ∘ ((λg π₁ ∘ eval′ ∘ ⟨ id , ! ⟩) ⁂ id)          ≈˘⟨ refl⟩∘⟨ first∘first ⟩
        eval′ ∘ ((λg π₁ ⁂ id) ∘ ((eval′ ∘ ⟨ id , ! ⟩) ⁂ id)) ≈⟨ pullˡ β′ ⟩
        π₁ ∘ ((eval′ ∘ ⟨ id , ! ⟩) ⁂ id)                     ≈⟨ helper ⟩
        eval′ ∘ (id ⁂ id)                                    ∎
      ; isoʳ = firstid ! $ begin
        ((eval′ ∘ ⟨ id , ! ⟩) ∘ λg π₁) ⁂ id                  ≈˘⟨ first∘first ⟩
        (eval′ ∘ ⟨ id , ! ⟩ ⁂ id) ∘ (λg π₁ ⁂ id)             ≈⟨ helper′ ⟩∘⟨refl ⟩
        (⟨ id , ! ⟩ ∘ eval′) ∘ (λg π₁ ⁂ id)                  ≈⟨ pullʳ β′ ⟩
        ⟨ id , ! ⟩ ∘ π₁                                      ≈⟨ ⟨⟩∘ ⟩
        ⟨ id ∘ π₁ , ! ∘ π₁ ⟩                                 ≈⟨ ⟨⟩-cong₂ identityˡ !-unique₂ ⟩
        ⟨ π₁ , π₂ ⟩                                          ≈⟨ η ⟩
        id                                                   ∎
      }
    }
    where helper = begin
            π₁ ∘ ((eval′ ∘ ⟨ id , ! ⟩) ⁂ id)                 ≈⟨ project₁ ⟩
            (eval′ ∘ ⟨ id , ! ⟩) ∘ π₁                        ≈⟨ pullʳ ⟨⟩∘ ⟩
            eval′ ∘ ⟨ id ∘ π₁ , ! ∘ π₁ ⟩                     ≈⟨ refl⟩∘⟨ ⟨⟩-congˡ !-unique₂ ⟩
            eval′ ∘ (id ⁂ id)                                ∎
          helper′ = let open _≅_ A×⊤≅A in begin
            (eval′ ∘ ⟨ id , ! ⟩) ⁂ id                        ≈⟨ introˡ isoˡ ⟩
            (⟨ id , ! ⟩ ∘ π₁) ∘ ((eval′ ∘ ⟨ id , ! ⟩) ⁂ id)  ≈⟨ pullʳ helper ⟩
            ⟨ id , ! ⟩ ∘ (eval′ ∘ (id ⁂ id))                 ≈⟨ refl⟩∘⟨ elimʳ (id×id product) ⟩
            ⟨ id , ! ⟩ ∘ eval′                               ∎

  -^- : Bifunctor 𝒞.op 𝒞 𝒞
  -^- = record
    { F₀           = λ where
      (A , B) → B ^ A
    ; F₁           = λ where
      (f , g) → λg (g ∘ eval′ ∘ second f)
    ; identity     = λ-cong (identityˡ ○ (elimʳ (id×id product))) ○ η-id′ 
    ; homomorphism = λ-unique₂′ helper
    ; F-resp-≈     = λ where
      (eq₁ , eq₂) → λ-cong (∘-resp-≈ eq₂ (∘-resp-≈ʳ (⁂-cong₂ refl eq₁)))
    }
    where helper : eval′ ∘ first (λg ((g ∘ f) ∘ eval′ ∘ second (h ∘ i)))
                 ≈ eval′ ∘ first (λg (g ∘ eval′ ∘ second i) ∘ λg (f ∘ eval′ ∘ second h))
          helper {g = g} {f = f} {h = h} {i = i} = begin
            eval′ ∘ first (λg ((g ∘ f) ∘ eval′ ∘ second (h ∘ i)))                         ≈⟨ β′ ⟩
            (g ∘ f) ∘ eval′ ∘ second (h ∘ i)                                              ≈˘⟨ refl⟩∘⟨ pullʳ second∘second ⟩
            (g ∘ f) ∘ (eval′ ∘ second h) ∘ second i                                       ≈˘⟨ pullˡ refl ⟩
            g ∘ f ∘ (eval′ ∘ second h) ∘ second i                                         ≈˘⟨ refl⟩∘⟨ assoc ⟩
            g ∘ (f ∘ eval′ ∘ second h) ∘ second i                                         ≈˘⟨ refl⟩∘⟨ pullˡ β′ ⟩
            g ∘ eval′ ∘ first (λg (f ∘ eval′ ∘ second h)) ∘ second i                      ≈⟨ refl⟩∘⟨ pushʳ first↔second ⟩
            g ∘ (eval′ ∘ second i) ∘ first (λg (f ∘ eval′ ∘ second h))                    ≈˘⟨ assoc ⟩
            (g ∘ eval′ ∘ second i) ∘ first (λg (f ∘ eval′ ∘ second h))                    ≈˘⟨ pullˡ β′ ⟩
            eval′ ∘ first (λg (g ∘ eval′ ∘ second i)) ∘ first (λg (f ∘ eval′ ∘ second h)) ≈⟨ refl⟩∘⟨ first∘first ⟩
            eval′ ∘ first (λg (g ∘ eval′ ∘ second i) ∘ λg (f ∘ eval′ ∘ second h))         ∎

  _^- : Obj → Endofunctor 𝒞
  _^- = appˡ -^-

  -^_ : Obj → Functor 𝒞.op 𝒞
  -^_ = appʳ -^-

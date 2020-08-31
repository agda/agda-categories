{-# OPTIONS --without-K --safe #-}
open import Categories.Category.Core using (Category)

module Categories.Diagram.Pullback {o ℓ e} (C : Category o ℓ e) where

open Category C
open HomReasoning
open Equiv

open import Level
open import Data.Product using (_,_; ∃)
open import Function using (flip; _$_) renaming (_∘_ to _●_)
open import Categories.Morphism C
open import Categories.Object.Product C hiding (up-to-iso; repack; repack∘; repack-cancel)
open import Categories.Diagram.Equalizer C hiding (up-to-iso)
open import Categories.Morphism.Reasoning C as Square
  renaming (glue to glue-square) hiding (id-unique)

private
  variable
    A B X Y Z : Obj
    f g h h₁ h₂ i i₁ i₂ j k : A ⇒ B

-- Pullback of two arrows with a common codomain
record Pullback (f : X ⇒ Z) (g : Y ⇒ Z) : Set (o ⊔ ℓ ⊔ e) where
  field
    {P} : Obj
    p₁  : P ⇒ X
    p₂  : P ⇒ Y

  field
    commute   : f ∘ p₁ ≈ g ∘ p₂
    universal : ∀ {h₁ : A ⇒ X} {h₂ : A ⇒ Y} → f ∘ h₁ ≈ g ∘ h₂ → A ⇒ P
    unique    : ∀ {eq : f ∘ h₁ ≈ g ∘ h₂} →
                  p₁ ∘ i ≈ h₁ → p₂ ∘ i ≈ h₂ →
                  i ≈ universal eq

    p₁∘universal≈h₁  : ∀ {eq : f ∘ h₁ ≈ g ∘ h₂} →
                         p₁ ∘ universal eq ≈ h₁
    p₂∘universal≈h₂  : ∀ {eq : f ∘ h₁ ≈ g ∘ h₂} →
                         p₂ ∘ universal eq ≈ h₂

  unique′ : (eq eq′ : f ∘ h₁ ≈ g ∘ h₂) → universal eq ≈ universal eq′
  unique′ eq eq′ = unique p₁∘universal≈h₁ p₂∘universal≈h₂

  id-unique : id ≈ universal commute
  id-unique = unique identityʳ identityʳ

  universal-resp-≈ : ∀ {eq : f ∘ h₁ ≈ g ∘ h₂} {eq′ : f ∘ i₁ ≈ g ∘ i₂} → h₁ ≈ i₁ → h₂ ≈ i₂ → universal eq ≈ universal eq′
  universal-resp-≈ h₁≈i₁ h₂≈i₂ = unique (p₁∘universal≈h₁ ○ h₁≈i₁) (p₂∘universal≈h₂ ○ h₂≈i₂)

  unique-diagram : p₁ ∘ h ≈ p₁ ∘ i →
                   p₂ ∘ h ≈ p₂ ∘ i →
                   h ≈ i
  unique-diagram {h = h} {i = i} eq₁ eq₂ = begin
    h            ≈⟨ unique eq₁ eq₂ ⟩
    universal eq ≈˘⟨ unique refl refl ⟩
    i            ∎
    where eq = extendʳ commute

up-to-iso : (pullback pullback′ : Pullback f g) → Pullback.P pullback ≅ Pullback.P pullback′
up-to-iso pullback pullback′ = record
  { from = repack pullback pullback′
  ; to = repack pullback′ pullback
  ; iso = record
    { isoˡ = repack-cancel pullback′ pullback
    ; isoʳ = repack-cancel pullback pullback′
    }
  }
  where
    open Pullback

    repack : (pullback pullback′ : Pullback f g) → P pullback ⇒ P pullback′
    repack pullback pullback′ = universal pullback′ (commute pullback)

    repack∘ : (pullback pullback′ pullback″ : Pullback f g) → repack pullback′ pullback″ ∘ repack pullback pullback′ ≈ repack pullback pullback″
    repack∘ pullback pullback′ pullback″ =
      unique pullback″
             (glueTrianglesʳ (p₁∘universal≈h₁ pullback″) (p₁∘universal≈h₁ pullback′))
             (glueTrianglesʳ (p₂∘universal≈h₂ pullback″) (p₂∘universal≈h₂ pullback′)) 

    repack-cancel : (pullback pullback′ : Pullback f g) → repack pullback pullback′ ∘ repack pullback′ pullback ≈ id
    repack-cancel pullback pullback′ = repack∘ pullback′ pullback pullback′ ○ ⟺ (id-unique pullback′)



swap : Pullback f g → Pullback g f
swap p = record
  { p₁              = p₂
  ; p₂              = p₁
  ; commute        = ⟺ commute
  ; universal       = universal ● ⟺
  ; unique          = flip unique
  ; p₁∘universal≈h₁ = p₂∘universal≈h₂
  ; p₂∘universal≈h₂ = p₁∘universal≈h₁
  }
  where open Pullback p

glue : (p : Pullback f g) → Pullback h (Pullback.p₁ p) → Pullback (f ∘ h) g
glue {h = h} p q = record
  { p₁              = q.p₁
  ; p₂              = p.p₂ ∘ q.p₂
  ; commute        = glue-square p.commute q.commute
  ; universal       = λ eq → q.universal (⟺ (p.p₁∘universal≈h₁ {eq = sym-assoc ○ eq}))
  ; unique          = λ {_ h₁ h₂ i} eq eq′ →
    q.unique eq (p.unique (begin
      p.p₁ ∘ q.p₂ ∘ i ≈˘⟨ extendʳ q.commute ⟩
      h ∘ q.p₁ ∘ i    ≈⟨ refl⟩∘⟨ eq ⟩
      h ∘ h₁          ∎)
                          (sym-assoc ○ eq′))
  ; p₁∘universal≈h₁ = q.p₁∘universal≈h₁
  ; p₂∘universal≈h₂ = assoc ○ ∘-resp-≈ʳ q.p₂∘universal≈h₂ ○ p.p₂∘universal≈h₂
  }
  where module p = Pullback p
        module q = Pullback q

unglue : (p : Pullback f g) → Pullback (f ∘ h) g → Pullback h (Pullback.p₁ p)
unglue {f = f} {g = g} {h = h} p q = record
  { p₁              = q.p₁
  ; p₂              = p₂′
  ; commute        = ⟺ p.p₁∘universal≈h₁
  ; universal       = λ {_ h₁ h₂} eq → q.universal $ begin
    (f ∘ h) ∘ h₁      ≈⟨ pullʳ eq ⟩
    f ∘ p.p₁ ∘ h₂     ≈⟨ extendʳ p.commute ⟩
    g ∘ p.p₂ ∘ h₂     ∎
  ; unique          = λ {_ h₁ h₂ i} eq eq′ → q.unique eq $ begin
  q.p₂ ∘ i            ≈⟨ pushˡ (⟺ p.p₂∘universal≈h₂) ⟩
  p.p₂ ∘ p₂′ ∘ i      ≈⟨ refl⟩∘⟨ eq′ ⟩
  p.p₂ ∘ h₂           ∎
  ; p₁∘universal≈h₁ = q.p₁∘universal≈h₁
  ; p₂∘universal≈h₂ = λ {_ _ _ eq} →
    p.unique-diagram ((pullˡ p.p₁∘universal≈h₁) ○ pullʳ q.p₁∘universal≈h₁ ○ eq)
                     (pullˡ p.p₂∘universal≈h₂ ○ q.p₂∘universal≈h₂)
  }
  where module p = Pullback p
        module q = Pullback q
        p₂′ = p.universal (sym-assoc ○ q.commute) -- used twice above

Product×Equalizer⇒Pullback :
  (p : Product A B) → Equalizer (f ∘ Product.π₁ p) (g ∘ Product.π₂ p) →
  Pullback f g
Product×Equalizer⇒Pullback {f = f} {g = g} p e = record
  { p₁              = π₁ ∘ arr
  ; p₂              = π₂ ∘ arr
  ; commute         = sym-assoc ○ equality ○ assoc
  ; universal       = λ {_ h₁ h₂} eq → equalize $ begin
    (f ∘ π₁) ∘ ⟨ h₁ , h₂ ⟩ ≈⟨ pullʳ project₁ ⟩
    f ∘ h₁                ≈⟨ eq ⟩
    g ∘ h₂                ≈˘⟨ pullʳ project₂ ⟩
    (g ∘ π₂) ∘ ⟨ h₁ , h₂ ⟩ ∎
  ; unique          = λ eq eq′ → e.unique (p.unique (sym-assoc ○ eq) (sym-assoc ○ eq′))
  ; p₁∘universal≈h₁ = pullʳ (⟺ e.universal) ○ project₁
  ; p₂∘universal≈h₂ = pullʳ (⟺ e.universal) ○ project₂
  }
  where module p = Product p
        module e = Equalizer e
        open p
        open e

Product×Pullback⇒Equalizer : (p : Product A B) → Pullback f g →
  Equalizer (f ∘ Product.π₁ p) (g ∘ Product.π₂ p)
Product×Pullback⇒Equalizer {f = f} {g = g} p pu = record
  { arr       = ⟨ p₁ , p₂ ⟩
  ; equality  = begin
    (f ∘ π₁) ∘ ⟨ p₁ , p₂ ⟩ ≈⟨ pullʳ project₁ ⟩
    f ∘ p₁                 ≈⟨ commute ⟩
    g ∘ p₂                 ≈˘⟨ pullʳ project₂ ⟩
    (g ∘ π₂) ∘ ⟨ p₁ , p₂ ⟩ ∎
  ; equalize  = λ eq → pu.universal (sym-assoc ○ eq ○ assoc)
  ; universal = λ {_ h} → begin
    h                      ≈˘⟨ p.unique (⟺ p₁∘universal≈h₁) (⟺ p₂∘universal≈h₂) ⟩
    ⟨ p₁ ∘ _ , p₂ ∘ _ ⟩    ≈⟨ p.unique (pullˡ project₁) (pullˡ project₂) ⟩
    ⟨ p₁ , p₂ ⟩ ∘ _        ∎
  ; unique    = λ eq → pu.unique (pushˡ (⟺ project₁) ○ ⟺ (∘-resp-≈ʳ eq))
                                 (pushˡ (⟺ project₂) ○ ⟺ (∘-resp-≈ʳ eq))
  }
  where module p = Product p
        module pu = Pullback pu
        open p
        open pu

module _ (p : Pullback f g) where
  open Pullback p

  Pullback-resp-≈ : h ≈ f → i ≈ g → Pullback h i
  Pullback-resp-≈ eq eq′ = record
    { p₁              = p₁
    ; p₂              = p₂
    ; commute         = ∘-resp-≈ˡ eq ○ commute ○ ⟺ (∘-resp-≈ˡ eq′)
    ; universal       = λ eq″ → universal (∘-resp-≈ˡ (⟺ eq) ○ eq″ ○ ∘-resp-≈ˡ eq′)
    ; unique          = unique
    ; p₁∘universal≈h₁ = p₁∘universal≈h₁
    ; p₂∘universal≈h₂ = p₂∘universal≈h₂
    }

  Pullback-resp-Mono : Mono g → Mono p₁
  Pullback-resp-Mono mg h i eq = unique-diagram eq (mg _ _ eq′)
    where eq′ : g ∘ p₂ ∘ h ≈ g ∘ p₂ ∘ i
          eq′ = begin
            g ∘ p₂ ∘ h ≈⟨ extendʳ (sym commute) ⟩
            f ∘ p₁ ∘ h ≈⟨ refl⟩∘⟨ eq ⟩
            f ∘ p₁ ∘ i ≈⟨ extendʳ commute ⟩
            g ∘ p₂ ∘ i ∎

  Pullback-resp-Iso : Iso g h → ∃ λ i → Iso p₁ i
  Pullback-resp-Iso {h = h} iso = universal eq
                                , record
                                { isoˡ = unique-diagram eq₁ eq₂
                                ; isoʳ = p₁∘universal≈h₁
                                }
    where open Iso iso
          eq = begin
            f ∘ id                 ≈⟨ introˡ refl ⟩
            id ∘ f ∘ id            ≈⟨ pushˡ (⟺ isoʳ) ⟩
            g ∘ h ∘ f ∘ id         ∎
          eq₁ = begin
            p₁ ∘ universal eq ∘ p₁ ≈⟨ cancelˡ p₁∘universal≈h₁ ⟩
            p₁                     ≈˘⟨ identityʳ ⟩
            p₁ ∘ id                ∎
          eq₂ = begin
            p₂ ∘ universal eq ∘ p₁ ≈⟨ extendʳ p₂∘universal≈h₂ ⟩
            h ∘ (f ∘ id) ∘ p₁      ≈⟨ refl ⟩∘⟨ identityʳ ⟩∘⟨ refl ⟩
            h ∘ f ∘ p₁             ≈⟨ refl ⟩∘⟨ commute ⟩
            h ∘ g ∘ p₂             ≈⟨ cancelˡ isoˡ ⟩
            p₂                     ≈˘⟨ identityʳ ⟩
            p₂ ∘ id                ∎

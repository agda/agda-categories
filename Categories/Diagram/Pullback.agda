{-# OPTIONS --without-K --safe #-}
open import Categories.Category

module Categories.Diagram.Pullback {o ℓ e} (C : Category o ℓ e) where

open Category C hiding (id-unique)
open HomReasoning

open import Level
open import Data.Product using (_,_; ∃)
open import Function using (flip; _$_)
open import Categories.Morphism C
open import Categories.Object.Product C
open import Categories.Diagram.Equalizer C
open import Categories.Square C as Square renaming (glue to glue-square)

private
  variable
    A B X Y Z : Obj
    f g h h₁ h₂ i i₁ i₂ j : A ⇒ B

record Pullback (f : X ⇒ Z)(g : Y ⇒ Z) : Set (o ⊔ ℓ ⊔ e) where
  field
    {P} : Obj
    p₁  : P ⇒ X
    p₂  : P ⇒ Y

  field
    commutes  : f ∘ p₁ ≈ g ∘ p₂
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

  id-unique : id ≈ universal commutes
  id-unique = unique identityʳ identityʳ

  unique-diagram : p₁ ∘ h ≈ p₁ ∘ i →
                   p₂ ∘ h ≈ p₂ ∘ i →
                   h ≈ i
  unique-diagram {h = h} {i = i} eq₁ eq₂ = begin
    h            ≈⟨ unique eq₁ eq₂ ⟩
    universal eq ≈˘⟨ unique refl refl ⟩
    i            ∎
    where eq = extendʳ commutes

swap : Pullback f g → Pullback g f
swap p = record
  { p₁              = p₂
  ; p₂              = p₁
  ; commutes        = sym commutes
  ; universal       = λ eq → universal (sym eq)
  ; unique          = flip unique
  ; p₁∘universal≈h₁ = p₂∘universal≈h₂
  ; p₂∘universal≈h₂ = p₁∘universal≈h₁
  }
  where open Pullback p

glue : (p : Pullback f g) → Pullback h (Pullback.p₁ p) → Pullback (f ∘ h) g
glue {h = h} p q = record
  { p₁              = q.p₁
  ; p₂              = p.p₂ ∘ q.p₂
  ; commutes        = glue-square p.commutes q.commutes
  ; universal       = λ eq → q.universal (sym (p.p₁∘universal≈h₁ {eq = trans (sym assoc) eq}))
  ; unique          = λ {_ h₁ h₂ i} eq eq′ →
    q.unique eq (p.unique (begin
      p.p₁ ∘ q.p₂ ∘ i ≈˘⟨ extendʳ q.commutes ⟩
      h ∘ q.p₁ ∘ i    ≈⟨ refl⟩∘⟨ eq ⟩
      h ∘ h₁          ∎)
                          (trans (sym assoc) eq′))
  ; p₁∘universal≈h₁ = q.p₁∘universal≈h₁
  ; p₂∘universal≈h₂ = trans assoc (trans (∘-resp-≈ʳ q.p₂∘universal≈h₂) p.p₂∘universal≈h₂)
  }
  where module p = Pullback p
        module q = Pullback q

unglue : (p : Pullback f g) → Pullback (f ∘ h) g → Pullback h (Pullback.p₁ p)
unglue {f = f} {g = g} {h = h} p q = record
  { p₁              = q.p₁
  ; p₂              = p₂′
  ; commutes        = sym p.p₁∘universal≈h₁
  ; universal       = λ {_ h₁ h₂} eq → q.universal $ begin
    (f ∘ h) ∘ h₁      ≈⟨ pullʳ eq ⟩
    f ∘ p.p₁ ∘ h₂     ≈⟨ extendʳ p.commutes ⟩
    g ∘ p.p₂ ∘ h₂     ∎
  ; unique          = λ {_ h₁ h₂ i} eq eq′ → q.unique eq $ begin
  q.p₂ ∘ i            ≈⟨ pushˡ (sym p.p₂∘universal≈h₂) ⟩
  p.p₂ ∘ p₂′ ∘ i      ≈⟨ refl⟩∘⟨ eq′ ⟩
  p.p₂ ∘ h₂           ∎
  ; p₁∘universal≈h₁ = q.p₁∘universal≈h₁
  ; p₂∘universal≈h₂ = λ {_ _ _ eq} →
    p.unique-diagram (trans (pullˡ p.p₁∘universal≈h₁)
                            (trans (pullʳ q.p₁∘universal≈h₁) eq))
                     (trans (pullˡ p.p₂∘universal≈h₂) q.p₂∘universal≈h₂)
  }
  where module p = Pullback p
        module q = Pullback q
        p₂′ = p.universal (trans (sym assoc) q.commutes)

Product×Equalizer⇒Pullback :
  (p : Product A B) → Equalizer (f ∘ Product.π₁ p) (g ∘ Product.π₂ p) →
  Pullback f g
Product×Equalizer⇒Pullback {f = f} {g = g} p e = record
  { p₁              = π₁ ∘ arr
  ; p₂              = π₂ ∘ arr
  ; commutes        = trans (sym assoc) (trans equality assoc)
  ; universal       = λ {_ h₁ h₂} eq → equalize $ begin
    (f ∘ π₁) ∘ ⟨ h₁ , h₂ ⟩ ≈⟨ pullʳ commute₁ ⟩
    f ∘ h₁                 ≈⟨ eq ⟩
    g ∘ h₂                 ≈˘⟨ pullʳ commute₂ ⟩
    (g ∘ π₂) ∘ ⟨ h₁ , h₂ ⟩ ∎
  ; unique          = λ eq eq′ → e.unique (p.unique (trans (sym assoc) eq)
                                                    (trans (sym assoc) eq′))
  ; p₁∘universal≈h₁ = trans (pullʳ (sym e.universal)) commute₁
  ; p₂∘universal≈h₂ = trans (pullʳ (sym e.universal)) commute₂
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
    (f ∘ π₁) ∘ ⟨ p₁ , p₂ ⟩ ≈⟨ pullʳ commute₁ ⟩
    f ∘ p₁                 ≈⟨ commutes ⟩
    g ∘ p₂                 ≈˘⟨ pullʳ commute₂ ⟩
    (g ∘ π₂) ∘ ⟨ p₁ , p₂ ⟩ ∎
  ; equalize  = λ eq → pu.universal (trans (sym assoc) (trans eq assoc))
  ; universal = λ {_ h} → begin
    h                      ≈˘⟨ p.unique (sym p₁∘universal≈h₁) (sym p₂∘universal≈h₂) ⟩
    ⟨ p₁ ∘ _ , p₂ ∘ _ ⟩    ≈⟨ p.unique (pullˡ commute₁)
                                          (pullˡ commute₂) ⟩
    ⟨ p₁ , p₂ ⟩ ∘ _        ∎
  ; unique    = λ eq → pu.unique (trans (pushˡ (sym commute₁)) (sym (∘-resp-≈ʳ eq)))
                                 (trans (pushˡ (sym commute₂)) (sym (∘-resp-≈ʳ eq)))
  }
  where module p = Product p
        module pu = Pullback pu
        open p
        open pu

module _ (p : Pullback f g) where
  open Pullback p

  Pullback-resp-Mono : Mono g → Mono p₁
  Pullback-resp-Mono mg h i eq = unique-diagram eq (mg _ _ eq′)
    where eq′ : g ∘ p₂ ∘ h ≈ g ∘ p₂ ∘ i
          eq′ = begin
            g ∘ p₂ ∘ h ≈⟨ extendʳ (sym commutes) ⟩
            f ∘ p₁ ∘ h ≈⟨ refl⟩∘⟨ eq ⟩
            f ∘ p₁ ∘ i ≈⟨ extendʳ commutes ⟩
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
            id ∘ f ∘ id            ≈⟨ pushˡ (sym isoʳ) ⟩
            g ∘ h ∘ f ∘ id         ∎
          eq₁ = begin
            p₁ ∘ universal eq ∘ p₁ ≈⟨ cancelˡ p₁∘universal≈h₁ ⟩
            p₁                     ≈˘⟨ identityʳ ⟩
            p₁ ∘ id                ∎
          eq₂ = begin
            p₂ ∘ universal eq ∘ p₁ ≈⟨ extendʳ p₂∘universal≈h₂ ⟩
            h ∘ (f ∘ id) ∘ p₁      ≈⟨ refl ⟩∘⟨ identityʳ ⟩∘⟨ refl ⟩
            h ∘ f ∘ p₁             ≈⟨ refl ⟩∘⟨ commutes ⟩
            h ∘ g ∘ p₂             ≈⟨ cancelˡ isoˡ ⟩
            p₂                     ≈˘⟨ identityʳ ⟩
            p₂ ∘ id                ∎

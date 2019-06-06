{-# OPTIONS --without-K --safe #-}
open import Categories.Category

module Categories.Diagram.Pullback {o ℓ e} (C : Category o ℓ e) where

open Category C
open HomReasoning

open import Level
open import Function using (flip; _$_)
open import Categories.Morphism C
open import Categories.Square C as Square renaming (glue to glue-square)

private
  variable
    A B X Y Z : Obj
    f g h h₁ h₂ i j : A ⇒ B

record Pullback (f : X ⇒ Z)(g : Y ⇒ Z) : Set (o ⊔ ℓ ⊔ e) where
  field
    {P} : Obj
    p₁  : P ⇒ X
    p₂  : P ⇒ Y

  field
    commutes  : f ∘ p₁ ≈ g ∘ p₂
    universal : f ∘ h₁ ≈ g ∘ h₂ → A ⇒ P
    unique    : ∀ {eq : f ∘ h₁ ≈ g ∘ h₂} →
                  p₁ ∘ i ≈ h₁ → p₂ ∘ i ≈ h₂ →
                  i ≈ universal eq

    p₁∘universal≈h₁  : ∀ {eq : f ∘ h₁ ≈ g ∘ h₂} →
                         p₁ ∘ universal eq ≈ h₁
    p₂∘universal≈h₂  : ∀ {eq : f ∘ h₁ ≈ g ∘ h₂} →
                         p₂ ∘ universal eq ≈ h₂

  unique′ : (eq eq′ : f ∘ h₁ ≈ g ∘ h₂) → universal eq ≈ universal eq′
  unique′ eq eq′ = unique p₁∘universal≈h₁ p₂∘universal≈h₂


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
  ; p₂∘universal≈h₂ = λ {_ h₁ h₂ eq} →
  let eq′ : f ∘ h ∘ h₁ ≈ g ∘ p.p₂ ∘ h₂
      eq′ = begin
        f ∘ h ∘ h₁    ≈⟨ refl⟩∘⟨ eq ⟩
        f ∘ p.p₁ ∘ h₂ ≈⟨ extendʳ p.commutes ⟩
        g ∘ p.p₂ ∘ h₂ ∎
  in begin
    p₂′ ∘ _           ≈⟨ p.unique (trans (pullˡ p.p₁∘universal≈h₁) (pullʳ q.p₁∘universal≈h₁))
                                  (trans (pullˡ p.p₂∘universal≈h₂) q.p₂∘universal≈h₂) ⟩
    p.universal eq′   ≈˘⟨ p.unique (sym eq) refl ⟩
    h₂                ∎
  }
  where module p = Pullback p
        module q = Pullback q
        p₂′ = p.universal (trans (sym assoc) q.commutes)

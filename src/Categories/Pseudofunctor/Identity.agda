{-# OPTIONS --without-K --safe #-}

-- The identity pseudofunctor

module Categories.Pseudofunctor.Identity where

open import Data.Product using (_,_)

open import Categories.Bicategory using (Bicategory)
import Categories.Bicategory.Extras as BicategoryExt
open import Categories.Category using (Category)
open import Categories.Category.Instance.One using (shift)
open import Categories.Category.Product using (_×₁_)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
import Categories.Morphism.Reasoning as MorphismReasoning
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (NaturalIsomorphism; _≃_; niHelper)
open import Categories.Pseudofunctor using (Pseudofunctor)

open Category using (module HomReasoning)
open NaturalIsomorphism using (F⇒G; F⇐G)

-- The identity pseudofunctor

idP : ∀ {o ℓ e t} {C : Bicategory o ℓ e t} → Pseudofunctor C C
idP {o} {ℓ} {e} {t} {C = C} = record
  { P₀             = λ x → x
  ; P₁             = idF
  ; P-identity     = P-identity
  ; P-homomorphism = P-homomorphism
  ; unitaryˡ       = unitaryˡ
  ; unitaryʳ       = unitaryʳ
  ; assoc          = assoc
  }
  where
    open BicategoryExt C

    P-identity : ∀ {x} → id {x} ∘F shift o ℓ e ≃ idF ∘F id
    P-identity {x} = niHelper (record
      { η       = λ _ → id₂
      ; η⁻¹     = λ _ → id₂
      ; commute = λ _ → MorphismReasoning.id-comm-sym (hom x x)
      ; iso     = λ _ → record { isoˡ = hom.identity² ; isoʳ = hom.identity² }
      })

    P-homomorphism : ∀ {x y z} → ⊚ ∘F (idF ×₁ idF) ≃ idF ∘F ⊚ {x} {y} {z}
    P-homomorphism {x} {_} {z} = niHelper (record
      { η       = λ _ → id₂
      ; η⁻¹     = λ _ → id₂
      ; commute = λ _ → MorphismReasoning.id-comm-sym (hom x z)
      ; iso     = λ _ → record { isoˡ = hom.identity² ; isoʳ = hom.identity² }
      })

    Pid  = λ {A} → NaturalTransformation.η (F⇒G (P-identity {A})) _
    Phom = λ {x} {y} {z} f,g →
           NaturalTransformation.η (F⇒G (P-homomorphism {x} {y} {z})) f,g
    λ⇒   = unitorˡ.from
    ρ⇒   = unitorʳ.from
    α⇒   = associator.from

    unitaryˡ : ∀ {x y} {f : x ⇒₁ y} →
               let open ComHom in
               [ id₁ ⊚₀ f ⇒ f ]⟨
                 Pid ⊚₁ id₂      ⇒⟨ id₁ ⊚₀ f ⟩
                 Phom (id₁ , f)  ⇒⟨ id₁ ⊚₀ f ⟩
                 λ⇒
               ≈ λ⇒
               ⟩
    unitaryˡ {x} {y} {f} = begin
      λ⇒ ∘ᵥ Phom (id₁ , f) ∘ᵥ (Pid ⊚₁ id₂)  ≈⟨ refl⟩∘⟨ elimʳ ⊚.identity ⟩
      λ⇒ ∘ᵥ Phom (id₁ , f)                  ≈⟨ hom.identityʳ ⟩
      λ⇒                                    ∎
      where
        open HomReasoning (hom x y)
        open MorphismReasoning (hom x y)

    unitaryʳ : ∀ {x y} {f : x ⇒₁ y} →
               let open ComHom in
               [ f ⊚₀ id₁ ⇒ f ]⟨
                 id₂ ⊚₁ Pid      ⇒⟨ f ⊚₀ id₁ ⟩
                 Phom (f , id₁)  ⇒⟨ f ⊚₀ id₁ ⟩
                 ρ⇒
               ≈ ρ⇒
               ⟩
    unitaryʳ {x} {y} {f} = begin
      ρ⇒ ∘ᵥ Phom (f , id₁) ∘ᵥ (id₂ ⊚₁ Pid)  ≈⟨ refl⟩∘⟨ elimʳ ⊚.identity ⟩
      ρ⇒ ∘ᵥ Phom (f , id₁)                  ≈⟨ hom.identityʳ ⟩
      ρ⇒                                    ∎
      where
        open HomReasoning (hom x y)
        open MorphismReasoning (hom x y)

    assoc : ∀ {x y z w} {f : x ⇒₁ y} {g : y ⇒₁ z} {h : z ⇒₁ w} →
            let open ComHom in
            [ (h ⊚₀ g) ⊚₀ f ⇒ h ⊚₀ (g ⊚₀ f) ]⟨
              Phom (h , g) ⊚₁ id₂  ⇒⟨ (h ⊚₀ g) ⊚₀ f ⟩
              Phom (_ , f)         ⇒⟨ (h ⊚₀ g) ⊚₀ f ⟩
              α⇒
            ≈ α⇒                   ⇒⟨ h ⊚₀ (g ⊚₀ f) ⟩
              id₂ ⊚₁ Phom (g , f)  ⇒⟨ h ⊚₀ (g ⊚₀ f) ⟩
              Phom (h , _)
            ⟩
    assoc {x} {_} {_} {w} {f} {g} {h} = begin
      α⇒ ∘ᵥ Phom (_ , f) ∘ᵥ Phom (h , g) ⊚₁ id₂  ≈⟨ refl⟩∘⟨ elimʳ ⊚.identity ⟩
      α⇒ ∘ᵥ Phom (_ , f)                         ≈⟨ hom.identityʳ ⟩
      α⇒                                         ≈˘⟨ elimˡ ⊚.identity ⟩
      id₂ ⊚₁ Phom (g , f) ∘ᵥ α⇒                  ≈˘⟨ hom.identityˡ ⟩
      Phom (h , _) ∘ᵥ id₂ ⊚₁ Phom (g , f) ∘ᵥ α⇒  ∎
      where
        open HomReasoning (hom x w)
        open MorphismReasoning (hom x w)

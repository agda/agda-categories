{-# OPTIONS --without-K --safe #-}

open import Categories.Bicategory

-- The two Hom 2-functors from (op C) and C to Cats.

module Categories.Pseudofunctor.Hom {o ℓ e t} (C : Bicategory o ℓ e t) where

open import Data.Product using (_,_)

import Categories.Bicategory.Extras as BicategoryExtras
open import Categories.Bicategory.Opposite using (op)
open import Categories.Bicategory.Instance.Cats using (Cats)
import Categories.Category.Construction.Core as Core
open import Categories.Functor.Bifunctor.Properties
open import Categories.Pseudofunctor using (Pseudofunctor)
import Categories.Morphism.Reasoning as MorphismReasoning
import Categories.Morphism as Morphism
open import Categories.NaturalTransformation using (ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (niHelper)

open BicategoryExtras C
open Shorthands
open hom.HomReasoning
private
  module MR {A} {B} where
    open Core.Shorthands (hom A B) public
    open MorphismReasoning (hom A B) public
  open MR


-- The left and right hom-pseudofunctors for a given bicategory.
--
-- Note that these are *not* simply partial applications of a single
-- *binary* hom-pseudofunctor because pre-/post-composition with
-- identity 1-cells in bicategories is only weakly unitary, i.e. the
-- partial applications Hom[ id , f ] and Hom[ g , id ] would send a
-- 1-cell h to (id ∘ h ∘ f) and (g ∘ h ∘ id) which are isomorphic but
-- not strictly equal to (h ∘ f) and (g ∘ h).

-- The right hom-pseudofunctor (post-composition)

Hom[_,-] : Obj → Pseudofunctor C (Cats o ℓ e)
Hom[ A ,-] = record
  { P₀ = hom A
  ; P₁ = [-]⊚-
  -- A curried version of the left unitor
  ; P-identity  = niHelper (record
    { η         = λ _ → ntHelper (record
      { η       = λ f → unitˡ.⇐.η (_ , f)
      ; commute = λ _ → ⟺ ▷-∘ᵥ-λ⇐
      })
    ; η⁻¹       = λ _ → ntHelper (record
      { η       = λ f → unitˡ.⇒.η (_ , f)
      ; commute = λ _ → λ⇒-∘ᵥ-▷
      })
    ; commute = λ _ → unitˡ.⇐.commute (_ , hom.id)
    ; iso     = λ _ → record
      { isoˡ  = λ {f} → unitˡ.iso.isoʳ (_ , f)
      ; isoʳ  = λ {f} → unitˡ.iso.isoˡ (_ , f)
      }
    })
  -- A curried version of the associator
  ; P-homomorphism = niHelper (record
    { η         = λ{ (f , g) → ntHelper (record
      { η       = λ h → ⊚-assoc.⇐.η ((f , g) , h)
      ; commute = λ _ → α⇐-▷-∘ₕ
      }) }
    ; η⁻¹       = λ{ (f , g) → ntHelper (record
      { η       = λ h → ⊚-assoc.⇒.η ((f , g) , h)
      ; commute = λ _ → α⇒-▷-∘ₕ
      }) }
    ; commute = λ{ {f₁ , g₁} {f₂ , g₂} (β , γ) {h} → begin
          α⇐ ∘ᵥ f₂ ▷ (γ ◁ h) ∘ᵥ β ◁ (g₁ ⊚₀ h)
        ≈˘⟨ refl⟩∘⟨ [ ⊚ ]-decompose₂ ⟩
          α⇐ ∘ᵥ β ⊚₁ (γ ◁ h)
        ≈⟨ ⊚-assoc.⇐.commute ((β , γ) , id₂) ⟩
          (β ⊚₁ γ) ◁ h ∘ᵥ α⇐
        ∎ }
    ; iso    = λ{ (f , g) → record
      { isoˡ = λ {h} → ⊚-assoc.iso.isoʳ ((f , g) , h)
      ; isoʳ = λ {h} → ⊚-assoc.iso.isoˡ ((f , g) , h) }
      }
    })
  ; unitaryˡ = λ {_ _ f g} → begin
      λ⇒ ◁ g ∘ᵥ α⇐ ∘ᵥ (id₂ ◁ (f ⊚₀ g)) ∘ᵥ λ⇐
                                 ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⊚.identity ⟩∘⟨refl ⟩
      λ⇒ ◁ g ∘ᵥ α⇐ ∘ᵥ id₂ ∘ᵥ λ⇐  ≈⟨ unitorˡ-coherence ⟩∘⟨ refl⟩∘⟨ hom.identityˡ ⟩
      (λ⇒ ∘ᵥ α⇒) ∘ᵥ α⇐ ∘ᵥ λ⇐     ≈⟨ isoʳ (unitorˡ ∘ᵢ associator) ⟩
      id₂                        ∎
  ; unitaryʳ = λ {_ _ f g} → begin
        ρ⇒ ◁ g ∘ᵥ α⇐ ∘ᵥ f ▷ λ⇐ ∘ᵥ id₂
      ≈⟨ pushʳ (refl⟩∘⟨ hom.identityʳ) ⟩
        (ρ⇒ ◁ g ∘ᵥ α⇐) ∘ᵥ f ▷ λ⇐
      ≈˘⟨ switch-tofromʳ (associator ⁻¹) triangle ⟩∘⟨refl ⟩
        f ▷ λ⇒ ∘ᵥ f ▷ λ⇐
      ≈⟨ isoʳ (f ▷ᵢ unitorˡ) ⟩
        id₂
      ∎
  ; assoc = λ {_ _ _ _ f g h e} → begin
        α⇒ ◁ e ∘ᵥ α⇐ ∘ᵥ (id₂ ⊚₁ id₂) ∘ᵥ α⇐
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⊚.identity ⟩∘⟨refl ⟩
        α⇒ ◁ e ∘ᵥ α⇐ ∘ᵥ id₂ ∘ᵥ α⇐
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ hom.identityˡ ⟩
        α⇒ ◁ e ∘ᵥ α⇐ ∘ᵥ α⇐
      ≈˘⟨ switch-fromtoˡ ((associator ◁ᵢ e) ⁻¹)
                         (hom.sym-assoc ○ pentagon-inv) ⟩
        α⇐ ∘ᵥ h ▷ α⇐
      ≈˘⟨ pushʳ hom.identityʳ ○ hom.identityʳ  ⟩
        α⇐ ∘ᵥ (h ▷ α⇐ ∘ᵥ id₂) ∘ᵥ id₂
      ∎
  }

-- The left hom-pseudofunctor (pre-composition)

Hom[-,_] : Obj → Pseudofunctor (op C) (Cats o ℓ e)
Hom[-, B ] = record
  { P₀ = λ A → hom A B
  ; P₁ = -⊚[-]
  -- A curried version of the right unitor
  ; P-identity  = niHelper (record
    { η         = λ _ → ntHelper (record
      { η       = λ f → unitʳ.⇐.η (f , _)
      ; commute = λ _ → ⟺ ◁-∘ᵥ-ρ⇐
      })
    ; η⁻¹       = λ _ → ntHelper (record
      { η       = λ f → unitʳ.⇒.η (f , _)
      ; commute = λ _ → ρ⇒-∘ᵥ-◁
      })
    ; commute = λ _ → unitʳ.⇐.commute (hom.id , _)
    ; iso     = λ _ → record
      { isoˡ  = λ {f} → unitʳ.iso.isoʳ (f , _)
      ; isoʳ  = λ {f} → unitʳ.iso.isoˡ (f , _)
      }
    })
  -- A curried version of the associator
  ; P-homomorphism = niHelper (record
    { η         = λ{ (f , g) → ntHelper (record
      { η       = λ h → ⊚-assoc.⇒.η ((h , g) , f)
      ; commute = λ _ → α⇒-◁-∘ₕ
      }) }
    ; η⁻¹       = λ{ (f , g) → ntHelper (record
      { η       = λ h → ⊚-assoc.⇐.η ((h , g) , f)
      ; commute = λ _ → α⇐-◁-∘ₕ
      }) }
    ; commute = λ{ {f₁ , g₁} {f₂ , g₂} (β , γ) {h} → begin
          α⇒ ∘ᵥ (h ▷ γ) ◁ f₂ ∘ᵥ (h ⊚₀ g₁) ▷ β
        ≈˘⟨ refl⟩∘⟨ [ ⊚ ]-decompose₁ ⟩
          α⇒ ∘ᵥ (h ▷ γ) ⊚₁ β
        ≈⟨ ⊚-assoc.⇒.commute ((id₂ , γ) , β) ⟩
          h ▷ (γ ⊚₁ β) ∘ᵥ α⇒
        ∎ }
    ; iso    = λ{ (f , g) → record
      { isoˡ = λ {h} → ⊚-assoc.iso.isoˡ ((h , g) , f)
      ; isoʳ = λ {h} → ⊚-assoc.iso.isoʳ ((h , g) , f) }
      }
    })
  ; unitaryˡ = λ {_ _ f g} → begin
      g ▷ ρ⇒ ∘ᵥ α⇒ ∘ᵥ ((g ⊚₀ f) ▷ id₂) ∘ᵥ ρ⇐
                                   ≈⟨ pushʳ (refl⟩∘⟨ ⊚.identity ⟩∘⟨refl) ⟩
      (g ▷ ρ⇒ ∘ᵥ α⇒) ∘ᵥ id₂ ∘ᵥ ρ⇐  ≈⟨ ⟺ unitorʳ-coherence ⟩∘⟨ hom.identityˡ ⟩
      ρ⇒ ∘ᵥ ρ⇐                     ≈⟨ isoʳ unitorʳ ⟩
      id₂                          ∎
  ; unitaryʳ = λ {_ _ f g} → begin
        g ▷ λ⇒ ∘ᵥ α⇒ ∘ᵥ ρ⇐ ◁ f ∘ᵥ id₂
      ≈⟨ pushʳ (refl⟩∘⟨ hom.identityʳ) ⟩
        (g ▷ λ⇒ ∘ᵥ α⇒) ∘ᵥ ρ⇐ ◁ f
      ≈⟨ triangle ⟩∘⟨refl ⟩
        ρ⇒ ◁ f ∘ᵥ ρ⇐ ◁ f
      ≈⟨ isoʳ (unitorʳ ◁ᵢ f) ⟩
        id₂
      ∎
  ; assoc = λ {_ _ _ _ f g h e} → begin
        e ▷ α⇐ ∘ᵥ α⇒ ∘ᵥ (id₂ ⊚₁ id₂) ∘ᵥ α⇒
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⊚.identity ⟩∘⟨refl ⟩
        e ▷ α⇐ ∘ᵥ α⇒ ∘ᵥ id₂ ∘ᵥ α⇒
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ hom.identityˡ ⟩
        e ▷ α⇐ ∘ᵥ α⇒ ∘ᵥ α⇒
      ≈˘⟨ switch-fromtoˡ (e ▷ᵢ associator) pentagon ⟩
        α⇒ ∘ᵥ α⇒ ◁ h
      ≈˘⟨ pushʳ hom.identityʳ ○ hom.identityʳ  ⟩
        α⇒ ∘ᵥ (α⇒ ◁ h ∘ᵥ id₂) ∘ᵥ id₂
      ∎
  }

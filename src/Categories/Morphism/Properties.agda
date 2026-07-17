{-# OPTIONS --without-K --safe #-}
open import Categories.Category

module Categories.Morphism.Properties {o ℓ e} (𝒞 : Category o ℓ e) where

open import Function.Base using (_$_)
open import Data.Product using (_,_; _×_)

open Category 𝒞
open Definitions 𝒞
open HomReasoning

import Categories.Morphism as M
open M 𝒞
open import Categories.Morphism.Reasoning 𝒞

private
  variable
    A B C D : Obj
    f g h i : A ⇒ B

module _ (iso : Iso f g) where

  open Iso iso

  Iso-resp-≈ : f ≈ h → g ≈ i → Iso h i
  Iso-resp-≈ {h = h} {i = i} eq₁ eq₂ = record
    { isoˡ = begin
      i ∘ h ≈˘⟨ eq₂ ⟩∘⟨ eq₁ ⟩
      g ∘ f ≈⟨ isoˡ ⟩
      id    ∎
    ; isoʳ = begin
      h ∘ i ≈˘⟨ eq₁ ⟩∘⟨ eq₂ ⟩
      f ∘ g ≈⟨ isoʳ ⟩
      id    ∎
    }

  Iso-swap : Iso g f
  Iso-swap = record
    { isoˡ = isoʳ
    ; isoʳ = isoˡ
    }

  Iso⇒Mono : Mono f
  Iso⇒Mono h i eq = begin
    h           ≈⟨ introˡ isoˡ ⟩
    (g ∘ f) ∘ h ≈⟨ pullʳ eq ⟩
    g ∘ f ∘ i   ≈⟨ cancelˡ isoˡ ⟩
    i           ∎

  Iso⇒Epi : Epi f
  Iso⇒Epi h i eq = begin
    h           ≈⟨ introʳ isoʳ ⟩
    h ∘ f ∘ g   ≈⟨ pullˡ eq ⟩
    (i ∘ f) ∘ g ≈⟨ cancelʳ isoʳ ⟩
    i           ∎

Iso-∘ : Iso f g → Iso h i → Iso (h ∘ f) (g ∘ i)
Iso-∘ {f = f} {g = g} {h = h} {i = i} iso iso′ = record
  { isoˡ = begin
    (g ∘ i) ∘ h ∘ f ≈⟨ cancelInner (isoˡ iso′) ⟩
    g ∘ f           ≈⟨ isoˡ iso ⟩
    id              ∎
  ; isoʳ = begin
    (h ∘ f) ∘ g ∘ i ≈⟨ cancelInner (isoʳ iso) ⟩
    h ∘ i           ≈⟨ isoʳ iso′ ⟩
    id              ∎
  }
  where open Iso

Iso-≈ : f ≈ h → Iso f g → Iso h i → g ≈ i
Iso-≈ {f = f} {h = h} {g = g} {i = i} eq iso iso′ = begin
  g           ≈⟨ introˡ (isoˡ iso′) ⟩
  (i ∘ h) ∘ g ≈˘⟨ (refl⟩∘⟨ eq) ⟩∘⟨refl ⟩
  (i ∘ f) ∘ g ≈⟨ cancelʳ (isoʳ iso) ⟩
  i           ∎
  where open Iso

module _ where
  open _≅_

  isos×≈⇒≈ : ∀ {f g : A ⇒ B} → h ≈ i → (iso₁ : A ≅ C) → (iso₂ : B ≅ D) →
               CommutativeSquare f (from iso₁) (from iso₂) h →
               CommutativeSquare g (from iso₁) (from iso₂) i →
               f ≈ g
  isos×≈⇒≈ {h = h} {i = i} {f = f} {g = g} eq iso₁ iso₂ sq₁ sq₂ = begin
    f ≈⟨ switch-fromtoˡ iso₂ sq₁ ⟩
    to iso₂ ∘ h ∘ from iso₁ ≈⟨ refl⟩∘⟨ (eq ⟩∘⟨refl ) ⟩
    to iso₂ ∘ i ∘ from iso₁ ≈˘⟨ switch-fromtoˡ iso₂ sq₂ ⟩
    g ∎

id-iso : ∀ {X} → Iso (id {X}) (id {X})
id-iso = record
  { isoˡ = identity²
  ; isoʳ = identity²
  }

id-is-iso : ∀ {X} → IsIso (id {X})
id-is-iso = record
  { inv = id
  ; iso = id-iso
  }

--------------------------------------------------------------------------------
-- Monomorphisms

Mono-∘₂ : Mono (f ∘ g) → Mono g
Mono-∘₂ {f = f} {g = g} fg-mono g₁ g₂ eq = fg-mono g₁ g₂ (extendˡ eq)

-- This might be trivial, but it also shouldn't be proved more than once!
Mono-id : Mono {A = A} id
Mono-id g₁ g₂ eq = begin
  g₁      ≈˘⟨ identityˡ ⟩
  id ∘ g₁ ≈⟨ eq ⟩
  id ∘ g₂ ≈⟨ identityˡ ⟩
  g₂ ∎

Mono-∘ : Mono f → Mono g → Mono (f ∘ g)
Mono-∘ {f = f} {g = g} f-mono g-mono g₁ g₂ eq =
  g-mono g₁ g₂ (f-mono (g ∘ g₁) (g ∘ g₂) (sym-assoc ○ eq ○ assoc))

id↣ : ∀ {A} → A ↣ A
id↣ = record { mor = id ; mono = Mono-id }

infixr 9 _∘↣_
_∘↣_ : B ↣ C → A ↣ B → A ↣ C
f ∘↣ g = record { mor = mor f ∘ mor g ; mono = Mono-∘ (mono f) (mono g) }
  where
    open _↣_
--------------------------------------------------------------------------------
-- Epimorphisms

Epi-∘₂ : Epi (f ∘ g) → Epi f
Epi-∘₂ {f = f} {g = g} fg-epi g₁ g₂ eq = fg-epi g₁ g₂ (extendʳ eq)

Epi-id : Epi {A = A} id
Epi-id g₁ g₂ eq = begin
  g₁      ≈˘⟨ identityʳ ⟩
  g₁ ∘ id ≈⟨ eq ⟩
  g₂ ∘ id ≈⟨ identityʳ ⟩
  g₂ ∎

Epi-∘ : Epi f → Epi g → Epi (f ∘ g)
Epi-∘ {f = f} {g = g} f-epi g-epi g₁ g₂ eq =
  f-epi g₁ g₂ (g-epi (g₁ ∘ f) (g₂ ∘ f) (assoc ○ eq ○ sym-assoc))

id↠ : ∀ {A} → A ↠ A
id↠ = record { mor = id ; epi = Epi-id }

infixr 9 _∘↠_

_∘↠_ : B ↠ C → A ↠ B → A ↠ C
f ∘↠ g = record { mor = mor f ∘ mor g ; epi = Epi-∘ (epi f) (epi g) }
  where
    open _↠_

Retract⇒Epi : ∀ {X Y} → (f : Retract X Y) → Epi (Retract.retract f)
Retract⇒Epi {X}{Y} f g₁ g₂ eq = begin
  g₁                                                   ≈⟨ introʳ (Retract.is-retract f) ⟩
  g₁ ∘ Retract.retract f ∘ Retract.section f           ≈⟨ extendʳ eq ⟩ 
  g₂ ∘ Retract.retract f ∘ Retract.section f           ≈⟨ elimʳ (Retract.is-retract f) ⟩ 
  g₂ ∎

Retract⇒Mono : ∀ {X Y} → (f : Retract X Y) → Mono (Retract.section f)
Retract⇒Mono {X}{Y} f g₁ g₂ eq = begin
  g₁                                                   ≈⟨ introˡ (Retract.is-retract f) ⟩ 
  (Retract.retract f ∘ Retract.section f) ∘ g₁         ≈⟨ extendˡ eq ⟩ 
  (Retract.retract f ∘ Retract.section f) ∘ g₂         ≈⟨ elimˡ (Retract.is-retract f) ⟩
  g₂ ∎

--------------------------------------------------------------------------------
-- Isomorphism from a section and a retraction

EpicRetract⇒Iso : ∀ {X Y} {f : Y ⇒ X} {r : X ⇒ Y} →
                   r RetractOf f → Epi f → Iso f r
EpicRetract⇒Iso {f = f} {r} rf≈id epi = record {
  isoˡ = rf≈id ;
  isoʳ = epi (f ∘ r) id frf≈idf }
  where frf≈idf : (f ∘ r) ∘ f ≈ id ∘ f
        frf≈idf = begin
          (f ∘ r) ∘ f ≈⟨ pullʳ rf≈id ⟩
          f ∘ id    ≈⟨ id-comm ⟩
          id ∘ f ∎

MonicSection⇒Iso : ∀ {X Y} {f : Y ⇒ X} {s : X ⇒ Y} →
                   s SectionOf f → Mono f → Iso f s
MonicSection⇒Iso {f = f} {s} fs≈id mono = record {
  isoˡ = mono (s ∘ f) id fsf≈fid ;
  isoʳ = fs≈id }
  where fsf≈fid : f ∘ (s ∘ f) ≈ f ∘ id
        fsf≈fid = begin
          f ∘ (s ∘ f) ≈⟨ pullˡ fs≈id ⟩
          id ∘ f      ≈⟨ id-comm-sym ⟩
          f ∘ id ∎

≈-SectionRetraction : ∀ {X Y} {f : Y ⇒ X} {s r : X ⇒ Y} →
                      s SectionOf f → r RetractOf f → s ≈ r
≈-SectionRetraction {f = f} {s} {r} fs≈id rf≈id = begin
  s           ≈⟨ insertˡ rf≈id ⟩
  r ∘ (f ∘ s) ≈⟨ elimʳ fs≈id ⟩
  r ∎

SectionRetraction⇒Isoˡ : ∀ {X Y} {f : Y ⇒ X} {s r : X ⇒ Y} →
                         s SectionOf f → r RetractOf f → Iso f s
SectionRetraction⇒Isoˡ {f = f} {s} {r} fs≈id rf≈id = record {
  isoˡ = sf≈id ;
  isoʳ = fs≈id }
  where sf≈id : s ∘ f ≈ id
        sf≈id = begin
          s ∘ f  ≈⟨ ≈-SectionRetraction fs≈id rf≈id ⟩∘⟨refl ⟩
          r ∘ f  ≈⟨ rf≈id ⟩
          id ∎

SectionRetraction⇒Isoʳ : ∀ {X Y} {f : Y ⇒ X} {s r : X ⇒ Y} →
                         s SectionOf f → r RetractOf f → Iso f r
SectionRetraction⇒Isoʳ {f = f} {s} {r} fs≈id rf≈id = record {
  isoˡ = rf≈id ;
  isoʳ = fr≈id }
  where fr≈id : f ∘ r ≈ id
        fr≈id = begin
          f ∘ r ≈⟨ refl⟩∘⟨ ⟺ (≈-SectionRetraction fs≈id rf≈id) ⟩
          f ∘ s ≈⟨ fs≈id ⟩
          id ∎

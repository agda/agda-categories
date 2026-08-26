{-# OPTIONS --without-K --safe #-}

open import Level
open import Categories.Category
open import Categories.Morphism.Lifts
open import Categories.Morphism using (IsIso; Iso)

module Categories.Morphism.FactorizationStructure.Duality where


private
  variable
    ℓℰ ℓℳ : Level
    o ℓ eq : Level
    𝒞 : Category o ℓ eq
    ℰ : MorphismClass 𝒞 ℓℰ
    ℳ : MorphismClass 𝒞 ℓℳ

open import Categories.Morphism.Lifts
open import Categories.Morphism.FactorizationStructure
open import Categories.Morphism.FactorizationStructure.Core

Diagonalᵒᵖ : ∀ {A B C D : Category.Obj 𝒞}
                {e : 𝒞 [ A , B ]} {f : 𝒞 [ A , C ]}
                {g : 𝒞 [ B , D ]} {m : 𝒞 [ C , D ]}
                → Diagonal 𝒞 e f g m
                → Diagonal (Category.op 𝒞) m g f e
Diagonalᵒᵖ diag = record
  { d = diag .d
  ; commˡ = commʳ diag
  ; commʳ = commˡ diag
  }
  where open Diagonal

_ᵒᵖ : {p : Level} {M : MorphismClass 𝒞 p}
      → {A B : Category.Obj 𝒞}
      → MorphismClassMember 𝒞 M A B
      → MorphismClassMember (Category.op 𝒞) M B A
_ᵒᵖ f = record { mor = f .mor ; in-class = f .in-class }
  where open MorphismClassMember


_≅ᵒᵖ : {A B : Category.Obj 𝒞} → {h : 𝒞 [ A , B ]} → IsIso 𝒞 h → IsIso (Category.op 𝒞) h
_≅ᵒᵖ {h = h} h-iso = record
  { inv = inv
  ; iso = record { isoˡ = isoʳ ; isoʳ = isoˡ }
  }
  where open IsIso h-iso

dual-factorizations : {ℰ : MorphismClass 𝒞 ℓℰ} {ℳ : MorphismClass 𝒞 ℓℳ}
                    → [ ℰ , ℳ ]-structured 𝒞
                    → [ ℳ , ℰ ]-structured (Category.op 𝒞)
dual-factorizations {𝒞 = 𝒞} factorizationstructure = record
  { ℰ-resp-≈ = ℳ-resp-≈
  ; ℳ-resp-≈ = ℰ-resp-≈
  ; factor = λ f →
           let open Factorization (factor f) in
           record
           { Im = Im
           ; e = m ᵒᵖ
           ; m = e ᵒᵖ
           ; m∘e≈h = m∘e≈h
           }
  ; Iso∘ℰ = λ h m → ℳ∘Iso (m ᵒᵖ) (h ≅ᵒᵖ)
  ; ℳ∘Iso = λ e h → Iso∘ℰ (h ≅ᵒᵖ) (e ᵒᵖ)
  ; diagonalization = λ eᵒᵖ mᵒᵖ comm →
      let
        d : UniqueDiagonal 𝒞 (mᵒᵖ .mor) _ _ (eᵒᵖ .mor)
        d = diagonalization (mᵒᵖ ᵒᵖ) (eᵒᵖ ᵒᵖ) (Equiv.sym comm)
      in
      record
      { diagonal = Diagonalᵒᵖ {𝒞 = 𝒞} (d .diagonal)
      ; unique = λ v → (d .unique) (Diagonalᵒᵖ v)
      }
  }
  where
    open FactorizationStructure factorizationstructure
    open MorphismClassMember using (mor)
    open Category 𝒞
    open UniqueDiagonal


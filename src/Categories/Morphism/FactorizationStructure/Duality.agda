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

Diagonal^op : ∀ {A B C D : Category.Obj 𝒞}
                {e : 𝒞 [ A , B ]} {f : 𝒞 [ A , C ]}
                {g : 𝒞 [ B , D ]} {m : 𝒞 [ C , D ]}
                → Diagonal 𝒞 e f g m
                → Diagonal (Category.op 𝒞) m g f e
Diagonal^op diag = record
  { d = diag .d
  ; commˡ = commʳ diag
  ; commʳ = commˡ diag
  }
  where open Diagonal

dual-factorizations : {ℰ : MorphismClass 𝒞 ℓℰ} {ℳ : MorphismClass 𝒞 ℓℳ}
                    → [ ℰ , ℳ ]-structured 𝒞
                    → [ ℳ , ℰ ]-structured (Category.op 𝒞)
dual-factorizations {𝒞 = 𝒞} factorizationstructure = record
  { ℰ-resp-≈ = ℳ-resp-≈
  ; ℳ-resp-≈ = ℰ-resp-≈
  ; factor = λ f →
           let
             open Factorization (factor f)
           in
           record
           { Im = Im
           ; e = record { mor = m .mor ; in-class = m .in-class }
           ; m = record { mor = e .mor ; in-class = e .in-class }
           ; m∘e≈h = m∘e≈h
           }
  ; Iso∘ℰ = λ h m →
      ℳ∘Iso
      (record { mor = m .mor ; in-class = m .in-class })
      (record { inv = h .inv
              ; iso = record
                      { isoˡ = isoʳ (h .iso)
                      ; isoʳ = isoˡ (h .iso) } })
  ; ℳ∘Iso = λ e h →
      Iso∘ℰ
      (record { inv = h .inv
              ; iso = record
                    { isoˡ = isoʳ (h .iso)
                    ; isoʳ = isoˡ (h .iso)}})
      (record { mor = e .mor ; in-class = e .in-class })
  ; diagonalization = λ e^op m^op comm →
      let
        e = record { mor = m^op .mor ; in-class = m^op .in-class }
        m = record { mor = e^op .mor ; in-class = e^op .in-class }
        d : UniqueDiagonal 𝒞 (m^op .mor) _ _ (e^op .mor)
        d = diagonalization e m (Equiv.sym comm)
      in
      record
      { diagonal = Diagonal^op {𝒞 = 𝒞} (d .diagonal)
      ; unique = λ v → (d. unique) (Diagonal^op v)
      }
  }
  where
    open FactorizationStructure factorizationstructure
    open MorphismClassMember
    open Category 𝒞
    open IsIso
    open Iso
    open Diagonal
    open UniqueDiagonal


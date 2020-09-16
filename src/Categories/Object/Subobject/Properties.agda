{-# OPTIONS --without-K --safe #-}


module Categories.Object.Subobject.Properties where

open import Level
open import Data.Product
open import Data.Unit
open import Function using (_$_)

open import Relation.Binary using (_=[_]⇒_)
open import Relation.Binary.Bundles
open import Relation.Binary.OrderMorphism

open import Categories.Category
open import Categories.Functor
open import Categories.Functor.Presheaf
open import Categories.Category.Slice
open import Categories.Object.Subobject
open import Categories.Diagram.Pullback renaming (glue to glue-pullback)
open import Categories.Diagram.Pullback.Properties
open import Categories.Category.Instance.Posets
open import Categories.Category.Instance.Setoids
open import Categories.Adjoint.Instance.PosetCore
import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR
open import Categories.Morphism.Notation


module _ {o ℓ e} {𝒞 : Category o ℓ e} (has-pullbacks : ∀ {A B X} → (f : 𝒞 [ A , X ]) → (g : 𝒞 [ B , X ]) → Pullback 𝒞 f g) where
  private
    module 𝒞 = Category 𝒞

  open 𝒞.HomReasoning
  open 𝒞.Equiv

  open Mor 𝒞
  open MR 𝒞
  open _↣_

  -- The Subobject functor, into the category of posets
  Subₚ : Presheaf 𝒞 (Posets (o ⊔ ℓ ⊔ e) (ℓ ⊔ e) (ℓ ⊔ e))
  Subₚ = record
    { F₀ = Subobjects 𝒞
    ; F₁ = λ f → record
      { fun = morphism f
      ; monotone = λ {(α , m) (β , n)} h → monotone f {(α , m)} {β , n} h
      }
    ; identity = λ {A} {(α , m)} →
      let pid = has-pullbacks 𝒞.id (mor m)
      in record
        { from = record
          { h = Pullback.p₂ pid
          ; △ = ⟺ (Pullback.commute pid) ○ 𝒞.identityˡ
          }
        ; to = record
          { h = Pullback.universal pid id-comm-sym
          ; △ = Pullback.p₁∘universal≈h₁ pid
          }
        ; iso = record
          { isoˡ = pullback-identity 𝒞 pid
          ; isoʳ = Pullback.p₂∘universal≈h₂ pid
          }
        }
    ; homomorphism = λ {X} {Y} {Z} {f} {g} {(α , m)} →
      let pfg = has-pullbacks (𝒞 [ f ∘ g ]) (mor m)
          pf = has-pullbacks f (mor m)
          pg = has-pullbacks g (Pullback.p₁ pf)
          iso = up-to-iso 𝒞 pfg (glue-pullback 𝒞 pf pg)
          module iso = _≅_ iso
      in record
        { from = record
          { h = iso.from
          ; △ = Pullback.p₁∘universal≈h₁ pg
          }
        ; to = record
          { h = iso.to
          ; △ = Pullback.p₁∘universal≈h₁ pfg
          }
        ; iso = record
          { isoˡ = iso.isoˡ
          ; isoʳ = iso.isoʳ
          }
        }
    ; F-resp-≈ = λ {A B f g} eq {(α , m)} →
      let pf = has-pullbacks f (mor m)
          pg = has-pullbacks g (mor m)
          iso = up-to-iso 𝒞 pf (pullback-resp-≈ 𝒞 pg (sym eq) refl)
          module iso = _≅_ iso
      in record
        { from = record
          { h = iso.from
          ; △ = Pullback.p₁∘universal≈h₁ pg
          }
        ; to = record
          { h = iso.to
          ; △ = Pullback.p₁∘universal≈h₁ pf
          }
        ; iso = record
          { isoˡ = iso.isoˡ
          ; isoʳ = iso.isoʳ
          }
        }
    }
    where
      morphism : ∀ {A B} → (f : 𝒞 [ B , A ]) → Σ[ α ∈ 𝒞.Obj ] (α ↣ A) → Σ[ β ∈ 𝒞.Obj ] (β ↣ B)
      morphism f (α , m) = 
        let pb = has-pullbacks f (mor m)
        in Pullback.P pb , record
          { mor = Pullback.p₁ pb
          ; mono = Pullback-resp-Mono 𝒞 pb (mono m)
          }

      monotone : ∀ {A B} (f : 𝒞 [ B , A ]) → Poset._≤_ (Subobjects 𝒞 A) =[ morphism f ]⇒ Poset._≤_ (Subobjects 𝒞 B)
      monotone f {(α , m)} {(β , n)} h =
        let pm = has-pullbacks f (mor m)
            pn = has-pullbacks f (mor n)
        in record
          { h = Pullback.universal pn $ begin
              𝒞 [ f ∘ Pullback.p₁ pm ] ≈⟨ Pullback.commute pm ⟩
              𝒞 [ mor m ∘ Pullback.p₂ pm ] ≈⟨ pushˡ (⟺ (Slice⇒.△ h)) ⟩
              𝒞 [ mor n ∘ 𝒞 [ Slice⇒.h h ∘ Pullback.p₂ pm ] ] ∎
          ; △ = Pullback.p₁∘universal≈h₁ pn
          }

  -- The subobject functor as a presheaf on Setoids.
  -- This is just Subₚ composed with the 'Core'
  Sub : Presheaf 𝒞 (Setoids (o ⊔ ℓ ⊔ e) (ℓ ⊔ e))
  Sub =  Core ∘F Subₚ

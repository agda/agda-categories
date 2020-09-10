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
open import Categories.Category.Construction.Comma
open import Categories.Object.Subobject
open import Categories.Diagram.Pullback renaming (glue to glue-pullback)
open import Categories.Diagram.Pullback.Properties
open import Categories.Category.Instance.Posets
import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR
open import Categories.Morphism.Notation


module _ {o ℓ e} {𝒞 : Category o ℓ e} (has-pullbacks : ∀ {A B X} → (f : 𝒞 [ A , X ]) → (g : 𝒞 [ B , X ]) → Pullback 𝒞 f g) where
  private
    module 𝒞 = Category 𝒞

  open 𝒞
  open 𝒞.HomReasoning
  open 𝒞.Equiv

  open Mor 𝒞
  open MR 𝒞
  open _↣_

  -- The Subobject functor, into the category of posets
  -- FIXME I should probably tidy up this proof a lot
  -- For starters, we only ever use composition/equality in 𝒞.
  -- Then, it feels like the 'homomorphism' and 'F-resp-≈' cases
  -- are pretty much the same
  -- We also should probably open Pullback at 𝒞
  Subₚ : Functor 𝒞.op (Posets (o ⊔ ℓ ⊔ e) (ℓ ⊔ e) (ℓ ⊔ e))
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
          { g = Pullback.p₂ pid
          ; h = lift tt
          ; commute = Pullback.commute pid
          }
        ; to = record
          { g = Pullback.universal pid id-comm-sym
          ; h = lift tt
          ; commute = 𝒞.identityˡ ○ ⟺ (Pullback.p₁∘universal≈h₁ pid)
          }
        ; iso = record
          { isoˡ = (pullback-identity 𝒞 pid) , lift tt
          ; isoʳ = (Pullback.p₂∘universal≈h₂ pid) , lift tt
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
          { g = iso.from
          ; h = lift tt
          ; commute = 𝒞.identityˡ ○ ⟺ (Pullback.p₁∘universal≈h₁ pg)
          }
        ; to = record
          { g = iso.to
          ; h = lift tt
          ; commute = 𝒞.identityˡ ○ ⟺ (Pullback.p₁∘universal≈h₁ pfg)
          }
        ; iso = record
          { isoˡ = iso.isoˡ , lift tt
          ; isoʳ = iso.isoʳ , lift tt
          }
        }
    ; F-resp-≈ = λ {A B f g} eq {(α , m)} →
      let pf = has-pullbacks f (mor m)
          pg = has-pullbacks g (mor m)
          iso = up-to-iso 𝒞 pf (pullback-resp-≈ 𝒞 pg (sym eq) refl)
          module iso = _≅_ iso
      in record
        { from = record
          { g = iso.from
          ; h = lift tt
          ; commute = 𝒞.identityˡ ○ ⟺ (Pullback.p₁∘universal≈h₁ pg)
          }
        ; to = record
          { g = iso.to
          ; h = lift tt
          ; commute = 𝒞.identityˡ ○ ⟺ (Pullback.p₁∘universal≈h₁ pf)
          }
        ; iso = record
          { isoˡ = iso.isoˡ , lift tt
          ; isoʳ = iso.isoʳ , lift tt
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
        { g = Pullback.universal pn $ begin
          𝒞 [ f ∘ Pullback.p₁ pm ] ≈˘⟨ 𝒞.identityˡ ⟩
          𝒞 [ 𝒞.id ∘ 𝒞 [ f ∘ Pullback.p₁ pm ] ] ≈⟨ pushʳ (Pullback.commute pm) ⟩
          𝒞 [ 𝒞 [ 𝒞.id ∘ mor m ] ∘ Pullback.p₂ pm ] ≈⟨ pushˡ (Comma⇒.commute h) ⟩
          𝒞 [ mor n ∘ 𝒞 [ Comma⇒.g h ∘ Pullback.p₂ pm ] ] ∎
        ; h = lift tt
        ; commute = begin
          𝒞 [ 𝒞.id ∘ Pullback.p₁ pm ] ≈⟨ 𝒞.identityˡ ⟩
          Pullback.p₁ pm ≈˘⟨ Pullback.p₁∘universal≈h₁ pn ⟩
          𝒞 [ Pullback.p₁ pn ∘ Pullback.universal pn _ ] ∎
        }

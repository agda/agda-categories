{-# OPTIONS --without-K --safe --lossy-unification #-}

module Categories.Diagram.End.Properties where

-- The following conventions are taken in this file: C is the 'source' category
-- and D is the destination. If two source categories are needed, the other is
-- called 'P' for "parameter", following MacLane. F, G and H are functors and ef,
-- eg and eh are witnesses of their respective ends.

open import Level
open import Data.Product using (Σ; _,_)
open import Function using (_$_)

open import Categories.Category using (Category)
open import Categories.Category.Construction.Functors using (Functors)
open import Categories.Category.Construction.TwistedArrow using (Codomain)
open import Categories.Category.Equivalence as SE using (StrongEquivalence)
open import Categories.Category.Equivalence.Preserves using (pres-Terminal)
open import Categories.Category.Product using () renaming (Product to _×ᶜ_)
open import Categories.Diagram.End using () renaming (End to ∫)
open import Categories.Diagram.Limit using (Limit)
open import Categories.Diagram.Limit.Properties using (≃-resp-lim)
open import Categories.Diagram.Wedge using (Wedge; module Wedge-Morphism)
open import Categories.Diagram.Wedge.Properties using (ConesTwist≅Wedges)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.Functor.Instance.Twisted using (Twist; Twistⁿⁱ)
open import Categories.Functor.Limits using (Continuous)
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ᵥ_) renaming (_∘ʳ_ to _▹ⁿ_; id to idN)
open import Categories.NaturalTransformation.Dinatural hiding (_≃_)
open import Categories.NaturalTransformation.Equivalence using () renaming (_≃_ to _≃ⁿ_)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism; sym-associator) renaming (_≃_ to _≃ⁱ_)
open import Categories.Object.Terminal as Terminal

import Categories.Category.Construction.Wedges as Wedges
import Categories.Morphism as M
import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e o′ ℓ′ e′ : Level
    P C D E : Category o ℓ e

open Category using (o-level; ℓ-level; e-level)

module _ (F : Bifunctor (Category.op C) C D) where
  open Wedges F

  -- Being an End is the same as being a Terminal object in the category of Wedges
  End⇒Terminal : ∫ F → Terminal Wedges
  End⇒Terminal c =  record
    { ⊤ = wedge
    ; ⊤-is-terminal = record
      { ! = λ {A} → record { u = factor A ; commute = universal }
      ; !-unique = λ {A} f → unique {A} (Wedge-Morphism.commute f)
      }
    }
    where
    open ∫ c

  Terminal⇒End : Terminal Wedges → ∫ F
  Terminal⇒End i = record
    { wedge = ⊤
    ; factor = λ W → u {W₁ = W} !
    ; universal = commute !
    ; unique = λ {_} {g} x → !-unique (record { u = g ; commute = x })
    }
    where
    open Terminal.Terminal i
    open Wedge-Morphism

-- A Natural Transformation between two functors induces an arrow between the
-- (object part of) the respective ends.
module _ {F G : Functor ((Category.op C) ×ᶜ C) D} (F⇒G : NaturalTransformation F G) where
  open ∫ renaming (E to end)
  open Category D

  opaque
    end-η : {{ef : ∫ F}} {{eg : ∫ G}} → end ef ⇒ end eg
    end-η {{ef}} {{eg}} = factor eg (record
      { E = ∫.E ef
      ; dinatural = dtHelper record
        { α = λ c → η (c , c) ∘ dinatural.α ef c
        ; commute = λ {C} {C′} f → begin
          G.₁ (C.id , f) ∘ (η (C , C) ∘ αf C) ∘ D.id       ≈⟨ pullˡ sym-assoc ⟩
          ((G.₁ (C.id , f) ∘ η (C , C)) ∘ αf C) ∘ D.id     ≈⟨ nt.sym-commute (C.id , f) ⟩∘⟨refl ⟩∘⟨refl ⟩
          ((η (C , C′) ∘ F.₁ (C.id , f)) ∘ αf C) ∘ D.id    ≈⟨ assoc²αε ⟩
          η (C , C′) ∘ (F.₁ (C.id , f) ∘ αf C ∘ D.id)      ≈⟨ refl⟩∘⟨ αf-comm f ⟩
          η (C , C′) ∘ F.₁ (f , C.id) ∘ αf C′ ∘ D.id       ≈⟨ assoc²εα ⟩
          ((η (C , C′) ∘ F.₁ (f , C.id)) ∘ αf C′) ∘ D.id   ≈⟨ nt.commute (f , C.id) ⟩∘⟨refl ⟩∘⟨refl ⟩
          ((G.₁ (f , C.id) ∘ η (C′ , C′)) ∘ αf C′) ∘ D.id  ≈⟨ pushˡ assoc ⟩
          G.₁ (f , C.id) ∘ (η (C′ , C′) ∘ αf C′) ∘ D.id    ∎
        }
      })
      where
      module nt = NaturalTransformation F⇒G
      open nt using (η)
      open HomReasoning
      module C = Category C
      module D = Category D
      module F = Functor F
      module G = Functor G
      open DinaturalTransformation (dinatural ef) renaming (α to αf; commute to αf-comm)
      open DinaturalTransformation (dinatural eg) renaming (α to αg; commute to αg-comm)
      open Wedge
      open MR D

-- The real start of the End Calculus. Maybe need to move such properties elsewhere?
-- This is an unpacking of the lhs of Eq. (25) of Loregian's book.
module _ (F : Bifunctor (Category.op C) C D) where
  private
    Eq = ConesTwist≅Wedges F
    module O = M D
  open M (Wedges.Wedges F)
  open Functor

  open StrongEquivalence Eq renaming (F to F⇒; G to F⇐)

  End-yields-limit : ∫ F → Limit (Twist C D F)
  End-yields-limit ef = record { terminal = pres-Terminal (SE.sym Eq) (End⇒Terminal F ef) }

  limit-yields-End : Limit (Twist C D F) → ∫ F
  limit-yields-End l = Terminal⇒End F (pres-Terminal Eq (Limit.terminal l))

  -- Ends and Limits are equivalent, in the category Wedge F
  End-as-Limit : (end : ∫ F) → (l : Limit (Twist C D F)) → ∫.wedge end ≅ F₀ F⇒ (Limit.terminal.⊤ l)
  End-as-Limit end l = Terminal.up-to-iso (Wedges.Wedges F) (End⇒Terminal F end) (pres-Terminal Eq terminal)
    where
    open Limit l

  -- Which then induces that the objects, in D, are also equivalent.
  End-as-Limit-on-Obj : (end : ∫ F) → (l : Limit (Twist C D F)) → ∫.E end O.≅ Limit.apex l
  End-as-Limit-on-Obj end l = record
    { from = Wedge-Morphism.u (M._≅_.from X≅Y)
    ; to = Wedge-Morphism.u (M._≅_.to X≅Y)
    ; iso = record
      { isoˡ = M._≅_.isoˡ X≅Y
      ; isoʳ = M._≅_.isoʳ X≅Y
      }
    }
    where
      X≅Y = End-as-Limit end l
      open Category D
module _ {F : Bifunctor (Category.op C) C D} (ω₁ ω₂ : ∫ F) where
  private
    module ω₁ = ∫ ω₁
    module ω₂ = ∫ ω₂
  open Category D
  open M D
  open _≅_
  open Iso
  open MR D
  open HomReasoning

  end-unique : ∫.E ω₁ ≅ ∫.E ω₂
  end-unique .to = ω₁.factor ω₂.wedge
  end-unique .from = ω₂.factor ω₁.wedge
  end-unique .iso .isoʳ = ω₂.unique′ $ pullˡ ω₂.universal ○ ω₁.universal ○ ⟺ identityʳ
  end-unique .iso .isoˡ = ω₁.unique′ $ pullˡ ω₁.universal ○ ω₂.universal ○ ⟺ identityʳ

module _ {C : Category o ℓ e } {D : Category o′ ℓ′ e′} where
  open MR D
  private
    open module D = Category D
    module C = Category C
    variable
     F G H : Functor ((Category.op C) ×ᶜ C) D
  open HomReasoning
  open NaturalTransformation using (η)

  opaque
    unfolding end-η

    -- "Partial functorality"
    end-identity : {{ef : ∫ F}} → end-η (idN {F = F}) ≈ id
    end-identity {F = F} {{ef}} = ∫.unique ef id-comm

    end-η-commute : {{ef : ∫ F}} {{eg : ∫ G}} (α : NaturalTransformation F G) → 
                    (c : C.Obj) → ∫.dinatural.α eg c ∘ end-η α ≈ α .η (c , c) ∘ ∫.dinatural.α ef c
    end-η-commute ⦃ _ ⦄ ⦃ eg ⦄ α c = ∫.universal eg

    end-η-resp-≈ : {{ef : ∫ F}} {{eg : ∫ G}} {α β : NaturalTransformation F G} →
                   α ≃ⁿ β → end-η α ≈ end-η β
    end-η-resp-≈ {{ef}} {{eg}} e = ∫.unique eg $ ∫.universal eg ○ ⟺ e ⟩∘⟨refl

    end-η-resp-∘ : (α : NaturalTransformation F G) (β : NaturalTransformation G H)
                   {{ef : ∫ F}} {{eg : ∫ G}} {{eh : ∫ H}} →
                   end-η (β ∘ᵥ α) ≈ end-η β ∘ end-η α
    end-η-resp-∘ α β {{ef}} {{eg}} {{eh}} = eh.unique $ extendʳ eh.universal ○ refl⟩∘⟨ eg.universal ○ sym-assoc
      where module eg = ∫ eg
            module eh = ∫ eh

module _ {F G : Functor ((Category.op C) ×ᶜ C) D} (F≃G : F ≃ⁱ G) {{ef : ∫ F}} {{eg : ∫ G}} where
  open Category D
  open M D
  open _≅_
  open Iso
  open HomReasoning
  open module F≃G = NaturalIsomorphism F≃G
  -- a duplicate proof of [_]-resp-≅ for the "partial" case
  end-resp-≅ : ∫.E ef ≅ ∫.E eg
  end-resp-≅ .to = end-η F⇐G
  end-resp-≅ .from = end-η F⇒G
  end-resp-≅ .iso .isoʳ = ⟺ (end-η-resp-∘ F⇐G F⇒G) ○ end-η-resp-≈ {α = F⇒G ∘ᵥ F⇐G} {β = idN} (λ {x} → F≃G.iso.isoʳ x) ○ end-identity {F = G}
  end-resp-≅ .iso .isoˡ = ⟺ (end-η-resp-∘ F⇒G F⇐G) ○ end-η-resp-≈ {α = F⇐G ∘ᵥ F⇒G} {β = idN} (λ {x} → F≃G.iso.isoˡ x) ○ end-identity {F = F}

  -- but really we would like something stronger---that ef implies eg and vice versa
module _ {F G : Functor ((Category.op C) ×ᶜ C) D} (F≃G : F ≃ⁱ G) where
  ≅-yields-end : ∫ F → ∫ G
  ≅-yields-end ef = limit-yields-End G (≃-resp-lim (Twistⁿⁱ C D F≃G) (End-yields-limit F ef))

-- continuous functors preserve ends
module _ {C : Category o ℓ e}
         (J : Bifunctor (Category.op C) C D) (F : Functor D E)
         {cont : Continuous (o ⊔ ℓ) (ℓ ⊔ e) e F} where
  open Category E
  open M E
  open _≅_
  open Iso
  open ∫ hiding (E)
  private
    module F = Functor F
    module J = Bifunctor J
    module E = Category E
  -- i don't have a better name for this
  -- the converse follows only if J reflects limits
  open import Categories.Diagram.Cone.Properties
  open import Categories.Diagram.Limit.Properties

  module _ (ej : ∫ J) where
    private
      module ej = ∫ ej
      j-limit : Limit (Twist C D J)
      j-limit = End-yields-limit J ej
      --new-limit
      f-limit : Limit (F ∘F (J ∘F Codomain C))
      f-limit .Limit.terminal = record
        { ⊤ = F-map-Coneˡ F (Limit.limit j-limit)
        ; ⊤-is-terminal = cont j-limit
        }
      -- for this we merely need to transport across the associator
      f-limit′ : Limit (Twist C E (F ∘F J))
      f-limit′ = ≃-resp-lim (sym-associator (Codomain C) J F) f-limit

    -- really we want IsEnd `F.₀ (∫.E ej)` (F ∘F J)
    contF-as-end : ∫ (F ∘F J)
    contF-as-end = limit-yields-End (F ∘F J) f-limit′
    _ : F.₀ (∫.E ej) ≅ (∫.E contF-as-end)
    _ =  ≅.refl

  Continuous-pres-End : {ej : ∫ J} {ef : ∫ (F ∘F J)} → F.₀ (∫.E ej) ≅ ∫.E ef
  Continuous-pres-End {ej} {ef} = end-unique (contF-as-end ej) ef

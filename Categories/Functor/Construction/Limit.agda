{-# OPTIONS --without-K --safe #-}

module Categories.Functor.Construction.Limit where

open import Function using (_$_)

open import Categories.Category
open import Categories.Category.Construction.Cones
open import Categories.Category.Complete
open import Categories.Category.Cocomplete
open import Categories.Category.Construction.Functors
open import Categories.Functor
open import Categories.NaturalTransformation
open import Categories.Diagram.Cone.Properties
open import Categories.Diagram.Duality

import Categories.Diagram.Limit as Lim
import Categories.Diagram.Cone as Con
import Categories.Morphism.Reasoning as MR

module _ {o ℓ e o′ ℓ′ e′} (C : Category o ℓ e) (Com : Complete o′ ℓ′ e′ C) where
  private
    module C = Category C
  open C
  open HomReasoning
  open Lim.Limit
  open Con.Cone⇒ renaming (commute to ⇒-commute)
  open MR C

  LimitF : ∀ {J : Category o′ ℓ′ e′} → Functor (Functors J C) C
  LimitF {J} = record
    { F₀           = λ F → apex (Com F)
    ; F₁           = λ {F G} α → arr (lim⇒lim α)
    ; identity     = λ {F} → terminal.!-unique (Com F) $ record
      { arr     = C.id
      ; commute = id-comm
      }
    ; homomorphism = λ {F G H} {α β} →
      let module α = NaturalTransformation α
          module β = NaturalTransformation β
      in terminal.!-unique₂ (Com H) {_} {terminal.! (Com H)}
      {record { commute = λ {j} → begin
        proj (Com H) j ∘ arr (lim⇒lim β) ∘ arr (lim⇒lim α) ≈⟨ pullˡ (⇒-commute (lim⇒lim β)) ⟩
        (β.η j ∘ proj (Com G) j) ∘ arr (lim⇒lim α)         ≈⟨ assoc ⟩
        β.η j ∘ proj (Com G) j ∘ arr (lim⇒lim α)           ≈⟨ pushʳ (⇒-commute (lim⇒lim α)) ⟩
        (β.η j ∘ α.η j) ∘ proj (Com F) j                   ∎ }}
    ; F-resp-≈     = λ {F G} {α β} eq → terminal.!-unique (Com G) $ record
      { commute = ⇒-commute (lim⇒lim β) ○ ∘-resp-≈ˡ (⟺ eq)
      }
    }
    where module J = Category J
          lim⇒lim : ∀ {F G : Functor J C} (α : NaturalTransformation F G) →
                      Cones G [ nat-map-Cone α (limit (Com F)) , limit (Com G) ]
          lim⇒lim {F} {G} α = rep-cone (Com G) (nat-map-Cone α (limit (Com F)))


module _ {o ℓ e o′ ℓ′ e′} (C : Category o ℓ e) (Coc : Cocomplete o′ ℓ′ e′ C) where
  private
    module C = Category C
  open C

  ColimitF : ∀ {J : Category o′ ℓ′ e′} → Functor (Functors J C) C
  ColimitF {J} = Functor.op LF ∘F opF⇐
    where Com : Complete o′ ℓ′ e′ C.op
          Com F = Colimit⇒coLimit C (Coc (Functor.op F))
          LF  : Functor (Functors (Category.op J) op) C.op
          LF    = LimitF C.op Com {Category.op J}

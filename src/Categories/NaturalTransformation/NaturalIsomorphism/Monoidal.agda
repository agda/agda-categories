{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Monoidal
open import Categories.Functor.Monoidal

module Categories.NaturalTransformation.NaturalIsomorphism.Monoidal
  where

open import Level
open import Data.Product using (_,_)
open import Relation.Binary using (IsEquivalence; Setoid)

open import Categories.Category.Product
import Categories.Category.Monoidal.Reasoning as MonoidalReasoning
import Categories.Category.Monoidal.Utilities as MonoidalUtilities
open import Categories.Functor hiding (id)
open import Categories.Functor.Monoidal.Properties using () renaming
  ( idF-Monoidal to idFˡ  ; idF-StrongMonoidal to idFˢ
  ; ∘-Monoidal   to _∘Fˡ_ ; ∘-StrongMonoidal   to _∘Fˢ_
  )
import Categories.Morphism.Reasoning as MorphismReasoning
import Categories.NaturalTransformation.Monoidal as NT
open import Categories.NaturalTransformation.NaturalIsomorphism as NI
  using (NaturalIsomorphism)

open NaturalIsomorphism using (F⇒G; F⇐G)

-- Monoidal natural isomorphisms between lax monoidal functors.

module Lax where
  open NT.Lax hiding (id)

  module _ {o ℓ e o′ ℓ′ e′}
           {C : MonoidalCategory o ℓ e} {D : MonoidalCategory o′ ℓ′ e′}
           (F G : MonoidalFunctor C D) where

    private
      module C = MonoidalCategory C
      module D = MonoidalCategory D
      module F = MonoidalFunctor F renaming (F to U)
      module G = MonoidalFunctor G renaming (F to U)

    IsMonoidalNaturalIsomorphism : NaturalIsomorphism F.U G.U → Set (o ⊔ ℓ′ ⊔ e′)
    IsMonoidalNaturalIsomorphism α = IsMonoidalNaturalTransformation F G (F⇒G α)

    record MonoidalNaturalIsomorphism : Set (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) where
      field
        U              : NaturalIsomorphism F.U G.U
        F⇒G-isMonoidal : IsMonoidalNaturalIsomorphism U

      open NaturalIsomorphism              U              public
      open IsMonoidalNaturalTransformation F⇒G-isMonoidal public

      open D using (module Equiv)
      open MorphismReasoning D.U using (switch-fromtoˡ; conjugate-from)
      open MonoidalUtilities D.monoidal using (_⊗ᵢ_)

      F⇐G-isMonoidal : IsMonoidalNaturalTransformation G F (F⇐G U)
      F⇐G-isMonoidal = record
        { ε-compat      = Equiv.sym (switch-fromtoˡ FX≅GX ε-compat)
        ; ⊗-homo-compat =
            conjugate-from (FX≅GX ⊗ᵢ FX≅GX) FX≅GX (Equiv.sym ⊗-homo-compat)
        }

      F⇒G-monoidal : MonoidalNaturalTransformation F G
      F⇒G-monoidal = record { U = F⇒G U ; isMonoidal = F⇒G-isMonoidal }

      F⇐G-monoidal : MonoidalNaturalTransformation G F
      F⇐G-monoidal = record { U = F⇐G U ; isMonoidal = F⇐G-isMonoidal }

    infix 4 _≃_

    _≃_ = MonoidalNaturalIsomorphism

  open MonoidalNaturalTransformation using (isMonoidal)
  open MonoidalNaturalIsomorphism

  -- Identity and compositions

  module _ {o ℓ e o′ ℓ′ e′}
           {C : MonoidalCategory o ℓ e} {D : MonoidalCategory o′ ℓ′ e′} where

    infixr 9 _ⓘᵥ_

    id : {F : MonoidalFunctor C D} → F ≃ F
    id = record { U = NI.refl ; F⇒G-isMonoidal = isMonoidal NT.Lax.id }

    _ⓘᵥ_ : {F G H : MonoidalFunctor C D} → G ≃ H → F ≃ G → F ≃ H
    _ⓘᵥ_ α β = record
      { U              = U α NI.ⓘᵥ U β
      ; F⇒G-isMonoidal = isMonoidal (F⇒G-monoidal α ∘ᵥ F⇒G-monoidal β)
      }

    isEquivalence : IsEquivalence _≃_
    isEquivalence = record
      { refl  = id
      ; sym   = λ α → record
        { U              = NI.sym (U α)
        ; F⇒G-isMonoidal = F⇐G-isMonoidal α
        }
      ; trans = λ α β → β ⓘᵥ α
      }

  module _ {o ℓ e o′ ℓ′ e′ o″ ℓ″ e″}
           {C : MonoidalCategory o ℓ e} {D : MonoidalCategory o′ ℓ′ e′}
           {E : MonoidalCategory o″ ℓ″ e″} where

    infixr 9 _ⓘₕ_ _ⓘˡ_ _ⓘʳ_

    _ⓘₕ_ : {F G : MonoidalFunctor C D} {H I : MonoidalFunctor D E} →
            H ≃ I → F ≃ G → (H ∘Fˡ F) ≃ (I ∘Fˡ G)
    _ⓘₕ_ α β = record
      { U              = U α NI.ⓘₕ U β
      ; F⇒G-isMonoidal = isMonoidal (F⇒G-monoidal α ∘ₕ F⇒G-monoidal β)
      }

    _ⓘˡ_ : {F G : MonoidalFunctor C D}
           (H : MonoidalFunctor D E) → F ≃ G → (H ∘Fˡ F) ≃ (H ∘Fˡ G)
    H ⓘˡ α = id {F = H} ⓘₕ α

    _ⓘʳ_ : {G H : MonoidalFunctor D E} →
           G ≃ H → (F : MonoidalFunctor C D) → (G ∘Fˡ F) ≃ (H ∘Fˡ F)
    α ⓘʳ F = α ⓘₕ id {F = F}

  -- Left and right unitors.

  module _ {o ℓ e o′ ℓ′ e′}
           {C : MonoidalCategory o ℓ e} {D : MonoidalCategory o′ ℓ′ e′}
           {F : MonoidalFunctor C D} where
    private
      module C = MonoidalCategory C
      module D = MonoidalCategory D
      module F = MonoidalFunctor F
    open D hiding (U; id; unitorˡ; unitorʳ)
    open MorphismReasoning D.U using (id-comm-sym)
    open MonoidalReasoning D.monoidal

    unitorˡ : idFˡ D ∘Fˡ F ≃ F
    unitorˡ = record
      { U = NI.unitorˡ
      ; F⇒G-isMonoidal = record
        { ε-compat      = identityˡ ○ identityʳ
        ; ⊗-homo-compat = λ {X Y} → begin
            D.id D.∘ F.⊗-homo.η (X , Y) D.∘ D.id  ≈⟨ identityˡ ⟩
            F.⊗-homo.η (X , Y) D.∘ D.id           ≈˘⟨ refl⟩∘⟨ ⊗.identity ⟩
            F.⊗-homo.η (X , Y) D.∘ D.id ⊗₁ D.id   ∎
        }
      }

    unitorʳ : F ∘Fˡ idFˡ C ≃ F
    unitorʳ = record
      { U               = NI.unitorʳ
      ; F⇒G-isMonoidal  = record
        { ε-compat      = begin
            D.id ∘ F.₁ C.id ∘ F.ε  ≈⟨ identityˡ ⟩
            F.₁ C.id ∘ F.ε         ≈⟨ F.identity ⟩∘⟨refl ⟩
            D.id ∘ F.ε             ≈⟨ identityˡ ⟩
            F.ε ∎ 
        ; ⊗-homo-compat = λ {X Y} → begin
            D.id D.∘ F.₁ C.id ∘ F.⊗-homo.η (X , Y)  ≈⟨ identityˡ ⟩
            F.₁ C.id ∘ F.⊗-homo.η (X , Y)           ≈⟨ F.identity ⟩∘⟨refl ⟩
            D.id ∘ F.⊗-homo.η (X , Y)               ≈⟨ id-comm-sym ⟩
            F.⊗-homo.η (X , Y) D.∘ D.id             ≈˘⟨ refl⟩∘⟨ ⊗.identity ⟩
            F.⊗-homo.η (X , Y) D.∘ D.id ⊗₁ D.id     ∎
        }
      }

  -- Associator.

  module _ {o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ o‴ ℓ‴ e‴}
           {B : MonoidalCategory o ℓ e} {C : MonoidalCategory o′ ℓ′ e′}
           {D : MonoidalCategory o″ ℓ″ e″} {E : MonoidalCategory o‴ ℓ‴ e‴}
           {F : MonoidalFunctor B C} {G : MonoidalFunctor C D}
           {H : MonoidalFunctor D E} where
    private
      module D = MonoidalCategory D
      module E = MonoidalCategory E
      module F = MonoidalFunctor F
      module G = MonoidalFunctor G
      module H = MonoidalFunctor H
    open E hiding (U; id; associator)
    open MorphismReasoning E.U
    open MonoidalReasoning E.monoidal

    associator : (H ∘Fˡ G) ∘Fˡ F ≃ H ∘Fˡ (G ∘Fˡ F)
    associator = record
      { U               = NI.associator (F.F) (G.F) (H.F)
      ; F⇒G-isMonoidal  = record
        { ε-compat      = begin
            E.id ∘ H.₁ (G.₁ F.ε) ∘ H.₁ G.ε ∘ H.ε  ≈⟨ identityˡ ⟩
            H.₁ (G.₁ F.ε) ∘ H.₁ G.ε ∘ H.ε         ≈˘⟨ pushˡ H.homomorphism ⟩
            H.₁ (G.₁ F.ε D.∘ G.ε) ∘ H.ε           ∎
        ; ⊗-homo-compat = λ {X Y} → begin
            E.id ∘ H.₁ (G.₁ (F.⊗-homo.η (X , Y))) ∘
            H.₁ (G.⊗-homo.η (F.F₀ X , F.F₀ Y)) ∘
            H.⊗-homo.η (G.F₀ (F.F₀ X) , G.F₀ (F.F₀ Y))
          ≈⟨ identityˡ ⟩
            H.₁ (G.₁ (F.⊗-homo.η (X , Y))) ∘
            H.₁ (G.⊗-homo.η (F.F₀ X , F.F₀ Y)) ∘
            H.⊗-homo.η (G.F₀ (F.F₀ X) , G.F₀ (F.F₀ Y))
          ≈˘⟨ pushˡ H.homomorphism ⟩
            H.₁ (G.₁ (F.⊗-homo.η (X , Y)) D.∘ G.⊗-homo.η (F.F₀ X , F.F₀ Y)) ∘
            H.⊗-homo.η (G.F₀ (F.F₀ X) , G.F₀ (F.F₀ Y))
          ≈˘⟨ identityʳ ⟩
            (H.₁ (G.₁ (F.⊗-homo.η (X , Y)) D.∘ G.⊗-homo.η (F.F₀ X , F.F₀ Y)) ∘
            H.⊗-homo.η (G.F₀ (F.F₀ X) , G.F₀ (F.F₀ Y))) ∘ E.id
          ≈˘⟨ refl⟩∘⟨ ⊗.identity ⟩
            (H.₁ (G.₁ (F.⊗-homo.η (X , Y)) D.∘ G.⊗-homo.η (F.F₀ X , F.F₀ Y)) ∘
             H.⊗-homo.η (G.F₀ (F.F₀ X) , G.F₀ (F.F₀ Y))) ∘
            E.id ⊗₁ E.id
          ∎
        }
      }

-- Monoidal natural isomorphisms between strong monoidal functors.

module Strong where
  open NT.Strong using (IsMonoidalNaturalTransformation)
  open StrongMonoidalFunctor renaming (F to UF; monoidalFunctor to laxF)

  module _ {o ℓ e o′ ℓ′ e′}
           {C : MonoidalCategory o ℓ e} {D : MonoidalCategory o′ ℓ′ e′}
           (F G : StrongMonoidalFunctor C D) where

    IsMonoidalNaturalIsomorphism : NaturalIsomorphism (UF F) (UF G) →
                                   Set (o ⊔ ℓ′ ⊔ e′)
    IsMonoidalNaturalIsomorphism α = IsMonoidalNaturalTransformation F G (F⇒G α)

    -- NOTE. This record contains the same data as the lax version,
    -- but the type arguments are different.  This helps type
    -- inference by providing the right constraints.

    record MonoidalNaturalIsomorphism : Set (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) where
      field
        U              : NaturalIsomorphism (UF F) (UF G)
        F⇒G-isMonoidal : IsMonoidalNaturalIsomorphism U

      laxNI : Lax.MonoidalNaturalIsomorphism (laxF F) (laxF G)
      laxNI = record { U = U ; F⇒G-isMonoidal = F⇒G-isMonoidal }
      open Lax.MonoidalNaturalIsomorphism laxNI public
        hiding (U; F⇒G-isMonoidal)

    infix 4 _≃_

    _≃_ = MonoidalNaturalIsomorphism

  open MonoidalNaturalIsomorphism

  module _ {o ℓ e o′ ℓ′ e′}
           {C : MonoidalCategory o ℓ e} {D : MonoidalCategory o′ ℓ′ e′} where

    infixr 9 _ⓘᵥ_

    -- Since they contain the same data, we can strengthen a lax
    -- monoidal isomorphism to a strong one.

    strengthen : {F G : StrongMonoidalFunctor C D} →
                 (laxF F) Lax.≃ (laxF G) → F ≃ G
    strengthen α = record { U = L.U ; F⇒G-isMonoidal = L.F⇒G-isMonoidal }
      where module L = Lax.MonoidalNaturalIsomorphism α

    -- Identity and compositions

    id : {F : StrongMonoidalFunctor C D} → F ≃ F
    id = strengthen Lax.id

    _ⓘᵥ_ : {F G H : StrongMonoidalFunctor C D} → G ≃ H → F ≃ G → F ≃ H
    α ⓘᵥ β = strengthen (laxNI α Lax.ⓘᵥ laxNI β)

    isEquivalence : IsEquivalence _≃_
    isEquivalence = record
      { refl  = λ {F} → id {F}
      ; sym   = λ α → record
        { U              = NI.sym (U α)
        ; F⇒G-isMonoidal = F⇐G-isMonoidal α
        }
      ; trans = λ {F} {G} {H} α β → _ⓘᵥ_ {F} {G} {H} β α
      }

  module _ {o ℓ e o′ ℓ′ e′ o″ ℓ″ e″}
           {C : MonoidalCategory o ℓ e} {D : MonoidalCategory o′ ℓ′ e′}
           {E : MonoidalCategory o″ ℓ″ e″} where

    open Lax.MonoidalNaturalIsomorphism
    
    infixr 9 _ⓘₕ_ _ⓘˡ_ _ⓘʳ_

    _ⓘₕ_ : {F G : StrongMonoidalFunctor C D} {H I : StrongMonoidalFunctor D E} →
            H ≃ I → F ≃ G → (H ∘Fˢ F) ≃ (I ∘Fˢ G)
    -- FIXME: this definition is clearly equivalent to
    --
    --   α ⓘₕ β = strengthen (laxNI α Lax.ⓘₕ laxNI β)
    --
    -- but the latter takes an unreasonably long time to typecheck,
    -- while the unfolded version typechecks almost immediately.
    α ⓘₕ β = record
      { U               = L.U
      ; F⇒G-isMonoidal  = record
        { ε-compat      = L.ε-compat
        ; ⊗-homo-compat = L.⊗-homo-compat }
        }
      where
        module L = Lax.MonoidalNaturalIsomorphism (laxNI α Lax.ⓘₕ laxNI β)

    _ⓘˡ_ : {F G : StrongMonoidalFunctor C D}
           (H : StrongMonoidalFunctor D E) → F ≃ G → (H ∘Fˢ F) ≃ (H ∘Fˢ G)
    H ⓘˡ α = id {F = H} ⓘₕ α

    _ⓘʳ_ : {G H : StrongMonoidalFunctor D E} →
           G ≃ H → (F : StrongMonoidalFunctor C D) → (G ∘Fˢ F) ≃ (H ∘Fˢ F)
    α ⓘʳ F = α ⓘₕ id {F = F}

  -- Left and right unitors.

  module _ {o ℓ e o′ ℓ′ e′}
           {C : MonoidalCategory o ℓ e} {D : MonoidalCategory o′ ℓ′ e′}
           {F : StrongMonoidalFunctor C D} where

    unitorˡ : idFˢ D ∘Fˢ F ≃ F
    -- FIXME: Again, this unfolded definition typechecks considerably
    -- faster than the equivalent
    --
    --   strengthen (Lax.unitorʳ {F = laxF F})
    unitorˡ = record
      { U               = L.U
      ; F⇒G-isMonoidal  = record
        { ε-compat      = L.ε-compat
        ; ⊗-homo-compat = L.⊗-homo-compat
        }
      }
      where module L = Lax.MonoidalNaturalIsomorphism (Lax.unitorˡ {F = laxF F})

    unitorʳ : F ∘Fˢ idFˢ C ≃ F
    -- FIXME: ... same here ...
    unitorʳ = record
      { U               = L.U
      ; F⇒G-isMonoidal  = record
        { ε-compat      = L.ε-compat
        ; ⊗-homo-compat = L.⊗-homo-compat
        }
      }
      where module L = Lax.MonoidalNaturalIsomorphism (Lax.unitorʳ {F = laxF F})

  -- Associator.

  module _ {o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ o‴ ℓ‴ e‴}
           {B : MonoidalCategory o ℓ e} {C : MonoidalCategory o′ ℓ′ e′}
           {D : MonoidalCategory o″ ℓ″ e″} {E : MonoidalCategory o‴ ℓ‴ e‴}
           {F : StrongMonoidalFunctor B C} {G : StrongMonoidalFunctor C D}
           {H : StrongMonoidalFunctor D E} where

    associator : (H ∘Fˢ G) ∘Fˢ F ≃ H ∘Fˢ (G ∘Fˢ F)
    -- FIXME: ... and here.  Though, for this one, even the unfolded
    -- version takes a lot of time.
    associator = record
      { U               = L.U
      ; F⇒G-isMonoidal  = record
        { ε-compat      = L.ε-compat
        ; ⊗-homo-compat = L.⊗-homo-compat
        }
      }
      where
        α = Lax.associator {F = laxF F} {laxF G} {laxF H}
        module L = Lax.MonoidalNaturalIsomorphism α

{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Monoidal

-- Monoidal natural transformations between lax and strong monoidal functors.
--
-- See
--  * John Baez, Some definitions everyone should know,
--    https://math.ucr.edu/home/baez/qg-fall2004/definitions.pdf
--  * https://ncatlab.org/nlab/show/monoidal+natural+transformation

module Categories.NaturalTransformation.Monoidal where

open import Level
open import Data.Product using (_,_)

open import Categories.Category using (module Commutation)
open import Categories.Category.Product
import Categories.Category.Monoidal.Reasoning as MonoidalReasoning
open import Categories.Functor.Monoidal
open import Categories.Functor.Monoidal.Properties using ()
  renaming (∘-Monoidal to _∘Fˡ_; ∘-StrongMonoidal to _∘Fˢ_)
import Categories.Morphism as Morphism
import Categories.Morphism.Reasoning as MorphismReasoning
open import Categories.NaturalTransformation as NT using (NaturalTransformation)

open NaturalTransformation renaming (η to _[_])

module Lax where

  module _ {o ℓ e o′ ℓ′ e′}
           {C : MonoidalCategory o ℓ e} {D : MonoidalCategory o′ ℓ′ e′}
           (F G : MonoidalFunctor C D) where

    private
      module C = MonoidalCategory C
      module D = MonoidalCategory D
      module F = MonoidalFunctor F renaming (F to U)
      module G = MonoidalFunctor G renaming (F to U)
    open D hiding (U; id)
    open Commutation D.U

    -- Monoidal natural transformations between lax monoidal functors.

    record IsMonoidalNaturalTransformation (β : NaturalTransformation F.U G.U)
           : Set (o ⊔ ℓ′ ⊔ e′) where
      field
        ε-compat      : [ unit ⇒ G.₀ C.unit  ]⟨
                          F.ε          ⇒⟨ F.₀ C.unit ⟩
                          β [ C.unit ]
                        ≈ G.ε
                        ⟩
        ⊗-homo-compat : ∀ {X Y} →
                        [ F.₀ X ⊗₀ F.₀ Y ⇒ G.₀ (X C.⊗₀ Y) ]⟨
                          F.⊗-homo [ (X , Y) ]  ⇒⟨ F.₀ (X C.⊗₀ Y) ⟩
                          β [ X C.⊗₀ Y ]
                        ≈ β [ X ] ⊗₁ β [ Y ]    ⇒⟨ G.₀ X ⊗₀ G.₀ Y ⟩
                          G.⊗-homo [ (X , Y) ]
                        ⟩

    record MonoidalNaturalTransformation : Set (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) where
      field
        U          : NaturalTransformation F.U G.U
        isMonoidal : IsMonoidalNaturalTransformation U

      open NaturalTransformation           U          public
      open IsMonoidalNaturalTransformation isMonoidal public


  -- To shorten some definitions
  private _⇛_ = MonoidalNaturalTransformation

  -- Identity and compositions

  module _ {o ℓ e o′ ℓ′ e′}
           {C : MonoidalCategory o ℓ e} {D : MonoidalCategory o′ ℓ′ e′} where

    private
      module C = MonoidalCategory C
      module D = MonoidalCategory D
    open D hiding (U; id)
    open MorphismReasoning D.U
    open MonoidalReasoning D.monoidal

    infixr 9 _∘ᵥ_

    id : {F : MonoidalFunctor C D} → F ⇛ F
    id {F} = record
      { U               = NT.id
      ; isMonoidal      = record
        { ε-compat      = D.identityˡ
        ; ⊗-homo-compat = λ {X Y} → begin
            D.id ∘ ⊗-homo.η (X , Y)          ≈⟨ id-comm-sym ⟩
            ⊗-homo.η (X , Y) ∘ D.id          ≈˘⟨ refl⟩∘⟨ ⊗.identity ⟩
            ⊗-homo.η (X , Y) ∘ D.id ⊗₁ D.id  ∎
        }
      }
      where open MonoidalFunctor F

    _∘ᵥ_ : {F G H : MonoidalFunctor C D} → G ⇛ H → F ⇛ G → F ⇛ H
    _∘ᵥ_ {F} {G} {H} αᵐ βᵐ = record
      { U               = α NT.∘ᵥ β
      ; isMonoidal      = record
        { ε-compat      = begin
            (α [ _ ] ∘ β [ _ ]) ∘ F.ε   ≈⟨ pullʳ (ε-compat βᵐ) ⟩
            α [ _ ] ∘ G.ε               ≈⟨ ε-compat αᵐ ⟩
            H.ε                         ∎
        ; ⊗-homo-compat = λ {X Y} → begin
              (α [ X C.⊗₀ Y ] ∘ β [ X C.⊗₀ Y ]) ∘ F.⊗-homo.η (X , Y)
            ≈⟨ pullʳ (⊗-homo-compat βᵐ) ⟩
              α [ X C.⊗₀ Y ] ∘ G.⊗-homo.η (X , Y) ∘ β [ X ] ⊗₁ β [ Y ]
            ≈⟨ extendʳ (⊗-homo-compat αᵐ) ⟩
              H.⊗-homo.η (X , Y) ∘ α [ X ] ⊗₁ α [ Y ] ∘ β [ X ] ⊗₁ β [ Y ]
            ≈˘⟨ refl⟩∘⟨ ⊗-distrib-over-∘ ⟩
              H.⊗-homo.η (X , Y) ∘ (α [ X ] ∘ β [ X ]) ⊗₁ (α [ Y ] ∘ β [ Y ])
            ∎
        }
      }
      where
        open MonoidalNaturalTransformation
        α = U αᵐ
        β = U βᵐ
        module F = MonoidalFunctor F
        module G = MonoidalFunctor G
        module H = MonoidalFunctor H

  module _ {o ℓ e o′ ℓ′ e′ o″ ℓ″ e″}
           {C : MonoidalCategory o ℓ e} {D : MonoidalCategory o′ ℓ′ e′}
           {E : MonoidalCategory o″ ℓ″ e″} where
    private
      module C = MonoidalCategory C
      module D = MonoidalCategory D
      module E = MonoidalCategory E
      open E hiding (U; id)
      open MorphismReasoning E.U
      open MonoidalReasoning E.monoidal

    infixr 9 _∘ₕ_ _∘ˡ_ _∘ʳ_

    _∘ₕ_ : {F G : MonoidalFunctor C D} {H I : MonoidalFunctor D E} →
            H ⇛ I → F ⇛ G → (H ∘Fˡ F) ⇛ (I ∘Fˡ G)
    _∘ₕ_ {F} {G} {H} {I} αᵐ βᵐ = record
      { U               = α NT.∘ₕ β
      ; isMonoidal      = record
        { ε-compat      = begin
            (I.₁ (β [ C.unit ]) ∘ α [ F.₀ C.unit ]) ∘ H.₁ F.ε ∘ H.ε
          ≈⟨ extend² (commute αᵐ F.ε) ⟩
            (I.₁ (β [ C.unit ]) ∘ I.₁ F.ε) ∘ α [ D.unit ] ∘ H.ε
          ≈˘⟨ I.homomorphism ⟩∘⟨refl ⟩
            I.₁ (β [ C.unit ] D.∘ F.ε) ∘ α [ D.unit ] ∘ H.ε
          ≈⟨ I.F-resp-≈ (ε-compat βᵐ) ⟩∘⟨ ε-compat αᵐ ⟩
            I.F₁ G.ε ∘ I.ε
          ∎
        ; ⊗-homo-compat = λ {X Y} → begin
            (I.₁ (β [ X C.⊗₀ Y ]) ∘ α [ F.₀ (X C.⊗₀ Y) ]) ∘
            H.₁ (F.⊗-homo.η (X , Y)) ∘ H.⊗-homo.η (F.₀ X , F.₀ Y)
          ≈⟨ extend² (commute αᵐ (F.⊗-homo.η (X , Y))) ⟩
            (I.₁ (β [ X C.⊗₀ Y ]) ∘ I.₁ (F.⊗-homo.η (X , Y))) ∘
            α [ F.₀ X D.⊗₀ F.₀ Y ] ∘ H.⊗-homo.η (F.₀ X , F.₀ Y)
          ≈˘⟨ I.homomorphism ⟩∘⟨refl ⟩
            (I.₁ (β [ X C.⊗₀ Y ] D.∘ F.⊗-homo.η (X , Y))) ∘
            α [ F.₀ X D.⊗₀ F.₀ Y ] ∘ H.⊗-homo.η (F.₀ X , F.₀ Y)
          ≈⟨ (I.F-resp-≈ (⊗-homo-compat βᵐ) ⟩∘⟨ ⊗-homo-compat αᵐ) ⟩
            (I.₁ (G.⊗-homo.η (X , Y) D.∘ β [ X ] D.⊗₁ β [ Y ])) ∘
            I.⊗-homo.η (F.₀ X , F.₀ Y) ∘ α [ F.₀ X ] ⊗₁ α [ F.₀ Y ]
          ≈⟨ I.homomorphism ⟩∘⟨refl ⟩
            (I.₁ (G.⊗-homo.η (X , Y)) ∘ I.₁ (β [ X ] D.⊗₁ β [ Y ])) ∘
            I.⊗-homo.η (F.₀ X , F.₀ Y) ∘ α [ F.₀ X ] ⊗₁ α [ F.₀ Y ]
          ≈˘⟨ extend² (I.⊗-homo.commute ((β [ X ]) , (β [ Y ]))) ⟩
            (I.₁ (G.⊗-homo.η (X , Y)) ∘ I.⊗-homo.η (G.₀ X , G.₀ Y)) ∘
            I.₁ (β [ X ]) ⊗₁ I.₁ (β [ Y ]) ∘ α [ F.₀ X ] ⊗₁ α [ F.₀ Y ]
          ≈˘⟨ refl⟩∘⟨ ⊗-distrib-over-∘ ⟩
            (I.₁ (G.⊗-homo.η (X , Y)) ∘ I.⊗-homo.η (G.₀ X , G.₀ Y)) ∘
            (I.₁ (β [ X ]) ∘ α [ F.₀ X ]) ⊗₁ (I.₁ (β [ Y ]) ∘ α [ F.₀ Y ])
          ∎
        }
      }
      where
        open MonoidalNaturalTransformation
        α = U αᵐ
        β = U βᵐ
        module F = MonoidalFunctor F
        module G = MonoidalFunctor G
        module H = MonoidalFunctor H
        module I = MonoidalFunctor I

    _∘ˡ_ : {F G : MonoidalFunctor C D}
           (H : MonoidalFunctor D E) → F ⇛ G → (H ∘Fˡ F) ⇛ (H ∘Fˡ G)
    H ∘ˡ α = id {F = H} ∘ₕ α

    _∘ʳ_ : {G H : MonoidalFunctor D E} →
           G ⇛ H → (F : MonoidalFunctor C D) → (G ∘Fˡ F) ⇛ (H ∘Fˡ F)
    α ∘ʳ F = α ∘ₕ id {F = F}

module Strong where
  open StrongMonoidalFunctor
    using () renaming (F to UF; monoidalFunctor to laxF)

  module _ {o ℓ e o′ ℓ′ e′}
           {C : MonoidalCategory o ℓ e} {D : MonoidalCategory o′ ℓ′ e′}
           (F G : StrongMonoidalFunctor C D) where

    -- Monoidal natural transformations between strong monoidal functors.

    IsMonoidalNaturalTransformation : NaturalTransformation (UF F) (UF G) →
                                      Set (o ⊔ ℓ′ ⊔ e′)
    IsMonoidalNaturalTransformation α =
      Lax.IsMonoidalNaturalTransformation (laxF F) (laxF G) α

    -- NOTE. This record contains the same data as the lax version,
    -- but the type arguments are different.  This helps type
    -- inference by providing the right constraints.

    record MonoidalNaturalTransformation : Set (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) where
      field
        U          : NaturalTransformation (UF F) (UF G)
        isMonoidal : IsMonoidalNaturalTransformation U

      laxNT : Lax.MonoidalNaturalTransformation (laxF F) (laxF G)
      laxNT = record { U = U ; isMonoidal = isMonoidal }
      open Lax.MonoidalNaturalTransformation laxNT public hiding (U; isMonoidal)

  private _⇛_ = MonoidalNaturalTransformation

  open MonoidalNaturalTransformation

  module _ {o ℓ e o′ ℓ′ e′}
           {C : MonoidalCategory o ℓ e} {D : MonoidalCategory o′ ℓ′ e′} where

    infixr 9 _∘ᵥ_

    -- Since they contain the same data, we can strengthen a lax
    -- monoidal transformation to a strong one.

    strengthen : {F G : StrongMonoidalFunctor C D} →
                 Lax.MonoidalNaturalTransformation (laxF F) (laxF G) → F ⇛ G
    strengthen α = record { U = L.U ; isMonoidal = L.isMonoidal }
      where module L = Lax.MonoidalNaturalTransformation α

    -- Identity and compositions

    id : {F : StrongMonoidalFunctor C D} → F ⇛ F
    id = strengthen Lax.id

    _∘ᵥ_ : {F G H : StrongMonoidalFunctor C D} → G ⇛ H → F ⇛ G → F ⇛ H
    α ∘ᵥ β = strengthen (laxNT α Lax.∘ᵥ laxNT β)

  module _ {o ℓ e o′ ℓ′ e′ o″ ℓ″ e″}
           {C : MonoidalCategory o ℓ e} {D : MonoidalCategory o′ ℓ′ e′}
           {E : MonoidalCategory o″ ℓ″ e″} where

    open Lax.MonoidalNaturalTransformation

    infixr 9 _∘ₕ_ _∘ˡ_ _∘ʳ_

    _∘ₕ_ : {F G : StrongMonoidalFunctor C D} {H I : StrongMonoidalFunctor D E} →
            H ⇛ I → F ⇛ G → (H ∘Fˢ F) ⇛ (I ∘Fˢ G)
    -- FIXME: this definition is clearly equivalent to
    --
    --   α ∘ₕ β = strengthen (laxNT α Lax.∘ₕ laxNT β)
    --
    -- but the latter takes an unreasonably long time to typecheck,
    -- while the unfolded version typechecks almost immediately.
    α ∘ₕ β = record
      { U               = L.U
      ; isMonoidal      = record
        { ε-compat      = L.ε-compat
        ; ⊗-homo-compat = L.⊗-homo-compat }
        }
      where
        module L = Lax.MonoidalNaturalTransformation (laxNT α Lax.∘ₕ laxNT β)

    _∘ˡ_ : {F G : StrongMonoidalFunctor C D}
           (H : StrongMonoidalFunctor D E) → F ⇛ G → (H ∘Fˢ F) ⇛ (H ∘Fˢ G)
    H ∘ˡ α  = id {F = H} ∘ₕ α

    _∘ʳ_ : {G H : StrongMonoidalFunctor D E} →
           G ⇛ H → (F : StrongMonoidalFunctor C D) → (G ∘Fˢ F) ⇛ (H ∘Fˢ F)
    α ∘ʳ F = α ∘ₕ id {F = F}

{-# OPTIONS --without-K --safe #-}

-- See https://ncatlab.org/nlab/show/graded+monad

module Categories.Monad.Graded where

open import Level
open import Data.Product using (_,_)

open import Categories.Category using (Category; _[_,_]; _[_≈_])
open import Categories.Category.Construction.Functors using (Functors)
open import Categories.Category.Monoidal using (MonoidalCategory)
open import Categories.Category.Monoidal.Construction.Endofunctors using (Endofunctors)
import Categories.Category.Monoidal.Utilities as Utilities
import Categories.Category.Monoidal.Properties as Properties
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Monoidal using (MonoidalFunctor)
import Categories.Morphism.Reasoning as MorphismReasoning
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)

private
  variable
    o ℓ e  o′ ℓ′ e′ : Level

open Category using (Obj)
open MonoidalCategory using (Obj; U; monoidal)
open Functor renaming (F₀ to _$₀_; F₁ to _$₁_)
open NaturalTransformation

-- The compact definition of a V-graded monad in a category C taken
-- from nLab.  See https://ncatlab.org/nlab/show/graded+monad for
-- details.

GradedMonad : MonoidalCategory o ℓ e → Category o′ ℓ′ e′ →
              Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′)
GradedMonad V C = MonoidalFunctor V (Endofunctors C)

-- An alternate Kleisli-triple-style definition of graded monads that
-- is more useful for modeling computational effects.  This
-- definition is inspired by Katsumata's `Parametric Effect Monads'
-- [1] and by Orchard, Petricek and Mycroft's `indexed monads' [2, 3].
--
--  [1] S. Katsumata. Parametric effect monads and semantics of effect
--      systems. POPL '14. https://doi.org/10.1145/2535838.2535846
--
--  [2] D. Orchard and T. Petricek. Embedding effect systems in
--      Haskell. Haskell '14. https://doi.org/10.1145/2633357.2633368
--
--  [3] D. Orchard, T. Petricek and A. Mycroft. The semantic marriage
--      of monads and effects.  arXiv:1401.5391 (2014).
--      https://doi.org/10.48550/arXiv.1401.5391

record GradedKleisliTriple (V : MonoidalCategory o ℓ e) (C : Category o′ ℓ′ e′)
  : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  open Category C
  open MonoidalCategory V using (_⊗₀_; _⊗₁_; unit)
    renaming (_⇒_ to _≤_; id to idV; _∘_ to _∙_; _≈_ to _∼_)
  open Utilities.Shorthands (monoidal V)

  field

    T₀ : Obj V → Obj C → Obj C   -- The action of T on objects

    -- Graded Kelisli extension (aka `Kleisli lifting')

    ext : ∀ u {v A B} → (A ⇒ T₀ v B) → (T₀ u A ⇒ T₀ (u ⊗₀ v) B)

    -- Graded unit (aka `η', aka `return')

    return : ∀ {A} → (A ⇒ T₀ unit A)

    -- Subsumption/coercion

    sub : ∀ {u v} → u ≤ v → ∀ {A} → (T₀ u A ⇒ T₀ v A)

    -- The laws of Kleisli triples, modulo grading
    --
    -- Note that the graded laws contain coercions that do not appear
    -- in the laws for ungraded Kleisli triples.  These are necessary
    -- because our grading is a monoidal category (rather than a
    -- partially ordered monoid) and hence grading is considered only
    -- up to coherent isomorphism (not up to equality).  For example,
    -- the objects `T₀ (unit ⊗₀ u) A' and `T₀ u A' are not identical,
    -- only isomorphic.  The same issue arises already when one
    -- specifies monoid laws only up to proof-relevant equivalence (as
    -- is the case in the Agda standard library).

    ext-identityˡ : ∀ {u A} → sub ρ⇒ ∘ ext u return ≈ id {T₀ u A}
    ext-identityʳ : ∀ {u A B} {f : A ⇒ T₀ u B} → sub λ⇒ ∘ ext unit f ∘ return ≈ f
    ext-assoc     : ∀ {u v w A B C} {f : B ⇒ T₀ w C} {g : A ⇒ T₀ v B} →
                    ext u (ext v f ∘ g) ≈ sub α⇒ ∘ (ext (u ⊗₀ v) f ∘ ext u g)
                 
    ext-resp-≈  : ∀ {u v A B} {f g : A ⇒ T₀ v B} → f ≈ g → ext u f ≈ ext u g

    -- A coherence law relating subsumption and Kleisli extension

    sub-commute      : ∀ {u₁ u₂ v₁ v₂ A B}
                       {α : u₁ ≤ v₁} {β : u₂ ≤ v₂} {f : A ⇒ T₀ u₂ B} →
                       ext v₁ (sub β ∘ f) ∘ sub α ≈ sub (α ⊗₁ β) ∘ ext u₁ f

    -- Subsumption induces a functorial structure on T₀ (in the first
    -- argument)

    sub-identity     : ∀ {u A} → sub idV ≈ id {T₀ u A}
    sub-homomorphism : ∀ {u v w A} {α : v ≤ w} {β : u ≤ v} →
                       sub (α ∙ β) ≈ sub α ∘ sub β {A}
    sub-resp-≈       : ∀ {u v A} {α β : u ≤ v} → α ∼ β → sub α ≈ sub β {A}

  open HomReasoning
  open MorphismReasoning C
  open MonoidalCategory V using (unitorʳ-commute-from; triangle)
  open Properties (monoidal V) using (coherence₂; coherence₃)

  private
    variable
      u v w u₁ u₂ v₁ v₂ : Obj V
      A B D : Obj C
      α β : u ≤ v
      f g h : A ⇒ B

  -- Left- and right-biased versions of `sub-commute'

  sub-commute₁ : ext v f ∘ sub α ≈ sub (α ⊗₁ idV) ∘ ext u f
  sub-commute₁ {v = v} {f = f} {u = u} {α = α} = begin
    ext v f ∘ sub α               ≈⟨ ext-resp-≈ (introˡ sub-identity) ⟩∘⟨refl ⟩
    ext v (sub idV ∘ f) ∘ sub α   ≈⟨ sub-commute ⟩
    sub (α ⊗₁ idV) ∘ ext u f      ∎

  sub-commute₂ : ext u (sub α ∘ f) ≈ sub (idV ⊗₁ α) ∘ ext u f
  sub-commute₂ {u = u} {α = α} {f = f} = begin
    ext u (sub α ∘ f)            ≈⟨ introʳ sub-identity ⟩
    ext u (sub α ∘ f) ∘ sub idV  ≈⟨ sub-commute ⟩
    sub (idV ⊗₁ α) ∘ ext u f     ∎

  -- The map (T₀ u) extends to a functor for every u.

  T₁ : ∀ u {A B} → (A ⇒ B) → (T₀ u A ⇒ T₀ u B)
  T₁ u f = sub ρ⇒ ∘ ext u (return ∘ f)

  T-identity : T₁ u id ≈ id {T₀ u A}
  T-identity {u = u} = begin
    sub ρ⇒ ∘ ext u (return ∘ id)  ≈⟨ refl⟩∘⟨ ext-resp-≈ identityʳ ⟩
    sub ρ⇒ ∘ ext u (return)       ≈⟨ ext-identityˡ ⟩
    id                            ∎

  -- A helper lemma
  ext-T-fusion : ext u f ∘ T₁ u g ≈ ext u (f ∘ g)
  ext-T-fusion {u = u} {f = f} {g = g} =
    let u⊗1 = u ⊗₀ unit in begin
      ext u f ∘ sub ρ⇒ ∘ ext u (return ∘ g)
    ≈⟨ extendʳ sub-commute₁ ⟩
      sub (ρ⇒ ⊗₁ idV) ∘ ext u⊗1 f ∘ ext u (return ∘ g)
    ≈˘⟨ sub-resp-≈ triangle ⟩∘⟨refl ⟩
      sub (idV ⊗₁ λ⇒ ∙ α⇒) ∘ ext u⊗1 f ∘ ext u (return ∘ g)
    ≈⟨ pushˡ sub-homomorphism ⟩
      sub (idV ⊗₁ λ⇒) ∘ sub α⇒ ∘ ext u⊗1 f ∘ ext u (return ∘ g)
    ≈˘⟨ refl⟩∘⟨ ext-assoc ⟩
      sub (idV ⊗₁ λ⇒) ∘ ext u (ext unit f ∘ return ∘ g)
    ≈˘⟨ sub-commute₂ ⟩
      ext u (sub λ⇒ ∘ ext unit f ∘ return ∘ g)
    ≈⟨ ext-resp-≈ ((refl⟩∘⟨ sym-assoc) ○ pullˡ ext-identityʳ) ⟩
      ext u (f ∘ g)
    ∎

  T-homomorphism : T₁ u (f ∘ g) ≈ T₁ u f ∘ T₁ u g
  T-homomorphism {u = u} {f = f} {g = g} = begin
    sub ρ⇒ ∘ ext u (return ∘ f ∘ g)         ≈˘⟨ refl⟩∘⟨ ext-resp-≈ assoc ⟩
    sub ρ⇒ ∘ ext u ((return ∘ f) ∘ g)       ≈˘⟨ pullʳ ext-T-fusion ⟩
    (sub ρ⇒ ∘ ext u (return ∘ f)) ∘ T₁ u g  ∎

  T-resp-≈ : f ≈ g → T₁ u f ≈ T₁ u g
  T-resp-≈ f≈g = ∘-resp-≈ʳ (ext-resp-≈ (∘-resp-≈ʳ f≈g))

  -- return is a natural transformation.

  return-commute : return ∘ f ≈ T₁ unit f ∘ return
  return-commute {f = f} = begin
    return ∘ f                                 ≈˘⟨ ext-identityʳ ⟩
    sub λ⇒ ∘ ext unit (return ∘ f) ∘ return    ≈⟨ pullˡ (sub-resp-≈ coherence₃ ⟩∘⟨refl) ⟩
    (sub ρ⇒ ∘ ext unit (return ∘ f)) ∘ return  ∎

  -- The (graded) monadic multiplication (aka `join')

  μ : ∀ u v {A} → (T₀ u (T₀ v A) ⇒ T₀ (u ⊗₀ v) A)
  μ u v = ext u id

  μ-commute : μ u v ∘ T₁ u (T₁ v f) ≈ T₁ (u ⊗₀ v) f ∘ μ u v
  μ-commute {u = u} {v = v} {f = f} =
    begin
      ext u id ∘ T₁ u (T₁ v f)
    ≈⟨ ext-T-fusion ⟩
      ext u (id ∘ T₁ v f)
    ≈⟨ ext-resp-≈ (id-comm-sym ○ assoc) ⟩
      ext u (sub ρ⇒ ∘ ext v (return ∘ f) ∘ id)
    ≈⟨ sub-commute₂ ⟩
      sub (idV ⊗₁ ρ⇒) ∘ ext u (ext v (return ∘ f) ∘ id)
    ≈⟨ refl⟩∘⟨ ext-assoc ⟩
      sub (idV ⊗₁ ρ⇒) ∘ sub α⇒ ∘ ext (u ⊗₀ v) (return ∘ f) ∘ ext u id
    ≈˘⟨ pushˡ sub-homomorphism ⟩
      sub (idV ⊗₁ ρ⇒ ∙ α⇒) ∘ ext (u ⊗₀ v) (return ∘ f) ∘ ext u id
    ≈⟨ pullˡ (sub-resp-≈ coherence₂ ⟩∘⟨refl) ⟩
      (sub ρ⇒ ∘ ext (u ⊗₀ v) (return ∘ f)) ∘ ext u id
    ∎

  -- The "classic" (graded) modad laws.

  μ-identityˡ : sub λ⇒ ∘ μ unit u ∘ return ≈ id {T₀ u A}
  μ-identityˡ = ext-identityʳ

  μ-identityʳ : sub ρ⇒ ∘ μ u unit ∘ T₁ u return ≈ id {T₀ u A}
  μ-identityʳ {u = u} = begin
    sub ρ⇒ ∘ ext u id ∘ T₁ u return  ≈⟨ refl⟩∘⟨ ext-T-fusion ⟩
    sub ρ⇒ ∘ ext u (id ∘ return)     ≈⟨ refl⟩∘⟨ ext-resp-≈ identityˡ ⟩
    sub ρ⇒ ∘ ext u return            ≈⟨ ext-identityˡ ⟩
    id                               ∎

  μ-assoc : sub α⇒ {A} ∘ μ (u ⊗₀ v) w ∘ μ u v ≈ μ u (v ⊗₀ w) ∘ T₁ u (μ v w)
  μ-assoc {u = u} {v = v} {w = w} = begin
    sub α⇒ ∘ ext (u ⊗₀ v) id ∘ ext u id  ≈˘⟨ ext-assoc ⟩
    ext u (ext v id ∘ id)                ≈⟨ ext-resp-≈ id-comm ⟩
    ext u (id ∘ μ v w)                   ≈˘⟨ ext-T-fusion ⟩
    μ u (v ⊗₀ w) ∘ T₁ u (μ v w)          ∎

  -- sub is a natural transformation

  sub-commute′ : sub α ∘ T₁ u f ≈ T₁ v f ∘ sub α
  sub-commute′ {u = u} {v = v} {α = α} {f = f} = begin
    sub α ∘ sub ρ⇒ ∘ ext u (return ∘ f)           ≈˘⟨ pushˡ sub-homomorphism ⟩
    sub (α ∙ ρ⇒) ∘ ext u (return ∘ f)             ≈˘⟨ sub-resp-≈ unitorʳ-commute-from ⟩∘⟨refl ⟩
    sub (ρ⇒ ∙ α ⊗₁ idV) ∘ ext u (return ∘ f)      ≈⟨ pushˡ sub-homomorphism ⟩
    sub ρ⇒ ∘ sub (α ⊗₁ idV) ∘ ext u (return ∘ f)  ≈˘⟨ pullʳ sub-commute₁ ⟩
    (sub ρ⇒ ∘ ext v (return ∘ f)) ∘ sub α         ∎

  -- A coherence law for μ and sub

  μ-sub-commute : μ v₁ v₂ ∘ T₁ v₁ (sub β) ∘ sub α ≈ sub (α ⊗₁ β) ∘ μ u₁ u₂ {A}
  μ-sub-commute {v₁ = v₁} {v₂ = v₂} {u₂ = u₂} {β = β} {u₁ = u₁} {α = α} = begin
    μ v₁ v₂ ∘ T₁ v₁ (sub β) ∘ sub α  ≈⟨ pullˡ ext-T-fusion ⟩
    ext v₁ (id ∘ sub β) ∘ sub α      ≈⟨ ext-resp-≈ id-comm-sym ⟩∘⟨refl ⟩
    ext v₁ (sub β ∘ id) ∘ sub α      ≈⟨ sub-commute ⟩
    sub (α ⊗₁ β) ∘ μ u₁ u₂           ∎

  -- Kleisli composition

  infixr 9 _⊙_

  _⊙_ : ∀ {u v A B C} → B ⇒ T₀ v C → A ⇒ T₀ u B → A ⇒ T₀ (u ⊗₀ v) C
  f ⊙ g = ext _ f ∘ g

  ⊙-identityˡ : sub ρ⇒ ∘ return ⊙ f ≈ f
  ⊙-identityˡ {f = f} = cancelˡ ext-identityˡ

  ⊙-identityʳ : sub λ⇒ ∘ f ⊙ return ≈ f
  ⊙-identityʳ = ext-identityʳ

  ⊙-assoc : (f ⊙ g) ⊙ h ≈ sub α⇒ ∘ f ⊙ (g ⊙ h)
  ⊙-assoc {f = f} {g = g} {h = h} = begin
    ext _ (f ⊙ g) ∘ h           ≈⟨ pushˡ ext-assoc ⟩
    sub α⇒ ∘ (f ⊙ ext _ g) ∘ h  ≈⟨ refl⟩∘⟨ assoc ⟩ 
    sub α⇒ ∘ f ⊙ (g ⊙ h)        ∎

module _ {V : MonoidalCategory o ℓ e} {C : Category o′ ℓ′ e′} where
  open Category C
  open MonoidalCategory V using (⊗; _⊗₀_; _⊗₁_; unit)
    renaming (_⇒_ to _≤_; id to idV; _∘_ to _∙_; _≈_ to _∼_)
  open Utilities.Shorthands (monoidal V)
  open HomReasoning
  open MorphismReasoning C

  private
    variable
      u v w u₁ u₂ v₁ v₂ : Obj V
      A B D : Obj C
      α β : u ≤ v
      f g : A ⇒ B

  GradedMonad⇒GradedKleisliTriple : GradedMonad V C → GradedKleisliTriple V C
  GradedMonad⇒GradedKleisliTriple M = record
    { T₀               = T₀
    ; ext              = ext
    ; return           = return
    ; sub              = sub
    ; ext-identityˡ    = ext-identityˡ
    ; ext-identityʳ    = ext-identityʳ
    ; ext-assoc        = ext-assoc
    ; ext-resp-≈       = ext-resp-≈
    ; sub-commute      = sub-commute
    ; sub-identity     = M.identity
    ; sub-homomorphism = M.homomorphism
    ; sub-resp-≈       = λ α∼β → M.F-resp-≈ α∼β
    }
    where
      module M = MonoidalFunctor M

      μ = λ u v {A} → η (M.⊗-homo.η (u , v)) A

      T₀ : Obj V → Obj C → Obj C
      T₀ u A = M.₀ u $₀ A

      T₁ : ∀ u {A B} → (A ⇒ B) → (T₀ u A ⇒ T₀ u B)
      T₁ u f = M.₀ u $₁ f

      ext : ∀ u {v A B} → (A ⇒ T₀ v B) → (T₀ u A ⇒ T₀ (u ⊗₀ v) B)
      ext u {v} f = μ u v ∘ T₁ u f

      return : A ⇒ T₀ unit A
      return {A} = η M.ε A
      
      sub : u ≤ v → ∀ {A} → (T₀ u A ⇒ T₀ v A)
      sub α = η (M.₁ α) _

      ext-identityˡ : sub ρ⇒ ∘ ext u return ≈ id {T₀ u A}
      ext-identityˡ {u = u} {A = A} = begin
        sub ρ⇒ ∘ ext u return                 ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ identityʳ ⟩
        sub ρ⇒ ∘ μ u unit ∘ T₁ u return ∘ id  ≈⟨ M.unitaryʳ ⟩
        id                                    ∎

      ext-identityʳ : sub λ⇒ ∘ ext unit {u} f ∘ return ≈ f
      ext-identityʳ {u = u} {f = f} = begin
          sub λ⇒ ∘ (μ unit u ∘ T₁ unit f) ∘ return
        ≈˘⟨ refl⟩∘⟨ pushʳ (commute M.ε f) ⟩
          sub λ⇒ ∘ μ unit u ∘ return ∘ f
        ≈⟨ assoc²εβ ⟩
          (sub λ⇒ ∘ μ unit u ∘ return) ∘ f
        ≈⟨ (refl⟩∘⟨ refl⟩∘⟨ introˡ (identity (M.₀ unit))) ⟩∘⟨refl ⟩
          (sub λ⇒ ∘ μ unit u ∘ T₁ unit id ∘ return) ∘ f
        ≈⟨ elimˡ M.unitaryˡ ⟩
          f
        ∎

      ext-assoc : ext u (ext v {w} f ∘ g) ≈ sub α⇒ ∘ (ext (u ⊗₀ v) f ∘ ext u g)
      ext-assoc {u = u} {v = v} {w = w} {f = f} {g = g} =
        let u⊗v = u ⊗₀ v
            v⊗w = v ⊗₀ w
        in begin
          μ u v⊗w ∘ T₁ u ((μ v w ∘ T₁ v f) ∘ g)
        ≈⟨ refl⟩∘⟨ F-resp-≈ (M.₀ u) assoc ⟩
          μ u v⊗w ∘ T₁ u (μ v w ∘ T₁ v f ∘ g)
        ≈⟨ refl⟩∘⟨ homomorphism (M.₀ u) ⟩
          μ u v⊗w ∘ T₁ u (μ v w) ∘ T₁ u ((T₁ v f) ∘ g)
        ≈˘⟨ refl⟩∘⟨ identityʳ ⟩∘⟨refl ⟩
          μ u v⊗w ∘ (T₁ u (μ v w) ∘ id) ∘ T₁ u ((T₁ v f) ∘ g)
        ≈˘⟨ pushˡ (refl⟩∘⟨ identityʳ ⟩∘⟨refl) ⟩
          (μ u v⊗w ∘ (T₁ u (μ v w) ∘ id) ∘ id) ∘ T₁ u ((T₁ v f) ∘ g)
        ≈˘⟨ M.associativity ⟩∘⟨refl ⟩
          (sub α⇒ ∘ μ u⊗v w ∘ T₁ u⊗v id ∘ μ u v) ∘ T₁ u ((T₁ v f) ∘ g)
        ≈⟨ pullʳ ((refl⟩∘⟨ elimˡ (identity (M.₀ u⊗v))) ⟩∘⟨ homomorphism (M.₀ u)) ⟩
          sub α⇒ ∘ (μ u⊗v w ∘ μ u v) ∘ T₁ u (T₁ v f) ∘ T₁ u g
        ≈⟨ refl⟩∘⟨ extend² (commute (M.⊗-homo.η (u , v)) f) ⟩
          sub α⇒ ∘ (μ u⊗v w ∘ T₁ u⊗v f) ∘ μ u v ∘ T₁ u g
        ∎

      ext-resp-≈ : f ≈ g → ext u f ≈ ext u g
      ext-resp-≈ f≈g = ∘-resp-≈ʳ (F-resp-≈ (M.₀ _) f≈g)

      sub-commute : ext v₁ {v₂} (sub β ∘ f) ∘ sub α
                      ≈ sub (α ⊗₁ β) ∘ ext u₁ {u₂} f
      sub-commute {v₁ = v₁} {v₂ = v₂} {u₂ = u₂} {β = β} {f = f} {u₁ = u₁}
                  {α = α} = begin
          (μ v₁ v₂ ∘ T₁ v₁ (sub β ∘ f)) ∘ sub α
        ≈⟨ pullʳ (homomorphism (M.₀ v₁) ⟩∘⟨refl) ⟩
          μ v₁ v₂ ∘ (T₁ v₁ (sub β) ∘ T₁ v₁ f) ∘ sub α
        ≈˘⟨ refl⟩∘⟨ extendˡ (commute (M.₁ α) f) ⟩
          μ v₁ v₂ ∘ (T₁ v₁ (sub β) ∘ sub α) ∘ T₁ u₁ f
        ≈⟨ extendʳ (M.⊗-homo.commute (α , β)) ⟩
          sub (α ⊗₁ β) ∘ μ u₁ u₂ ∘ T₁ u₁ f
        ∎

  GradedKleisliTriple⇒GradedMonad : GradedKleisliTriple V C → GradedMonad V C
  GradedKleisliTriple⇒GradedMonad T = record
    { F               = F
    ; isMonoidal      = record
      { ε             = ntHelper (record
        { η           = λ _ → return 
        ; commute     = λ _ → return-commute
        })
      ; ⊗-homo        = ntHelper (record
        { η           = λ{ (u , v) → ntHelper (record
          { η         = λ _ → μ u v
          ; commute   = λ _ → μ-commute
          }) }
        ; commute     = λ _ → μ-sub-commute
        })
      ; associativity = associativity
      ; unitaryˡ      = unitaryˡ
      ; unitaryʳ      = unitaryʳ
      }
    }
    where
      open GradedKleisliTriple T

      F₀ : Obj V → Functor C C
      F₀ u = record
        { F₀           = T₀ u
        ; F₁           = T₁ u
        ; identity     = T-identity
        ; homomorphism = T-homomorphism
        ; F-resp-≈     = T-resp-≈
        }

      F₁ : ∀ {A B} → A ≤ B → NaturalTransformation (F₀ A) (F₀ B)
      F₁ α = ntHelper (record
        { η       = λ _ → sub α
        ; commute = λ _ → sub-commute′
        })

      F : Functor (U V) (Functors C C)
      F = record
        { F₀           = F₀
        ; F₁           = F₁
        ; identity     = sub-identity
        ; homomorphism = sub-homomorphism
        ; F-resp-≈     = λ α∼β → sub-resp-≈ α∼β
        }

      unitaryˡ : sub λ⇒ ∘ μ unit u ∘ T₁ unit id ∘ return ≈ id {T₀ u A}
      unitaryˡ {u = u} = begin
        sub λ⇒ ∘ μ unit u ∘ T₁ unit id ∘ return  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ elimˡ T-identity ⟩
        sub λ⇒ ∘ μ unit u ∘ return               ≈⟨ ext-identityʳ ⟩
        id                                       ∎

      unitaryʳ : sub ρ⇒ ∘ μ u unit ∘ T₁ u return ∘ id ≈ id {T₀ u A}
      unitaryʳ {u = u} = begin
        sub ρ⇒ ∘ μ u unit ∘ T₁ u return ∘ id     ≈⟨ assoc²εβ ⟩
        (sub ρ⇒ ∘ μ u unit ∘ T₁ u return) ∘ id   ≈⟨ elimˡ μ-identityʳ ⟩
        id                                       ∎

      associativity : sub α⇒ {A} ∘ μ (u ⊗₀ v) w ∘ T₁ (u ⊗₀ v) id ∘ μ u v
                        ≈ μ u (v ⊗₀ w) ∘ (T₁ u (μ v w) ∘ id) ∘ id
      associativity {u = u} {v = v} {w = w} = begin
          sub α⇒ ∘ μ (u ⊗₀ v) w ∘ T₁ (u ⊗₀ v) id ∘ μ u v
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ elimˡ T-identity ⟩
          sub α⇒ ∘ μ (u ⊗₀ v) w ∘ μ u v
        ≈⟨ μ-assoc ⟩
          μ u (v ⊗₀ w) ∘ T₁ u (μ v w)
        ≈˘⟨ refl⟩∘⟨ identityʳ ⟩
          μ u (v ⊗₀ w) ∘ T₁ u (μ v w) ∘ id
        ≈˘⟨ refl⟩∘⟨ identityʳ ⟩
          μ u (v ⊗₀ w) ∘ (T₁ u (μ v w) ∘ id) ∘ id
        ∎

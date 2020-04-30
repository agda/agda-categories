{-# OPTIONS --without-K --safe #-}

module Categories.Category.Equivalence where

-- Strong equivalence of categories.  Same as ordinary equivalence in Cat.
-- May not include everything we'd like to think of as equivalences, namely
-- the full, faithful functors that are essentially surjective on objects.

open import Level
open import Relation.Binary using (IsEquivalence; Setoid)

open import Categories.Category.Core using (Category)
open import Categories.Functor renaming (id to idF)
open import Categories.NaturalTransformation.NaturalIsomorphism as ≃
  using (NaturalIsomorphism ; unitorˡ; unitorʳ; associator; _ⓘᵥ_; _ⓘˡ_; _ⓘʳ_)

private
  variable
    o ℓ e : Level
    C D E : Category o ℓ e

record WeakInverse (F : Functor C D) (G : Functor D C) : Set (levelOfTerm F ⊔ levelOfTerm G) where
  field
    F∘G≈id : NaturalIsomorphism (F ∘F G) idF
    G∘F≈id : NaturalIsomorphism (G ∘F F) idF

  module F∘G≈id = NaturalIsomorphism F∘G≈id
  module G∘F≈id = NaturalIsomorphism G∘F≈id

record StrongEquivalence {o ℓ e o′ ℓ′ e′} (C : Category o ℓ e) (D : Category o′ ℓ′ e′) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  field
    F            : Functor C D
    G            : Functor D C
    weak-inverse : WeakInverse F G

  open WeakInverse weak-inverse public

refl : StrongEquivalence C C
refl = record
  { F            = idF
  ; G            = idF
  ; weak-inverse = record
    { F∘G≈id = unitorˡ
    ; G∘F≈id = unitorˡ
    }
  }

sym : StrongEquivalence C D → StrongEquivalence D C
sym e = record
  { F            = G
  ; G            = F
  ; weak-inverse = record
    { F∘G≈id     = G∘F≈id
    ; G∘F≈id     = F∘G≈id
    }
  }
  where open StrongEquivalence e

trans : StrongEquivalence C D → StrongEquivalence D E → StrongEquivalence C E
trans {C = C} {D = D} {E = E} e e′ = record
  { F            = e′.F ∘F e.F
  ; G            = e.G ∘F e′.G
  ; weak-inverse = record
    { F∘G≈id = let module S = Setoid (≃.Functor-NI-setoid E E)
               in S.trans (S.trans (associator (e.G ∘F e′.G) e.F e′.F)
                                   (e′.F ⓘˡ (unitorˡ ⓘᵥ (e.F∘G≈id ⓘʳ e′.G) ⓘᵥ ≃.sym (associator e′.G e.G e.F))))
                          e′.F∘G≈id
    ; G∘F≈id = let module S = Setoid (≃.Functor-NI-setoid C C)
               in S.trans (S.trans (associator (e′.F ∘F e.F) e′.G e.G)
                                   (e.G ⓘˡ (unitorˡ ⓘᵥ (e′.G∘F≈id ⓘʳ e.F) ⓘᵥ ≃.sym (associator e.F e′.F e′.G))))
                          e.G∘F≈id
    }
  }
  where module e  = StrongEquivalence e
        module e′ = StrongEquivalence e′

isEquivalence : ∀ {o ℓ e} → IsEquivalence (StrongEquivalence {o} {ℓ} {e})
isEquivalence = record
  { refl  = refl
  ; sym   = sym
  ; trans = trans
  }

setoid : ∀ o ℓ e → Setoid _ _
setoid o ℓ e = record
  { Carrier       = Category o ℓ e
  ; _≈_           = StrongEquivalence
  ; isEquivalence = isEquivalence
  }

{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Functor.Core where

open import Level
open import Function renaming (id to idfun) using ()
open import Relation.Binary hiding (_⇒_)

import Relation.Binary.Reasoning.Setoid as SetoidR

import Categories.Morphism as M
import Categories.Square as Square

private
  variable
    o ℓ e o′ ℓ′ e′ o′′ ℓ′′ e′′ : Level
    C D : Category o ℓ e

record Functor (C : Category o ℓ e) (D : Category o′ ℓ′ e′) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  private module C = Category C
  private module D = Category D


  field
    F₀ : C.Obj → D.Obj
    F₁ : ∀ {A B} → C [ A , B ] → D [ F₀ A , F₀ B ]

    identity     : ∀ {A} → D [ F₁ (C.id {A}) ≈ D.id ]
    homomorphism : ∀ {X Y Z} {f : C [ X , Y ]} {g : C [ Y , Z ]} →
                     D [ F₁ (C [ g ∘ f ]) ≈ D [ F₁ g ∘ F₁ f ] ]
    F-resp-≈     : ∀ {A B} {f g : C [ A , B ]} → C [ f ≈ g ] → D [ F₁ f ≈ F₁ g ]

  op : Functor C.op D.op
  op = record
    { F₀           = F₀
    ; F₁           = F₁
    ; identity     = identity
    ; homomorphism = homomorphism
    ; F-resp-≈     = F-resp-≈
    }

Endofunctor : Category o ℓ e → Set _
Endofunctor C = Functor C C

Contravariant : ∀ (C : Category o ℓ e) (D : Category o′ ℓ′ e′) → Set _
Contravariant C D = Functor C.op D
  where module C = Category C

id : ∀ {C : Category o ℓ e} → Endofunctor C
id {C = C} = record
  { F₀           = idfun
  ; F₁           = idfun
  ; identity     = refl
  ; homomorphism = refl
  ; F-resp-≈     = idfun
  }
  where open Category.Equiv C

infixr 9 _∘F_

_∘F_ : ∀ {C : Category o ℓ e} {D : Category o′ ℓ′ e′} {E : Category o′′ ℓ′′ e′′}
    → Functor D E → Functor C D → Functor C E
_∘F_ {C = C} {D = D} {E = E} F G = record
  { F₀ = λ x → F₀ (G₀ x)
  ; F₁ = λ f → F₁ (G₁ f)
  ; identity = identity′
  ; homomorphism = homomorphism′
  ; F-resp-≈ = ∘-resp-≈′
  }
  where
  module C = Category C
  module D = Category D
  module E = Category E
  module F = Functor F
  module G = Functor G
  open F
  open G renaming (F₀ to G₀; F₁ to G₁; F-resp-≈ to G-resp-≈)

  identity′ : ∀ {A} → E [ F₁ (G₁ (C.id {A})) ≈ E.id ]
  identity′ = begin
    F₁ (G₁ C.id) ≈⟨ F-resp-≈ G.identity ⟩
    F₁ D.id      ≈⟨ F.identity ⟩
    E.id         ∎
    where open SetoidR E.hom-setoid

  homomorphism′ : ∀ {X Y Z} {f : C [ X , Y ]} {g : C [ Y , Z ]}
                 → E [ F₁ (G₁ (C [ g ∘ f ])) ≈ E [ F₁ (G₁ g) ∘ F₁ (G₁ f) ] ]
  homomorphism′ {f = f} {g = g} = begin
    F₁ (G₁ (C [ g ∘ f ]))       ≈⟨ F-resp-≈ G.homomorphism ⟩
    F₁ (D [ G₁ g ∘ G₁ f ])      ≈⟨ F.homomorphism ⟩
    E [ F₁ (G₁ g) ∘ F₁ (G₁ f) ] ∎
    where open SetoidR E.hom-setoid

  ∘-resp-≈′ : ∀ {A B} {F G : C [ A , B ]}
            → C [ F ≈ G ] → E [ F₁ (G₁ F) ≈ F₁ (G₁ G) ]
  ∘-resp-≈′ = λ x → F-resp-≈ (G-resp-≈ x)

-- equivalence of Functor is weaker than it is intuitively defined.
-- to replace obj≅ with _≡_, I suppose K is needed.
infix 4 _≋_
record _≋_ {C : Category o ℓ e} {D : Category o′ ℓ′ e′} (F G : Functor C D) : Set (o ⊔ o′ ⊔ ℓ ⊔ ℓ′ ⊔ e′) where
  private
    module F = Functor F
    module G = Functor G
    module C = Category C
    module D = Category D
  open Category D
  open M D
  open _≅_

  field
    obj≅  : ∀ {A} → F.F₀ A ≅ G.F₀ A
    conj≈ : ∀ {A B} {f : A C.⇒ B} → from obj≅ ∘ F.F₁ f ∘ to obj≅ ≈ G.F₁ f

module _ where
  open Functor

  ≋-refl : Reflexive (_≋_ {C = C} {D = D})
  ≋-refl {D = D} = record
    { obj≅  = ≅.refl
    ; conj≈ = trans identityˡ identityʳ
    }
    where open M D
          open Category D
          open HomReasoning

  ≋-sym : Symmetric (_≋_ {C = C} {D = D})
  ≋-sym {D = D} {i = F} {j = G} eq = record
    { obj≅  = ≅.sym obj≅
    ; conj≈ = λ {_ _ f} → begin
      to obj≅ ∘ F₁ G f ∘ from obj≅ ≈˘⟨ refl ⟩∘⟨ trans assoc conj≈ ⟩∘⟨ refl ⟩
      to obj≅ ∘ ((from obj≅ ∘ F₁ F f) ∘ to obj≅) ∘ from obj≅ ≈⟨ refl ⟩∘⟨ cancelʳ (isoˡ obj≅) ⟩
      to obj≅ ∘ (from obj≅ ∘ F₁ F f) ≈⟨ cancelˡ (isoˡ obj≅) ⟩
      F₁ F f ∎
    }
    where open _≋_ eq
          open M D
          open Category D
          open Square D
          open HomReasoning
          open _≅_

  ≋-trans : Transitive (_≋_ {C = C} {D = D})
  ≋-trans {D = D} {i = F} {j = G} {k = H} eq eq′ = record
    { obj≅  = E.trans (obj≅ eq) (obj≅ eq′)
    ; conj≈ = λ {_ _ f} → begin
      (from (obj≅ eq′) ∘ from (obj≅ eq)) ∘
        F₁ F f ∘ to (obj≅ eq) ∘ to (obj≅ eq′)   ≈⟨ assoc ⟩
      from (obj≅ eq′) ∘ from (obj≅ eq) ∘
        F₁ F f ∘ to (obj≅ eq) ∘ to (obj≅ eq′)   ≈˘⟨ refl ⟩∘⟨ refl ⟩∘⟨ assoc ⟩
      from (obj≅ eq′) ∘ from (obj≅ eq) ∘
        (F₁ F f ∘ to (obj≅ eq)) ∘ to (obj≅ eq′) ≈⟨ refl ⟩∘⟨ pullˡ (conj≈ eq) ⟩
      from (obj≅ eq′) ∘ F₁ G f ∘ to (obj≅ eq′)  ≈⟨ conj≈ eq′ ⟩
      F₁ H f                                    ∎
    }
    where open _≋_
          open M D
          open Category D
          open Square D
          open HomReasoning
          open _≅_
          module E = IsEquivalence (M.≅-isEquivalence D)


  ≋-isEquivalence : IsEquivalence (_≋_ {C = C} {D = D})
  ≋-isEquivalence = record
    { refl  = ≋-refl
    ; sym   = ≋-sym
    ; trans = ≋-trans
    }

  ≋-setoid : (C : Category o ℓ e) (D : Category o′ ℓ′ e′) → Setoid _ _
  ≋-setoid C D = record
    { Carrier       = _
    ; _≈_           = _≋_ {C = C} {D = D}
    ; isEquivalence = ≋-isEquivalence
    }

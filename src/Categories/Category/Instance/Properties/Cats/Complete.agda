{-# OPTIONS --safe --without-K #-}

module Categories.Category.Instance.Properties.Cats.Complete where

open import Categories.Category
open import Categories.Category.Complete
open import Categories.Category.Instance.Cats
open import Categories.Diagram.Cone
open import Categories.Functor
open import Categories.Morphism
open import Categories.Morphism.Reasoning
open import Categories.NaturalTransformation.NaturalIsomorphism

open import Data.Product
open import Level

private module _ {o ℓ e} {J : Category o ℓ e} (F : Functor J (Cats (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) (o ⊔ e))) where
  open Functor F
  module FJ j = Category (F₀ j)

  -- The objects of the limit of F.
  record NObj : Set (o ⊔ ℓ ⊔ e) where
    field
      -- For each object j of J, we have an object of F j.
      ψ : ∀ j → FJ.Obj j
      -- For each morphism f : j ⇒ k in J, we have the isomorphism (in F k):
      --   F f (ψ j) ≅ ψ k.
      commute : ∀ {j k} (f : J [ j , k ]) → _≅_ (F₀ k) (Functor.F₀ (F₁ f) (ψ j)) (ψ k)
    module commute {j k} (f : J [ j , k ]) = _≅_ (commute f)

  -- The morphisms of the limit of F.
  record N⇒ (A B : NObj) : Set (o ⊔ ℓ ⊔ e) where
    module A = NObj A
    module B = NObj B
    field
      -- For each object j in J, we have a morphism in F j from A.ψ j to B.ψ j.
      arr : ∀ j → F₀ j [ A.ψ j , B.ψ j ]
      -- For each morphism f : j ⇒ k in J, we have the equality in F k:
      --   B.commute f ∘ F f (arr j) ≈ arr k ∘ A.commute f.
      commute : ∀ {j k} (f : J [ j , k ]) → F₀ k [ F₀ k [ B.commute.from f ∘ Functor.F₁ (F₁ f) (arr j) ] ≈ F₀ k [ arr k ∘ A.commute.from f ] ]

  -- The actual category that is the limit of F.
  N : Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) (o ⊔ e)
  N = record
    { Obj = NObj
    ; _⇒_ = N⇒
    ; _≈_ = λ f g → ∀ j → F₀ j [ N⇒.arr f j ≈ N⇒.arr g j ]
    ; id = λ {A} → let module A = NObj A in record
      { arr = λ j → FJ.id j
      ; commute = λ {j} {k} g → let open FJ.HomReasoning k in begin
        F₀ k [ A.commute.from g ∘ Functor.F₁ (F₁ g) (FJ.id j) ] ≈⟨ refl⟩∘⟨ Functor.identity (F₁ g) ⟩
        F₀ k [ A.commute.from g ∘ FJ.id k ]                     ≈⟨ id-comm (F₀ k) ⟩
        F₀ k [ FJ.id k ∘ A.commute.from g ]                     ∎
      }
    ; _∘_ = λ {A} {B} {C} f g →
      let
        module A = NObj A
        module B = NObj B
        module C = NObj C
      in record
        { arr = λ j → F₀ j [ N⇒.arr f j ∘ N⇒.arr g j ]
        ; commute = λ {j} {k} h → let open FJ.HomReasoning k in begin
          F₀ k [ C.commute.from h ∘ Functor.F₁ (F₁ h) (F₀ j [ N⇒.arr f j ∘ N⇒.arr g j ]) ]                     ≈⟨ pushʳ (F₀ k) (Functor.homomorphism (F₁ h)) ⟩
          F₀ k [ F₀ k [ C.commute.from h ∘ Functor.F₁ (F₁ h) (N⇒.arr f j) ] ∘ Functor.F₁ (F₁ h) (N⇒.arr g j) ] ≈⟨ pushˡ (F₀ k) (N⇒.commute f h) ⟩
          F₀ k [ N⇒.arr f k ∘ F₀ k [ B.commute.from h ∘ Functor.F₁ (F₁ h) (N⇒.arr g j) ] ]                     ≈⟨ pushʳ (F₀ k) (N⇒.commute g h) ⟩
          F₀ k [ F₀ k [ N⇒.arr f k ∘ N⇒.arr g k ] ∘ A.commute.from h ]                                         ∎
        }
    ; assoc = λ j → FJ.assoc j
    ; sym-assoc = λ j → FJ.sym-assoc j
    ; identityˡ = λ j → FJ.identityˡ j
    ; identityʳ = λ j → FJ.identityʳ j
    ; identity² = λ j → FJ.identity² j
    ; equiv = record
      { refl = λ j → FJ.Equiv.refl j
      ; sym = λ f≈g j → FJ.Equiv.sym j (f≈g j)
      ; trans = λ f≈g g≈h j → FJ.Equiv.trans j (f≈g j) (g≈h j)
      }
    ; ∘-resp-≈ = λ f≈h g≈i j → FJ.∘-resp-≈ j (f≈h j) (g≈i j)
    }

  -- For any j in J, we have a functor from the limit of F to F j.
  ψ : ∀ j → Functor N (F₀ j)
  ψ j = record
      { F₀ = λ A → NObj.ψ A j
    ; F₁ = λ f → N⇒.arr f j
    ; identity = FJ.Equiv.refl j
    ; homomorphism = FJ.Equiv.refl j
    ; F-resp-≈ = λ f≈g → f≈g j
    }

  -- This functor plays nice with F
  ψ-commute : ∀ {j k} (f : J [ j , k ]) → F₁ f ∘F ψ j ≃ ψ k
  ψ-commute {j} {k} f = niHelper record
    { η = λ n → NObj.commute.from n f
    ; η⁻¹ = λ n → NObj.commute.to n f
    ; commute = λ g → N⇒.commute g f
    ; iso = λ n → NObj.commute.iso n f
    }

  -- Thus N forms the point of a Cone F
  ⊤ : Cone F
  ⊤ = record
    { apex = record
      { ψ = ψ
      ; commute = ψ-commute
      }
    }

  -- For any Cone F we have a functor from its point to N
  arr : ∀ (C : Cone F) → Functor (Cone.N C) N
  arr C = record
    { F₀ = λ n → record
      { ψ = λ j → Functor.₀ (Cone.ψ C j) n
      ; commute = λ f → record
        { from = NaturalIsomorphism.⇒.η (Cone.commute C f) n
        ; to = NaturalIsomorphism.⇐.η (Cone.commute C f) n
        ; iso = record
          { isoˡ = NaturalIsomorphism.iso.isoˡ (Cone.commute C f) n
          ; isoʳ = NaturalIsomorphism.iso.isoʳ (Cone.commute C f) n
          }
        }
      }
    ; F₁ = λ f → record
      { arr = λ j → Functor.₁ (Cone.ψ C j) f
      ; commute = λ g → NaturalIsomorphism.⇒.commute (Cone.commute C g) f
      }
    ; identity = λ j → Functor.identity (Cone.ψ C j)
    ; homomorphism = λ j → Functor.homomorphism (Cone.ψ C j)
    ; F-resp-≈ = λ f≈g j → Functor.F-resp-≈ (Cone.ψ C j) f≈g
    }

  -- This functor plays nice with the Cone's ψ
  !-commute : ∀ (C : Cone F) {j : Category.Obj J} → NaturalIsomorphism (ψ j ∘F arr C) (Cone.ψ C j)
  !-commute C {j} = niHelper record
    { η = λ n → FJ.id j
    ; η⁻¹ = λ n → FJ.id j
    ; commute = λ f → id-comm-sym (F₀ j)
    ; iso = λ n → record
      { isoˡ = FJ.identity² j
      ; isoʳ = FJ.identity² j
      }
    }

  -- Thus there is a morphism in Cones F from C to ⊤ for any C
  ! : {C : Cone F} → Cone⇒ F C ⊤
  ! {C} = record
    { arr = arr C
    ; commute = !-commute C
    }

  -- This morphism is unique
  -- TODO: this definition is mostly rearranging Cone⇒.commute. It should probably expand it out to use all of Cone⇒.commute
  !-unique : ∀ {C : Cone F} (f : Cone⇒ F C ⊤) → arr C ≃ Cone⇒.arr f
  !-unique {C} f = niHelper record
    { η = λ n → record
      { arr = λ j → NaturalIsomorphism.⇐.η (Cone⇒.commute f) n
      ; commute = λ {j} {k} g → let open FJ.HomReasoning k in begin
        F₀ k [ NObj.commute.from (Functor.₀ (Cone⇒.arr f) n) g ∘ Functor.₁ (F₁ g) (NaturalIsomorphism.⇐.η (Cone⇒.commute f) n) ] ≈⟨ {!!} ⟩
        F₀ k [ NaturalIsomorphism.⇐.η (Cone⇒.commute f) n ∘ NaturalIsomorphism.⇒.η (Cone.commute C g) n ] ∎
      }
    ; η⁻¹ = λ n → record
      { arr = λ j → NaturalIsomorphism.⇒.η (Cone⇒.commute f) n
      ; commute = λ {j} {k} g → {!!}
      }
    ; commute = λ g j → NaturalIsomorphism.⇐.commute (Cone⇒.commute f) g
    ; iso = λ n → record
      { isoˡ = λ j → NaturalIsomorphism.iso.isoʳ (Cone⇒.commute f) n
      ; isoʳ = λ j → NaturalIsomorphism.iso.isoˡ (Cone⇒.commute f) n
      }
    }

-- Therefore Cats is complete!
Cats-Complete : ∀ o ℓ e → Complete o ℓ e (Cats (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) (o ⊔ e))
Cats-Complete o ℓ e {j} F = record
  { terminal = record
    { ⊤ = ⊤ F
    ; ⊤-is-terminal = record
      { ! = ! F
      ; !-unique = !-unique F
      }
    }
  }

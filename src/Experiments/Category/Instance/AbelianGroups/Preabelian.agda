{-# OPTIONS --without-K --safe #-}
module Experiments.Category.Instance.AbelianGroups.Preabelian where

open import Level
open import Function using (_$_)

open import Data.Unit.Polymorphic
open import Data.Product using (Σ-syntax; _,_; _×_; proj₁; proj₂)

import Algebra.Construct.DirectProduct as DirectProduct
open import Algebra.Properties.AbelianGroup

import Relation.Binary.Reasoning.Setoid as SR

open import Categories.Category.Core
open import Categories.Object.Zero
open import Categories.Object.Kernel
open import Categories.Object.Cokernel

open import Categories.Morphism.Notation
import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR

open import Categories.Category.Preadditive
open import Categories.Category.Additive
open import Experiments.Category.PreAbelian

open import Experiments.Category.Instance.AbelianGroups
open import Experiments.Category.Instance.AbelianGroups.Preadditive
open import Experiments.Category.Instance.AbelianGroups.Additive

private
  variable
    c ℓ : Level

open AbelianGroup
open AbelianGroupHomomorphism


kernels : ∀ {A B : AbelianGroup (c ⊔ ℓ) ℓ} (f : AbelianGroupHomomorphism A B) → Kernel 𝟎 f
kernels {A = A} {B = B} f = record
  { kernel = subgroup A P ∙-closed ε-closed ⁻¹-closed
 ; kernel⇒ = record
    { ⟦_⟧ = proj₁
    ; cong = λ eq → eq
    ; homo = λ _ _ → A.refl
    }
  ; isKernel = record
    { commute = proj₂
    ; universal = λ {X} {h} eq → record
      { ⟦_⟧ = λ x → (⟦ h ⟧ x) , (eq x)
      ; cong = cong h
      ; homo = homo h
      }
    ; factors = λ _ → A.refl
    ; unique = λ eq x → A.sym (eq x)
    }
  }
  where
    module A = AbelianGroup A
    module B = AbelianGroup B

    open SR B.setoid

    P : A.Carrier → Set _
    P x = ⟦ f ⟧ x B.≈ B.ε

    ∙-closed : ∀ x y → P x → P y → P (x A.∙ y)
    ∙-closed x y px py = begin
      ⟦ f ⟧ (x A.∙ y)     ≈⟨ homo f x y ⟩
      ⟦ f ⟧ x B.∙ ⟦ f ⟧ y ≈⟨ B.∙-cong px py ⟩
      B.ε B.∙ B.ε         ≈⟨ B.identityˡ B.ε ⟩
      B.ε ∎

    ε-closed : P A.ε
    ε-closed = ε-homo f

    ⁻¹-closed : ∀ x → P x → P (x A.⁻¹)
    ⁻¹-closed x px = begin
      ⟦ f ⟧ (x A.⁻¹) ≈⟨ ⁻¹-homo f x ⟩
      ⟦ f ⟧ x B.⁻¹   ≈⟨ B.⁻¹-cong px  ⟩
      B.ε B.⁻¹       ≈⟨ ε⁻¹≈ε B ⟩
      B.ε ∎


cokernels : ∀ {A B : AbelianGroup c (c ⊔ ℓ)} (f : AbelianGroupHomomorphism A B) → Cokernel 𝟎 f
cokernels {A = A} {B = B} f = record
  { cokernel = abGroupHelper record
    { Carrier = B.Carrier
    ; _≈_ = λ b₁ b₂ → Σ[ a ∈ A.Carrier ] (b₁ B.∙ ⟦ f ⟧ a B.≈ b₂)
    ; _∙_ = B._∙_
    ; ε = B.ε
    ; _⁻¹ = B._⁻¹ 
    ; isEquivalence = record
      { refl = A.ε , quot-refl
      ; sym = λ { {b₁} {b₂} (a , eq) → (a A.⁻¹) , quot-sym eq }
      ; trans = λ { {b₁} {b₂} {b₃} (a₁ , eq₁) (a₂ , eq₂) → (a₁ A.∙ a₂) , quot-trans eq₁ eq₂ }
      }
    ; ∙-cong = λ { (a₁ , eq₁) (a₂ , eq₂) → (a₁ A.∙ a₂) , quot-∙-cong eq₁ eq₂ }
    ; ⁻¹-cong = λ { (a , eq) → (a A.⁻¹) , quot-inv-cong eq }
    ; assoc = λ x y z → A.ε , lift-quot (B.assoc x y z) 
    ; identityˡ = λ x → A.ε , lift-quot (B.identityˡ x)
    ; inverseˡ = λ x → A.ε , lift-quot (B.inverseˡ x)
    ; comm = λ x y → A.ε , lift-quot (B.comm x y)
    }
  ; cokernel⇒ = record
    { ⟦_⟧ = λ x → x
    ; cong = λ { eq → A.ε , lift-quot eq }
    ; homo = λ x y → A.ε , quot-refl
    }
  ; isCokernel = record
    { commute = λ a → (a A.⁻¹) , quot-commute
    ; universal = λ {X} {h} eq →
      let module X = AbelianGroup X
          open SR X.setoid
          open MR (Delooping X)
      in record
        { ⟦_⟧ = λ x → ⟦ h ⟧ x
        ; cong = λ { {x} {y} (a , eq-a) → begin
          ⟦ h ⟧ x                            ≈˘⟨ cong h (quot-sym eq-a) ⟩
          ⟦ h ⟧ (y B.∙ ⟦ f ⟧ (a A.⁻¹))       ≈⟨ homo h y (⟦ f ⟧ (a A.⁻¹)) ⟩
          ⟦ h ⟧ y X.∙ ⟦ h ⟧ (⟦ f ⟧ (a A.⁻¹)) ≈⟨ elimʳ (eq (a A.⁻¹)) ⟩
          ⟦ h ⟧ y ∎
        }
        ; homo = λ x y → homo h x y
        }
    ; factors = λ {X} {h} {eq} x → X .refl
    ; unique = λ {X} {h} {i} {eq} eq x → X .sym (eq x)
    }
  }
  where
    module A = AbelianGroup A
    module B = AbelianGroup B

    abstract
      quot-refl : ∀ {b} → (b B.∙ ⟦ f ⟧ A.ε) B.≈ b
      quot-refl {b} = begin
        b B.∙ ⟦ f ⟧ A.ε ≈⟨ elimʳ (ε-homo f) ⟩
        b               ∎
        where
          open SR B.setoid
          open MR (Delooping B)

      quot-sym : ∀ {b₁ b₂} {a} → b₁ B.∙ ⟦ f ⟧ a B.≈ b₂ → b₂ B.∙ ⟦ f ⟧ (a A.⁻¹) B.≈ b₁
      quot-sym {b₁ = b₁} {b₂ = b₂} {a = a} eq = begin
        b₂ B.∙ ⟦ f ⟧ (a A.⁻¹)           ≈⟨ B.∙-congˡ (⁻¹-homo f a) ⟩
        b₂ B.∙ ⟦ f ⟧ a B.⁻¹             ≈˘⟨ B.∙-congʳ eq ⟩
        b₁ B.∙ ⟦ f ⟧ a B.∙ ⟦ f ⟧ a B.⁻¹ ≈⟨ cancelʳ (B.inverseʳ (⟦ f ⟧ a)) ⟩
        b₁                              ∎
        where
          open SR B.setoid
          open MR (Delooping B)

      quot-trans : ∀ {b₁ b₂ b₃} {a₁ a₂} → b₁ B.∙ ⟦ f ⟧ a₁ B.≈ b₂ → b₂ B.∙ ⟦ f ⟧ a₂ B.≈ b₃ → b₁ B.∙ ⟦ f ⟧ (a₁ A.∙ a₂) B.≈ b₃
      quot-trans {b₁ = b₁} {b₂ = b₂} {b₃ = b₃} {a₁ = a₁} {a₂ = a₂} eq₁ eq₂ = begin
        b₁ B.∙ ⟦ f ⟧ (a₁ A.∙ a₂)       ≈⟨ B.∙-congˡ (homo f a₁ a₂) ⟩
        b₁ B.∙ (⟦ f ⟧ a₁ B.∙ ⟦ f ⟧ a₂) ≈⟨ pullˡ eq₁ ⟩
        b₂ B.∙ ⟦ f ⟧ a₂                ≈⟨ eq₂ ⟩
        b₃                             ∎
        where
          open SR B.setoid
          open MR (Delooping B)

      quot-∙-cong : ∀ {b₁ b₂ b₃ b₄} {a₁ a₂} → b₁ B.∙ ⟦ f ⟧ a₁ B.≈ b₂ → b₃ B.∙ ⟦ f ⟧ a₂ B.≈ b₄ → b₁ B.∙ b₃ B.∙ ⟦ f ⟧ (a₁ A.∙ a₂) B.≈ b₂ B.∙ b₄
      quot-∙-cong {b₁ = b₁} {b₂ = b₂} {b₃ = b₃} {b₄ = b₄} {a₁ = a₁} {a₂ = a₂} eq₁ eq₂ = begin
        b₁ B.∙ b₃ B.∙ ⟦ f ⟧ (a₁ A.∙ a₂)       ≈⟨ B.∙-congˡ (homo f a₁ a₂) ⟩
        b₁ B.∙ b₃ B.∙ (⟦ f ⟧ a₁ B.∙ ⟦ f ⟧ a₂) ≈⟨ B.∙-congˡ (B.comm (⟦ f ⟧ a₁) (⟦ f ⟧ a₂)) ⟩
        b₁ B.∙ b₃ B.∙ (⟦ f ⟧ a₂ B.∙ ⟦ f ⟧ a₁) ≈⟨ center eq₂ ⟩
        b₁ B.∙ (b₄ B.∙ ⟦ f ⟧ a₁)            ≈⟨ B.∙-congˡ (B.comm b₄ (⟦ f ⟧ a₁)) ⟩
        b₁ B.∙ (⟦ f ⟧ a₁ B.∙ b₄)            ≈⟨ pullˡ eq₁ ⟩
        b₂ B.∙ b₄                             ∎
        where
          open SR B.setoid
          open MR (Delooping B)

      quot-inv-cong : ∀ {b₁ b₂} {a} → b₂ B.∙ ⟦ f ⟧ a B.≈ b₁ → (b₂ B.⁻¹) B.∙ ⟦ f ⟧ (a A.⁻¹) B.≈ (b₁ B.⁻¹)
      quot-inv-cong {b₁ = b₁} {b₂ = b₂} {a = a} eq = begin
        b₂ B.⁻¹ B.∙ ⟦ f ⟧ (a A.⁻¹) ≈⟨ B.∙-congˡ (⁻¹-homo f a) ⟩
        b₂ B.⁻¹ B.∙ ⟦ f ⟧ a B.⁻¹   ≈⟨ ⁻¹-∙-comm B b₂ (⟦ f ⟧ a) ⟩
        (b₂ B.∙ ⟦ f ⟧ a) B.⁻¹      ≈⟨ B.⁻¹-cong eq  ⟩
        b₁ B.⁻¹                    ∎
        where
          open SR B.setoid
          open MR (Delooping B)

      lift-quot : ∀ {b₁ b₂} → b₁ B.≈ b₂ → b₁ B.∙ ⟦ f ⟧ A.ε B.≈ b₂
      lift-quot {b₁} {b₂} eq = begin
        b₁ B.∙ ⟦ f ⟧ A.ε ≈⟨ elimʳ (ε-homo f) ⟩
        b₁               ≈⟨ eq ⟩
        b₂               ∎
        where
          open SR B.setoid
          open MR (Delooping B)

      quot-commute : ∀ {a} → ⟦ f ⟧ a B.∙ ⟦ f ⟧ (a A.⁻¹) B.≈ B.ε
      quot-commute {a = a} = begin
        ⟦ f ⟧ a B.∙ ⟦ f ⟧ (a A.⁻¹) ≈⟨ B.∙-congˡ (⁻¹-homo f a) ⟩
        ⟦ f ⟧ a B.∙ ⟦ f ⟧ a B.⁻¹   ≈⟨ B.inverseʳ (⟦ f ⟧ a) ⟩
        B.ε ∎
        where
          open SR B.setoid
          open MR (Delooping B)

-- Some facts about morphisms in Ab
module _ {A B : AbelianGroup (c ⊔ ℓ) (c ⊔ ℓ)} (f : AbelianGroupHomomorphism A B) where
  private
    module A = AbelianGroup A
    module B = AbelianGroup B

    module ker = Kernel (kernels {c = c ⊔ ℓ} f)
    module coker = Cokernel (cokernels {ℓ = c ⊔ ℓ} f)

    open Mor (AbelianGroups (c ⊔ ℓ) (c ⊔ ℓ))
    open Zero (𝟎 {c = (c ⊔ ℓ)} {ℓ = (c ⊔ ℓ)})
    open Category (AbelianGroups (c ⊔ ℓ) (c ⊔ ℓ))

  mono-trivial-kernel : Mono f → IsZero (AbelianGroups (c ⊔ ℓ) (c ⊔ ℓ)) ker.kernel
  mono-trivial-kernel f-mono = record
    { isInitial = record
      { ! = zero⇒
      ; !-unique = λ { {X} g (x , eq) →
        let module X = AbelianGroup X
            open SR X.setoid
        in begin
          X.ε                ≈˘⟨ ε-homo g ⟩
          ⟦ g ⟧ (A.ε , _)    ≈˘⟨ cong g (f-mono ker.kernel⇒ zero⇒ (λ { (x′ , eq′) → B.trans eq′ (B.sym (ε-homo f)) }) (x , eq)) ⟩
          ⟦ g ⟧ (x , eq) ∎
        }
      }
    ; isTerminal = record
      { ! = zero⇒
      ; !-unique = λ {X} g →
        let open SR B.setoid
        in f-mono zero⇒ (ker.kernel⇒ ∘ g) λ x → begin
          ⟦ f ⟧ A.ε               ≈⟨ ε-homo f ⟩
          B.ε                     ≈˘⟨ proj₂ (⟦ g ⟧ x) ⟩
          ⟦ f ⟧ (proj₁ (⟦ g ⟧ x)) ∎
      }
    }

  trivial-kernel-injective : ∀ {x y} → IsZero (AbelianGroups (c ⊔ ℓ) (c ⊔ ℓ)) ker.kernel → ⟦ f ⟧ x B.≈ ⟦ f ⟧ y → x A.≈ y
  trivial-kernel-injective {x = x} {y = y} kernel-zero eq =
    let
      -- First, let us show that x⁻¹y ∈ ker f
        in-kernel = begin
          ⟦ f ⟧ (x A.⁻¹ A.∙ y)       ≈⟨ homo f (x A.⁻¹) y ⟩
          ⟦ f ⟧ (x A.⁻¹) B.∙ ⟦ f ⟧ y ≈⟨ B.∙-cong (⁻¹-homo f x) (B.sym eq) ⟩
          (⟦ f ⟧ x B.⁻¹ B.∙ ⟦ f ⟧ x) ≈⟨ B.inverseˡ (⟦ f ⟧ x) ⟩
          B.ε ∎
        -- However, the kernel is trivial, so x⁻¹y ≈ ε
        is-inverse = zero-trivial kernel-zero ((x A.⁻¹ A.∙ y) , in-kernel) (A.ε , ε-homo f)
        -- Furthermore, inverses are unique, so this means that x ≈ y
    in ⁻¹-injective A $ inverseˡ-unique A (x A.⁻¹) y is-inverse
    where
      open SR B.setoid
      module kernel-zero = IsZero kernel-zero

  mono-injective : ∀ {x y} → Mono f → ⟦ f ⟧ x B.≈ ⟦ f ⟧ y → x A.≈ y
  mono-injective f-mono = trivial-kernel-injective (mono-trivial-kernel f-mono)

-- module _ {c ℓ} {H G : AbelianGroup (c ⊔ ℓ) (c ⊔ ℓ)} (sub : AbelianGroups (c ⊔ ℓ) (c ⊔ ℓ) [ H ↣ G ]) where
--   private
--     module G = AbelianGroup G
--     module H = AbelianGroup H
--     open Mor._↣_ sub renaming (mor to inj)
--     open SR G.setoid

--   record Quot (x y : G.Carrier) : Set (c ⊔ ℓ) where
--     constructor quot
--     field
--       witness : H.Carrier
--       element : ⟦ inj ⟧ witness G.≈ (x G.∙ (y G.⁻¹))
--       -- Need to show that if x ≈ y, that the two witnesses produced are the same!

--   open Quot

--   -- I guess this is right... huh
--   quot-cong : ∀ {x y} → (p q : Quot x y) → (witness p) H.≈ (witness q)
--   quot-cong {x = x} {y = y} eq p q = mono-injective {c = c} {ℓ = ℓ} inj mono $ begin
--     ⟦ inj ⟧ (witness p) ≈⟨ element p ⟩
--     (x G.∙ y G.⁻¹)      ≈˘⟨ element q ⟩
--     ⟦ inj ⟧ (witness q) ∎


  epi-trivial-cokernel : Epi f → IsZero (AbelianGroups (c ⊔ ℓ) (c ⊔ ℓ)) coker.cokernel
  epi-trivial-cokernel f-epi = record
    { isInitial = record
      { ! = zero⇒
      ; !-unique = λ {X} g →
        let module X = AbelianGroup X
            open SR X.setoid
        in f-epi zero⇒ (g ∘ coker.cokernel⇒) λ x → begin
          X.ε             ≈˘⟨ ε-homo g ⟩
          ⟦ g ⟧ B.ε       ≈˘⟨ cong g (coker.commute x) ⟩
          ⟦ g ⟧ (⟦ f ⟧ x) ∎
      }
    ; isTerminal = record
      { ! = zero⇒
      ; !-unique = λ {X} g x →
        let module X = AbelianGroup X
            open SR B.setoid
            open MR (Delooping B)
            (a , a-eq) = f-epi coker.cokernel⇒ zero⇒ (λ a → a A.⁻¹ , (B.trans (B.∙-congˡ (⁻¹-homo f a)) (B.inverseʳ (⟦ f ⟧ a)))) (⟦ g ⟧ x) 
            eq = begin 
              B.ε B.∙ ⟦ f ⟧ (a A.⁻¹)                 ≈⟨ B.∙-cong (B.sym a-eq) (⁻¹-homo f a) ⟩
              ⟦ g ⟧ x B.∙ ⟦ f ⟧ a B.∙ (⟦ f ⟧ a B.⁻¹) ≈⟨ cancelʳ (B.inverseʳ (⟦ f ⟧ a)) ⟩
              ⟦ g ⟧ x                                ∎
        in a A.⁻¹ , eq
      }
    }

  record Surjection : Set (c ⊔ ℓ) where
    field
      from : AbelianGroupHomomorphism B A
      right-inverse : ∀ (b : B.Carrier) → ⟦ f ⟧ (⟦ from ⟧ b) B.≈ b


  trivial-cokernel-surjective : IsZero (AbelianGroups (c ⊔ ℓ) (c ⊔ ℓ)) coker.cokernel → Surjection
  trivial-cokernel-surjective cokernel-zero = record
      { from = record
        { ⟦_⟧ = λ x → preimage x
        ; cong = λ {x} {y} x≈y →
          let open SR A.setoid
              ϕ = λ x → proj₁ (cokernel-zero.¡-unique {coker.cokernel} (zero⇒ {coker.cokernel} {coker.cokernel}) (x B.⁻¹))
          in begin
            -- ((proj₁ (cokernel-zero.¡-unique zero⇒ (x B.⁻¹)) A.⁻¹ A.∙ (proj₁ (cokernel-zero.¡-unique (coker.universal {!!}) (x B.⁻¹)) A.∙ A.ε)) A.⁻¹ A.∙ (proj₁ (cokernel-zero.¡-unique zero⇒ B.ε) A.⁻¹ A.∙ (proj₁ (cokernel-zero.¡-unique (coker.universal {!!}) B.ε) A.∙ A.ε) A.∙ A.ε)) ≈⟨ {!!} ⟩
            ((ϕ x A.⁻¹ A.∙ ({!!} A.∙ A.ε)) A.⁻¹ A.∙ ({!ϕ x!} A.⁻¹ A.∙ ({!ϕ x!} A.∙ A.ε) A.∙ A.ε)) ≈⟨ {!!} ⟩
            ((ϕ y A.⁻¹ A.∙ ({!foo!} A.∙ A.ε)) A.⁻¹ A.∙ ({!!} A.⁻¹ A.∙ ({!!} A.∙ A.ε) A.∙ A.ε)) ∎
        ; homo = {!!}
        }
      ; right-inverse = {!!}
      }
      where
        module cokernel-zero = IsZero cokernel-zero

        preimage : B.Carrier → A.Carrier
        preimage x = proj₁ (zero-trivial cokernel-zero (⟦ coker.cokernel⇒ ⟧ (x B.⁻¹)) (coker.cokernel .ε))

        preimage-eq : (x : B.Carrier) → x B.⁻¹ B.∙ ⟦ f ⟧ (preimage x) B.≈ B.ε
        preimage-eq x = proj₂ (zero-trivial cokernel-zero (⟦ coker.cokernel⇒ ⟧ (x B.⁻¹)) (coker.cokernel .ε))

        quot-cong : ∀ {x y} → x B.≈ y → preimage x A.≈ preimage y
        quot-cong eq = mono-injective {!!} {!!}
  --       -- proj₂ (zero-trivial cokernel-zero (⟦ coker.cokernel⇒ ⟧ (x B.⁻¹)) (coker.cokernel .ε))
  -- This is wrong :(
  -- trivial-cokernel-surjective : IsZero (AbelianGroups (c ⊔ ℓ) (c ⊔ ℓ)) coker.cokernel → (x : B.Carrier) → Σ[ a ∈ A.Carrier ] (⟦ f ⟧ a B.≈ x)
  -- trivial-cokernel-surjective cokernel-zero x =
  --   let open SR B.setoid
  --       -- As the cokernel is trivial, all elements of it are equal.
  --       -- However, due to how equality in the cokernel is defined
  --       -- (IE: b₁ ≈ b₁ := Σ[ a ∈ A ], b₁ ∙ ⟦ f ⟧ a ≈ b₂)
  --       -- we get an explicit element a ∈ A such that 'x⁻¹ ∙ f a ≈ ε'
  --       (a , coker-eq) = zero-trivial cokernel-zero (⟦ coker.cokernel⇒ ⟧ (x B.⁻¹)) (coker.cokernel .ε)
  --       -- However, inverses are unique, so 'f a ≈ x'
  --       is-inverse = begin
  --         (x B.∙ (⟦ f ⟧ a) B.⁻¹) B.⁻¹      ≈˘⟨ ⁻¹-∙-comm B x ((⟦ f ⟧ a) B.⁻¹) ⟩
  --         x B.⁻¹ B.∙ (⟦ f ⟧ a B.⁻¹) B.⁻¹   ≈⟨ B.∙-congˡ (⁻¹-involutive B (⟦ f ⟧ a)) ⟩
  --         x B.⁻¹ B.∙ ⟦ f ⟧ a               ≈⟨ coker-eq ⟩
  --         B.ε                              ≈˘⟨ ε⁻¹≈ε B ⟩
  --         B.ε B.⁻¹                         ∎
  --   in a , ⁻¹-injective B (inverseʳ-unique B x ((⟦ f ⟧ a) B.⁻¹) (⁻¹-injective B is-inverse))
  --   where
  --     module cokernel-zero = IsZero cokernel-zero

  -- -- We don't really care how this computes, so let's mark it as abstract
  -- abstract
  --   epi-surjective : Epi f → (x : B.Carrier) → Σ[ a ∈ A.Carrier ] (⟦ f ⟧ a B.≈ x)
  --   epi-surjective f-epi = trivial-cokernel-surjective (epi-trivial-cokernel f-epi)

  --   preimage : Epi f → B.Carrier → A.Carrier
  --   preimage f-epi b = proj₁ (epi-surjective f-epi b)

AbelianGroupsPreAbelian : PreAbelian (AbelianGroups (c ⊔ ℓ) (c ⊔ ℓ))
AbelianGroupsPreAbelian {c = c} {ℓ = ℓ} = record
  { additive = AbelianGroupsAdditive
  ; kernel = kernels {c = (c ⊔ ℓ)} {ℓ = (c ⊔ ℓ)}
  ; cokernel = cokernels {c = (c ⊔ ℓ)} {ℓ = (c ⊔ ℓ)}
  }

{-# OPTIONS --without-K --safe #-}
module Categories.Category.Instance.Nat where

-- Skeleton of FinSetoid as a Category

open import Level

open import Data.Fin.Base using (Fin; _↑ˡ_; _↑ʳ_; splitAt; join; remQuot; combine)
open import Data.Fin.Properties using (join-splitAt; splitAt-↑ˡ; splitAt-↑ʳ; combine-remQuot;
  remQuot-combine)
open import Data.Nat.Base using (ℕ; _+_; _*_)
open import Data.Product using (proj₁; proj₂; uncurry; <_,_>)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Sum.Properties using ([,]-∘; [,]-cong)
open import Relation.Binary.PropositionalEquality
  using (_≗_; _≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)
open import Function using (id; _∘′_; case_returning_of_)

open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Cartesian.Bundle using (CartesianCategory)
open import Categories.Category.Cocartesian using (Cocartesian)
open import Categories.Category.Cocartesian.Bundle using (CocartesianCategory)
open import Categories.Category.Core using (Category)
open import Categories.Category.Duality using (Cocartesian⇒coCartesian; coCartesian⇒Cocartesian)
open import Categories.Object.Coproduct using (Coproduct)
open import Categories.Object.Duality using (Coproduct⇒coProduct; coProduct⇒Coproduct)
open import Categories.Object.Product using (Product)

Nat : Category 0ℓ 0ℓ 0ℓ
Nat = record
  { Obj = ℕ
  ; _⇒_ = λ m n → (Fin m → Fin n)
  ; _≈_ = _≗_
  ; id = id
  ; _∘_ = _∘′_
  ; assoc = λ _ → refl
  ; sym-assoc = λ _ → refl
  ; identityˡ = λ _ → refl
  ; identityʳ = λ _ → refl
  ; identity² = λ _ → refl
  ; equiv = record
    { refl = λ _ → refl
    ; sym = λ x≡y z → sym (x≡y z)
    ; trans = λ x≡y y≡z w → trans (x≡y w) (y≡z w)
    }
  ; ∘-resp-≈ = λ {_ _ _ f h g i} f≗h g≗i x → trans (f≗h (g x)) (cong h (g≗i x))
  }

-- For other uses, it is important to choose coproducts
-- in theory, it should be strictly associative... but it's not, and won't be for any choice.
Coprod : (m n : ℕ) → Coproduct Nat m n
Coprod m n = record
  { A+B = m + n
  ; i₁ = _↑ˡ n
  ; i₂ = m ↑ʳ_
  ; [_,_] = λ l r z → [ l , r ]′ (splitAt m z)
  ; inject₁ = λ {_ f g} x → cong [ f , g ]′ (splitAt-↑ˡ m x n)
  ; inject₂ = λ {_ f g} x → cong [ f , g ]′ (splitAt-↑ʳ m n x)
  ; unique = uniq
  }
  where
    open ≡-Reasoning
    uniq : {o : ℕ} {h : Fin (m + n) → Fin o} {f : Fin m → Fin o} {g : Fin n → Fin o} →
      h ∘′ (_↑ˡ n) ≗ f → h ∘′ (m ↑ʳ_) ≗ g → (λ z → [ f , g ]′ (splitAt m z)) ≗ h
    uniq {_} {h} {f} {g} h≗f h≗g w = begin
      [ f , g ]′ (splitAt m w)                       ≡˘⟨ [,]-cong h≗f h≗g (splitAt m w) ⟩
      [ h ∘′ (_↑ˡ n) , h ∘′ (m ↑ʳ_) ]′ (splitAt m w) ≡˘⟨ [,]-∘ h (splitAt m w) ⟩
      h ([ _↑ˡ n , m ↑ʳ_ ]′ (splitAt m w))           ≡⟨ cong h (join-splitAt m n w) ⟩
      h w                                            ∎

Nat-Cocartesian : Cocartesian Nat
Nat-Cocartesian = record
  { initial = record
    { ⊥ = 0
    ; ⊥-is-initial = record
      { ¡ = λ ()
      ; ¡-unique = λ _ ()
      }
    }
  ; coproducts = record { coproduct = λ {m} {n} → Coprod m n }
  }

Prod : (m n : ℕ) → Product Nat m n
Prod m n = record
  { A×B = m * n
  ; π₁ = proj₁ ∘′ remQuot n
  ; π₂ = proj₂ ∘′ remQuot {m} n
  ; ⟨_,_⟩ = λ l r z → uncurry combine (< l , r > z)
  ; project₁ = λ {_ f g} z → cong proj₁ (remQuot-combine (f z) (g z))
  ; project₂ = λ {_ f g} z → cong proj₂ (remQuot-combine (f z) (g z))
  ; unique = uniq
  }
  where
    open ≡-Reasoning
    uniq : {o : ℕ} {h : Fin o → Fin (m * n)} {f : Fin o → Fin m} {g : Fin o → Fin n} →
      proj₁ ∘′ remQuot n ∘′ h ≗ f →  proj₂ ∘′ remQuot {m} n ∘′ h ≗ g → uncurry combine ∘′ < f , g > ≗ h
    uniq {_} {h} {f} {g} h≗f h≗g w = begin
      combine (f w) (g w)                                                 ≡˘⟨ cong₂ combine (h≗f w) (h≗g w) ⟩
      combine (proj₁ (remQuot {m} n (h w))) (proj₂ (remQuot {m} n (h w))) ≡⟨ combine-remQuot {m} n (h w) ⟩
      h w                                                                 ∎

Nat-Cartesian : Cartesian Nat
Nat-Cartesian = record
  { terminal = record
    { ⊤ = 1
    ; ⊤-is-terminal = record
      { !-unique = λ f x → case f x returning (Fin.zero ≡_) of λ { Fin.zero → refl }
      }
    }
  ; products = record {product = λ {m} {n} → Prod m n }
  }

-- And Natop is what is used a lot, so record some things here too
Natop : Category 0ℓ 0ℓ 0ℓ
Natop = Category.op Nat

Natop-Product : (m n : ℕ) → Product Natop m n
Natop-Product m n = Coproduct⇒coProduct Nat (Coprod m n)

Natop-Cartesian : CartesianCategory 0ℓ 0ℓ 0ℓ
Natop-Cartesian = record
  { U = Natop
  ; cartesian = Cocartesian⇒coCartesian Nat Nat-Cocartesian
  }

Natop-Coprod : (m n : ℕ) → Coproduct Natop m n
Natop-Coprod m n = coProduct⇒Coproduct Natop (Prod m n)

Natop-Cocartesian : CocartesianCategory 0ℓ 0ℓ 0ℓ
Natop-Cocartesian = record
  { U = Natop
  ; cocartesian = coCartesian⇒Cocartesian Natop Nat-Cartesian
  }

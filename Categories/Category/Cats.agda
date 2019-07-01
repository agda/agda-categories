{-# OPTIONS --without-K --safe #-}
module Categories.Category.Cats where

open import Level
open import Categories.Category
open import Categories.Functor
open import Categories.Functor.Properties
import Categories.Morphism as M
import Categories.Square as Square

private
  variable
    o ℓ e : Level
    C D E : Category o ℓ e
    F G H I : Functor C D

Cats : ∀ o ℓ e → Category _ _ _
Cats o ℓ e = record
  { Obj       = Category o ℓ e
  ; _⇒_       = Functor
  ; _≈_       = _≋_
  ; id        = id
  ; _∘_       = _∘F_
  ; assoc     = λ {_ _ _ _ H G F} → assoc′ {F = F} {G = G} {H = H}
  ; identityˡ = λ {_ _ F} → record
    { obj≅  = M.≅-refl (Fcod F)
    ; conj≈ = let open Category (Fcod F)
                  open Equiv
              in trans identityˡ identityʳ
    }
  ; identityʳ = λ {_ _ F} → record
    { obj≅  = M.≅-refl (Fcod F)
    ; conj≈ = let open Category (Fcod F)
                  open Equiv
              in trans identityˡ identityʳ
    }
  ; equiv     = ≋-isEquivalence
  ; ∘-resp-≈  = ∘-resp-≈′
  }
  where Fcod : Functor C D → Category _ _ _
        Fcod {D = D} F = D
        
        assoc′ : (F ∘F G) ∘F H ≋ F ∘F G ∘F H
        assoc′ {F = F} {G = G} {H = H} = record
          { obj≅  = ≅-refl
          ; conj≈ = trans identityˡ identityʳ
          }
          where open M (Fcod F)
                open Category (Fcod F)
                open HomReasoning
                
        ∘-resp-≈′ : F ≋ H → G ≋ I → F ∘F G ≋ H ∘F I
        ∘-resp-≈′ {F = F} {H = H} {G = G} {I = I} eq eq′ = record
          { obj≅  = ≅-trans (obj≅ eq) ([ H ]-resp-≅ (obj≅ eq′))
          ; conj≈ = λ {_ _ f} → begin
            (F₁ H (from (obj≅ eq′)) ∘ from (obj≅ eq)) ∘
              F₁ F (F₁ G f) ∘ to (obj≅ eq) ∘ F₁ H (to (obj≅ eq′))         ≈⟨ assoc ⟩
            F₁ H (from (obj≅ eq′)) ∘ from (obj≅ eq) ∘
              F₁ F (F₁ G f) ∘ to (obj≅ eq) ∘ F₁ H (to (obj≅ eq′))         ≈˘⟨ refl ⟩∘⟨ refl ⟩∘⟨ assoc ⟩
            F₁ H (from (obj≅ eq′)) ∘ from (obj≅ eq) ∘
              (F₁ F (F₁ G f) ∘ to (obj≅ eq)) ∘ F₁ H (to (obj≅ eq′))       ≈⟨ refl ⟩∘⟨ pullˡ (conj≈ eq) ⟩
            F₁ H (from (obj≅ eq′)) ∘ F₁ H (F₁ G f) ∘ F₁ H (to (obj≅ eq′)) ≈˘⟨ refl ⟩∘⟨ homomorphism H ⟩
            F₁ H (from (obj≅ eq′)) ∘ F₁ H (F₁ G f D.∘ to (obj≅ eq′))      ≈˘⟨ homomorphism H ⟩
            F₁ H (from (obj≅ eq′) D.∘ F₁ G f D.∘ to (obj≅ eq′))           ≈⟨ F-resp-≈ H (conj≈ eq′) ⟩
            F₁ H (F₁ I f)                                                 ∎
          }
          where module D = Category (Fcod G)
                open M (Fcod F)
                open Category (Fcod F)
                open Square (Fcod F)
                open HomReasoning
                open _≋_
                open Functor
                open M._≅_

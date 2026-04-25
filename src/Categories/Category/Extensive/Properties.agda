{-# OPTIONS --without-K --safe #-}

-- open import Level
open import Categories.Category.Core using (Category)

open import Data.Fin using (Fin; zero) renaming (suc to nzero)

module Categories.Category.Extensive.Properties {o ℓ e} (𝒞 : Category o ℓ e) where

open import Categories.Category.Extensive using (Extensive)
open import Categories.Diagram.Pullback 𝒞 using (Pullback; IsPullback; Pullback-resp-≈; unglue′) 
open import Categories.Object.Coproduct 𝒞 using (IsCoproduct; Coproduct; IsCoproduct⇒Coproduct)

import Categories.Morphism as M
import Categories.Morphism.Reasoning as MR

open Category 𝒞
open M 𝒞
open MR 𝒞
open HomReasoning
open Equiv

module _ (extensive : Extensive 𝒞) where
  open Extensive extensive
  open CC using (_+_; i₁; i₂; ¡; ⊥; +₁∘i₁; +₁∘i₂; ¡-unique₂; _+₁_; inject₁; inject₂; ∘-distribˡ-[]; []-cong₂; +₁∘+-swap; initial; coproducts)

  -- For coproducts with equal injections there is at most one outgoing morphism
  equal-inj : ∀ {A C D} (f : A ⇒ C) → IsCoproduct f f → (g h : C ⇒ D) → g ≈ h
  equal-inj f cp g h = sym CP.g-η ○ CP.[]-cong₂ gf≈hf gf≈hf ○ CP.g-η
    where
      module CP = Coproduct (IsCoproduct⇒Coproduct cp)
      gf≈hf = sym CP.inject₁ ○ CP.inject₂

  to-⊥-is-iso : ∀ {A} (f : A ⇒ ⊥) → IsIso f
  to-⊥-is-iso f .M.IsIso.inv = CC.initial.!
  to-⊥-is-iso f .M.IsIso.iso .M.Iso.isoʳ = ¡-unique₂ _ _
  to-⊥-is-iso f .M.IsIso.iso .M.Iso.isoˡ = equal-inj id (pullback-of-cp-is-cp' pb₁ pb₂) (initial.! ∘ f) id
    where
      pb₁ : Pullback (i₁ ∘ f) i₁
      pb₁ = record
        { p₁ = id ; p₂ = f
        ; isPullback = record
            { commute         = identityʳ
            ; universal       = λ {_} {h₁} _ → h₁
            ; p₁∘universal≈h₁ = identityˡ
            ; p₂∘universal≈h₂ = λ {_} {_} {_} {eq} → pullback₁-is-mono {⊥} {⊥} _ _ (sym-assoc ○ eq)
            ; unique-diagram  = λ eq₁ _ → sym identityˡ ○ eq₁ ○ identityˡ
            } }
      pb₂ : Pullback (i₁ ∘ f) i₂
      pb₂ = record
        { p₁ = id ; p₂ = f
        ; isPullback = record
            { commute         = identityʳ ○ ∘-resp-≈ˡ (¡-unique₂ _ _)
            ; universal       = λ {_} {h₁} _ → h₁
            ; p₁∘universal≈h₁ = identityˡ
            ; p₂∘universal≈h₂ = λ {_} {_} {_} {eq} → pullback₁-is-mono {⊥} {⊥} _ _ (sym-assoc ○ eq ○ ∘-resp-≈ˡ (¡-unique₂ _ _))
            ; unique-diagram  = λ eq₁ _ → sym identityˡ ○ eq₁ ○ identityˡ
            } }

  -- The naturality square for i₁ is a pullback in any extensive category
  i₁-cartesian : ∀ {A B C D} (f : A ⇒ B) (g : C ⇒ D) → IsPullback f i₁ i₁ (f +₁ g)
  i₁-cartesian {A} {B} {C} {D} f g = record
    { commute         = sym +₁∘i₁
    ; universal       = universal
    ; p₁∘universal≈h₁ = p₁∘universal≈h₁
    ; p₂∘universal≈h₂ = p₂∘universal≈h₂
    ; unique-diagram  = λ _ → pullback₁-is-mono _ _
    }
    where
      open Pullback using (p₁; p₂; commute)

      clash : ∀ {Q} {h₁ : Q ⇒ B} {h₂ : Q ⇒ A + C} → i₁ ∘ h₁ ≈ (f +₁ g) ∘ h₂ → Pullback.P (pullback₂ h₂) ⇒ initial.⊥
      clash {_}{h₁}{h₂} eq = IsPullback.universal disjoint
        (begin
            i₁ ∘ h₁ ∘ p₁ (pullback₂ h₂)                     ≈⟨ extendʳ eq ⟩
            (f +₁ g) ∘ h₂ ∘ p₁ (pullback₂ h₂)               ≈⟨ refl⟩∘⟨ commute (pullback₂ h₂) ⟩
            (f +₁ g) ∘ i₂ ∘ p₂ (pullback₂ h₂)               ≈⟨ extendʳ +₁∘i₂ ⟩
            i₂ ∘ g ∘ p₂ (pullback₂ h₂)                      ∎)

      universal : ∀ {Q} {h₁ : Q ⇒ B} {h₂ : Q ⇒ A + C} → i₁ ∘ h₁ ≈ (f +₁ g) ∘ h₂ → Q ⇒ A
      universal {_} {h₁} {h₂} eq = CP.[ p₂ pb₁ , ¡ ∘ clash eq ]
        where
          pb₁ = pullback₁ h₂
          
          module CP = IsCoproduct (pullback-of-cp-is-cp h₂)

      p₂∘universal≈h₂ : ∀ {Q} {h₁ : Q ⇒ B} {h₂ : Q ⇒ A + C} {eq : i₁ ∘ h₁ ≈ (f +₁ g) ∘ h₂} → i₁ ∘ universal eq ≈ h₂
      p₂∘universal≈h₂ {_} {h₁} {h₂} {eq} = begin
          i₁ ∘ CP.[ p₂ pb₁ , ¡ ∘ clash eq ]              ≈⟨ CP.∘-distribˡ-[] ⟩
          CP.[ i₁ ∘ p₂ pb₁ , i₁ ∘ ¡ ∘ clash eq ]         ≈⟨ CP.[]-cong₂ refl (pullˡ (¡-unique₂ _ _)) ⟩
          CP.[ i₁ ∘ p₂ pb₁ , ¡ ∘ clash eq ]              ≈⟨ CP.[]-cong₂ h₂-pb₁ h₂-pb₂ ⟨
          CP.[ h₂ ∘ p₁ pb₁ , h₂ ∘ p₁ pb₂ ]               ≈⟨ CP.g-η ⟩
          h₂                                             ∎
          
        where
          pb₁ = pullback₁ h₂
          pb₂ = pullback₂ h₂
          
          module CP = Coproduct (IsCoproduct⇒Coproduct (pullback-of-cp-is-cp h₂))
          
          h₂-pb₁ : h₂ ∘ p₁ pb₁ ≈ i₁ ∘ p₂ pb₁
          h₂-pb₁ = commute pb₁

          clash-inv = M.IsIso.inv (to-⊥-is-iso (clash eq))
          isoˡ = M.Iso.isoˡ (M.IsIso.iso (to-⊥-is-iso (clash eq)))
          
          h₂-pb₂ : h₂ ∘ p₁ pb₂ ≈ ¡ ∘ clash eq
          h₂-pb₂ = begin
            h₂ ∘ p₁ pb₂                               ≈⟨ commute pb₂ ⟩
            i₂ ∘ p₂ pb₂                               ≈⟨ introʳ isoˡ ⟩ 
            (i₂ ∘ p₂ pb₂) ∘ clash-inv ∘ clash eq      ≈⟨ pullˡ (¡-unique₂ _ _) ⟩ 
            ¡ ∘ clash eq                              ∎

      p₁∘universal≈h₁ : ∀ {Q} {h₁ : Q ⇒ B} {h₂ : Q ⇒ A + C} {eq : i₁ ∘ h₁ ≈ (f +₁ g) ∘ h₂} → f ∘ universal eq ≈ h₁
      p₁∘universal≈h₁ {_} {h₁} {h₂} {eq} = pullback₁-is-mono (f ∘ CP.[ p₂ pb₁ , ¡ ∘ clash eq ]) h₁
         (begin
            i₁ ∘ f ∘ CP.[ p₂ pb₁ , ¡ ∘ clash eq ]                ≈⟨ pushˡ inject₁ ⟨ 
            ((f +₁ g) ∘ i₁) ∘ CP.[ p₂ pb₁ , ¡ ∘ clash eq ]       ≈⟨ pullʳ p₂∘universal≈h₂ ⟩ 
            (f +₁ g) ∘ h₂                                        ≈⟨ eq ⟨ 
            i₁ ∘ h₁                                              ∎)
           where
             pb₁ = pullback₁ h₂
             pb₂ = pullback₂ h₂
          
             module CP = Coproduct (IsCoproduct⇒Coproduct (pullback-of-cp-is-cp h₂))
         
  -- The naturality square for i₂ is a pullback in any extensive category
  i₂-cartesian : ∀ {A B C D} (f : A ⇒ B) (g : C ⇒ D) → IsPullback g i₂ i₂ (f +₁ g)
  i₂-cartesian {A} {B} {C} {D} f g = unglue′ (sym +₁∘+-swap) (sym CC.inject₂) jm other-pb
   where
     jm : JointMono₂ (f +₁ g) CC.+-swap
     jm h₁ h₂ h = begin
       h₁                                      ≈⟨ introˡ CC.+-swap∘swap  ⟩ 
       (CC.+-swap ∘ CC.+-swap) ∘  h₁           ≈⟨ pullʳ (h (nzero zero)) ⟩ 
       CC.+-swap ∘ CC.+-swap ∘ h₂              ≈⟨ cancelˡ CC.+-swap∘swap  ⟩
       h₂                                      ∎ 

     other-pb : IsPullback g (CC.+-swap ∘ i₂) (CC.+-swap ∘ i₂) (g +₁ f)
     other-pb .IsPullback.commute =
       begin
         (CC.+-swap ∘ i₂) ∘ g                  ≈⟨ inject₂ ⟩∘⟨refl ⟩
         i₁ ∘ g                                ≈⟨ IsPullback.commute (i₁-cartesian g f) ⟩
         (g +₁ f) ∘ i₁                         ≈⟨ refl ⟩∘⟨ inject₂ ⟨
         (g +₁ f) ∘ CC.+-swap ∘ i₂  ∎
         
     other-pb .IsPullback.universal eq = IsPullback.universal (i₁-cartesian g f) (∘-resp-≈ˡ (sym inject₂) ○ eq ) 
     other-pb .IsPullback.p₁∘universal≈h₁ = IsPullback.p₁∘universal≈h₁ (i₁-cartesian g f) 
     other-pb .IsPullback.p₂∘universal≈h₂ = ∘-resp-≈ˡ inject₂ ○ IsPullback.p₂∘universal≈h₂ (i₁-cartesian g f)  
     other-pb .IsPullback.unique-diagram eq eq' = IsPullback.unique-diagram (i₁-cartesian g f) eq (sym (∘-resp-≈ˡ inject₂) ○ eq' ○ ∘-resp-≈ˡ inject₂) 

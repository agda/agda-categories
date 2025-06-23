{-# OPTIONS --without-K --safe #-}

open import Categories.Category

-- we use duality to prove properties about coequalizer
module Categories.Diagram.Coequalizer.Properties {o ℓ e} (𝒞 : Category o ℓ e) where

open Category 𝒞

open import Categories.Diagram.Coequalizer 𝒞 using (Coequalizer; IsCoequalizer; Coequalizer⇒Epi; up-to-iso)
open import Categories.Morphism 𝒞 using (_RetractOf_; _≅_)
open _≅_
import Categories.Morphism.Reasoning as MR
open import Categories.Diagram.Equalizer op using (Equalizer)
open import Categories.Diagram.Equalizer.Properties op using (section-equalizer)
open import Categories.Diagram.Duality 𝒞 using (Coequalizer⇒coEqualizer; IscoEqualizer⇒IsCoequalizer)
open import Categories.Diagram.KernelPair 𝒞 using (KernelPair)
open import Categories.Diagram.Pullback 𝒞 using (Pullback; IsPullback)
open import Categories.Morphism.Regular 𝒞 using (RegularEpi)


import Relation.Binary.Reasoning.Setoid as SR

open Pullback hiding (universal; unique)

private
  variable
    A B : Obj
    f g : A ⇒ B

module _ (coe : Coequalizer f g) where
  open Coequalizer coe

  private
    equalizer : Equalizer f g
    equalizer = Coequalizer⇒coEqualizer coe

  open Equalizer equalizer
    using (unique′; unique-diagram)
    renaming ( id-equalize      to id-coequalize
             ; equalize-resp-≈  to coequalize-resp-≈
             ; equalize-resp-≈′ to coequalize-resp-≈′
             )
    public

-- a regular epi is a coequalizer of its kernel pair
regular-is-coeq-kp : {A B : Obj} (f : A ⇒ B) → RegularEpi f → (kp : KernelPair f) → IsCoequalizer (p₁ kp) (p₂ kp) f
regular-is-coeq-kp {A} {B} f record { C = D ; h = h ; g = g ; coequalizer = coeq } kp = record
  { equality   = IsPullback.commute (isPullback kp)
  ; coequalize = λ {_}{u} u∘p₁≈u∘p₂ → coequalize (u∘h≈u∘g u u∘p₁≈u∘p₂)
  ; universal  = universal
  ; unique     = unique
  }

  where
    open IsCoequalizer coeq
    pb-univ : D ⇒ P kp
    pb-univ = IsPullback.universal (isPullback kp) equality

    u∘h≈u∘g : {X : Obj} → (u : A ⇒ X) → u ∘ (p₁ kp) ≈ u ∘ (p₂ kp) → u ∘ h ≈ u ∘ g
    u∘h≈u∘g {X} u u∘p₁≈u∘p₂ = begin
      u ∘ h                   ≈˘⟨ refl⟩∘⟨ p₁∘universal≈h₁ kp ⟩
      u ∘ (p₁ kp  ∘ pb-univ)  ≈⟨ pullˡ u∘p₁≈u∘p₂ ⟩
      (u ∘ p₂ kp) ∘ pb-univ   ≈⟨ pullʳ (p₂∘universal≈h₂ kp) ⟩
      u ∘ g                   ∎
      where
        open HomReasoning
        open MR 𝒞

retract-coequalizer : ∀ {X Y} {f : Y ⇒ X} {g : X ⇒ Y} → f RetractOf g → IsCoequalizer (g ∘ f) id f
retract-coequalizer f∘g≈id = IscoEqualizer⇒IsCoequalizer (section-equalizer f∘g≈id)


module SplitCoequalizer {A B C : Obj} {f g : A ⇒ B} {e : B ⇒ C}
  (t : B ⇒ A) (s : C ⇒ B) (eq : e ∘ f ≈ e ∘ g) where
  -- split coequalizer are coequalizer --
  splitCoequalizer⇒Coequalizer : (tisSection : f ∘ t ≈ id)
                                 (sisSection : e ∘ s ≈ id)
                                 (sq : s ∘ e ≈ g ∘ t)
                               → IsCoequalizer f g e
  splitCoequalizer⇒Coequalizer tisSection sisSection sq = record
    { equality = eq
    ; coequalize = λ {_} {h} _ → h ∘ s
    ; universal = λ {_} {h} {h∘f≈h∘g} → begin
      h           ≈⟨ introʳ tisSection ⟩
      h ∘ f ∘ t   ≈⟨ extendʳ h∘f≈h∘g ⟩
      h ∘ g ∘ t   ≈⟨ pushʳ (⟺ sq) ⟩
      (h ∘ s) ∘ e ∎
    ; unique = λ {_} {h} {i} {h∘f≈h∘g} h≈i∘e → begin
      i         ≈⟨ introʳ sisSection ⟩
      i ∘ e ∘ s ≈⟨ pullˡ (⟺ h≈i∘e) ⟩
      h ∘ s     ∎
    }
    where
      open HomReasoning
      open MR 𝒞

  splitCoequalizer⇒Coequalizer-sym : (tisSection : g ∘ t ≈ id)
                                     (sisSection : e ∘ s ≈ id)
                                     (sq : s ∘ e ≈ f ∘ t)
                                   → IsCoequalizer f g e
  splitCoequalizer⇒Coequalizer-sym tisSection sisSection sq = record
    { equality = eq
    ; coequalize = λ {_} {h} _ → h ∘ s
    ; universal = λ {_} {h} {h∘f≈h∘g} → begin
      h           ≈⟨ introʳ tisSection ⟩
      h ∘ g ∘ t   ≈⟨ extendʳ (⟺ h∘f≈h∘g) ⟩
      h ∘ f ∘ t   ≈⟨ pushʳ (⟺ sq) ⟩
      (h ∘ s) ∘ e ∎
    ; unique = λ {_} {h} {i} {h∘f≈h∘g} h≈i∘e → begin
      i         ≈⟨ introʳ sisSection ⟩
      i ∘ e ∘ s ≈⟨ pullˡ (⟺ h≈i∘e) ⟩
      h ∘ s     ∎
    }
    where
      open HomReasoning
      open MR 𝒞

open SplitCoequalizer public

open Categories.Category.Definitions 𝒞 using (CommutativeSquare)

module MapBetweenCoequalizers
  {A₁ B₁ A₂ B₂ : Obj} {f₁ g₁ : A₁ ⇒ B₁} {f₂ g₂ : A₂ ⇒ B₂}
  (α : A₁ ⇒ A₂) (β : B₁ ⇒ B₂)
  (sq₁ : CommutativeSquare α f₁ f₂ β)                -- f₂ ∘ α ≈ β ∘ f₁
  (sq₂ : CommutativeSquare α g₁ g₂ β)                -- g₂ ∘ α ≈ β ∘ g₁
  where
  open Coequalizer

  ⇒coequalize : (coeq₂ : Coequalizer f₂ g₂) → (arr coeq₂ ∘ β) ∘ f₁ ≈ (arr coeq₂ ∘ β) ∘ g₁
  ⇒coequalize coeq₂ = begin
    (arr coeq₂ ∘ β) ∘ f₁ ≈⟨ extendˡ (⟺ sq₁) ⟩
    (arr coeq₂ ∘ f₂) ∘ α ≈⟨ equality coeq₂ ⟩∘⟨refl ⟩
    (arr coeq₂ ∘ g₂) ∘ α ≈⟨ extendˡ sq₂ ⟩
    (arr coeq₂ ∘ β) ∘ g₁ ∎
    where
      open HomReasoning
      open MR 𝒞

  ⇒MapBetweenCoeq : (coeq₁ : Coequalizer f₁ g₁)
                  → (coeq₂ : Coequalizer f₂ g₂)
                  → obj coeq₁ ⇒ obj coeq₂
  ⇒MapBetweenCoeq coeq₁ coeq₂ = coequalize coeq₁ (⇒coequalize coeq₂)
    where
      open HomReasoning

  ⇒MapBetweenCoeqSq : (coeq₁ : Coequalizer f₁ g₁)
                    → (coeq₂ : Coequalizer f₂ g₂)
                    → CommutativeSquare
                        β (arr coeq₁)
                        (arr coeq₂) (⇒MapBetweenCoeq coeq₁ coeq₂)
  ⇒MapBetweenCoeqSq coeq₁ coeq₂ = universal coeq₁

open MapBetweenCoequalizers public

CoeqOfIsomorphicDiagram : {A B : Obj} {f g : A ⇒ B} (coeq : Coequalizer f g )
                        → {A' B' : Obj}
                        → (a : A ≅ A') (b : B ≅ B')
                        → Coequalizer (from b ∘ f ∘ to a) (from b ∘ g ∘ to a)
CoeqOfIsomorphicDiagram {f = f} {g} coeq {A'} {B'} a b = record
  { arr = arr ∘ to b
  ; isCoequalizer = record
    { equality = begin
        (arr ∘ to b) ∘ from b ∘ f ∘ to a ≈⟨ assoc²γβ ⟩
        (arr ∘ to b ∘ from b) ∘ f ∘ to a ≈⟨ elimʳ (isoˡ b) ⟩∘⟨refl ⟩
        arr ∘ f ∘ to a                   ≈⟨ extendʳ equality ⟩
        arr ∘ g ∘ to a                   ≈⟨ introʳ (isoˡ b) ⟩∘⟨refl ⟩
        (arr ∘ to b ∘ from b) ∘ g ∘ to a ≈⟨ assoc²βγ ⟩
        (arr ∘ to b) ∘ from b ∘ g ∘ to a ∎
    ; coequalize = coequalize'
    ; universal =  λ {_} {h} {eq} → begin
        h                             ≈⟨ switch-fromtoʳ b universal ⟩
        (coequalize' eq ∘ arr) ∘ to b ≈⟨ assoc ⟩
        coequalize' eq ∘ (arr ∘ to b) ∎
    ; unique = λ {_} {h} {i} {eq} e → unique (⟺ (switch-tofromʳ b (begin
        (i ∘ arr) ∘ to b ≈⟨ assoc ⟩
        i ∘ arr ∘ to b   ≈⟨ ⟺ e ⟩
        h                ∎)))
    }
  }
  where
    open Coequalizer coeq
    open HomReasoning
    open MR 𝒞
    
    f' g' : A' ⇒ B'
    f' = from b ∘ f ∘ to a
    g' = from b ∘ g ∘ to a

    equalize'⇒equalize : {C : Obj} {h : B' ⇒ C}
                         (eq : h ∘ f' ≈ h ∘ g')
                       → (h ∘ from b) ∘ f ≈ (h ∘ from b) ∘ g
    equalize'⇒equalize {_} {h} eq = cancel-toʳ a (begin
      ((h ∘ from b) ∘ f) ∘ to a ≈⟨ assoc²αε ⟩
      h ∘ f'                    ≈⟨ eq ⟩
      h ∘ g'                    ≈⟨ assoc²εα ⟩
      ((h ∘ from b) ∘ g) ∘ to a ∎)

    coequalize' : {C : Obj} {h : B' ⇒ C}
                  (eq : h ∘ f' ≈ h ∘ g')
                → obj ⇒ C
    coequalize' eq = coequalize (equalize'⇒equalize eq)


-- coequalizer commutes with coequalizer
module CoequalizerOfCoequalizer
  {A B C D : Obj} {f₁ f₂ : A ⇒ B} {g₁ g₂ : A ⇒ C} {h₁ h₂ : B ⇒ D} {i₁ i₂ : C ⇒ D}
  (coeqᶠ : Coequalizer f₁ f₂) (coeqᵍ : Coequalizer g₁ g₂)
  (coeqʰ : Coequalizer h₁ h₂) (coeqⁱ : Coequalizer i₁ i₂)
  (let open Coequalizer)
  (f⇒i₁ f⇒i₂ : obj coeqᶠ ⇒ obj coeqⁱ)
  (g⇒h₁ g⇒h₂ : obj coeqᵍ ⇒ obj coeqʰ)
  (sq₁ᶠⁱ : CommutativeSquare (arr coeqᶠ) h₁ f⇒i₁ (arr coeqⁱ))
  (sq₂ᶠⁱ : CommutativeSquare (arr coeqᶠ) h₂ f⇒i₂ (arr coeqⁱ))
  (sq₁ᵍʰ : CommutativeSquare i₁ (arr coeqᵍ) (arr coeqʰ) g⇒h₁)
  (sq₂ᵍʰ : CommutativeSquare i₂ (arr coeqᵍ) (arr coeqʰ) g⇒h₂)
  (coeqcoeqᵍʰ : Coequalizer g⇒h₁ g⇒h₂) where

  {-
          f₁₂
       A ====> B ----> coeqᶠ
       ||      ||       ||
    g₁₂||   h₁₂||  sqᶠⁱ ||
       vv i₁₂  vv       vv        t
       C ====> D ----> coeqⁱ ----------
       |       |         |             |
       | sqᵍʰ  |  arrSq  |             |
       v       v         v             v
     coeqᵍ==>coeqʰ --> coeqcoeqᵍʰ ···> T
               .               coequalize
               .                       ^
               .                       .
               .........................
                            u
  -}

  -- We construct a coequalizer of the parallel pair f⇒i₁, f⇒i₂
  -- its components will be called: objᶠⁱ, arrᶠⁱ, ...

  open HomReasoning

  objᶠⁱ : Obj
  objᶠⁱ = obj coeqcoeqᵍʰ

  arrᶠⁱ : obj coeqⁱ ⇒ objᶠⁱ
  arrᶠⁱ = ⇒MapBetweenCoeq (arr coeqᵍ) (arr coeqʰ) (⟺ sq₁ᵍʰ) (⟺ sq₂ᵍʰ) coeqⁱ coeqcoeqᵍʰ

  abstract
    arrSq : arr coeqcoeqᵍʰ ∘ arr coeqʰ ≈ arrᶠⁱ ∘ arr coeqⁱ
    arrSq = ⇒MapBetweenCoeqSq (arr coeqᵍ) (arr coeqʰ) (⟺ sq₁ᵍʰ) (⟺ sq₂ᵍʰ) coeqⁱ coeqcoeqᵍʰ

    equalityᶠⁱ∘arr : (arrᶠⁱ ∘ f⇒i₁) ∘ arr coeqᶠ  ≈ (arrᶠⁱ ∘ f⇒i₂) ∘ arr coeqᶠ
    equalityᶠⁱ∘arr = begin
      (arrᶠⁱ ∘ f⇒i₁) ∘ arr coeqᶠ        ≈⟨ extendˡ sq₁ᶠⁱ ⟩
      (arrᶠⁱ ∘ arr coeqⁱ) ∘ h₁          ≈⟨ ⟺ arrSq ⟩∘⟨refl ⟩
      (arr coeqcoeqᵍʰ ∘ arr coeqʰ) ∘ h₁ ≈⟨ extendˡ (equality coeqʰ) ⟩
      (arr coeqcoeqᵍʰ ∘ arr coeqʰ) ∘ h₂ ≈⟨ arrSq ⟩∘⟨refl ⟩
      (arrᶠⁱ ∘ arr coeqⁱ) ∘ h₂          ≈⟨ extendˡ (⟺ sq₂ᶠⁱ) ⟩
      (arrᶠⁱ ∘ f⇒i₂) ∘ arr coeqᶠ        ∎
      where
        open MR 𝒞

    equalityᶠⁱ : arrᶠⁱ ∘ f⇒i₁ ≈ arrᶠⁱ ∘ f⇒i₂
    equalityᶠⁱ = Coequalizer⇒Epi coeqᶠ (arrᶠⁱ ∘ f⇒i₁) (arrᶠⁱ ∘ f⇒i₂) equalityᶠⁱ∘arr


    commutes : {T : Obj} {t : obj coeqⁱ ⇒ T} (eq : t ∘ f⇒i₁ ≈ t ∘ f⇒i₂)
             → (t ∘ arr coeqⁱ) ∘ h₁ ≈ (t ∘ arr coeqⁱ) ∘ h₂
    commutes {_} {t} eq = begin
      (t ∘ arr coeqⁱ) ∘ h₁   ≈⟨ extendˡ (⟺ sq₁ᶠⁱ) ⟩
      (t ∘ f⇒i₁) ∘ arr coeqᶠ ≈⟨ eq ⟩∘⟨refl ⟩
      (t ∘ f⇒i₂) ∘ arr coeqᶠ ≈⟨ extendˡ sq₂ᶠⁱ ⟩
      (t ∘ arr coeqⁱ) ∘ h₂   ∎
      where
        open MR 𝒞
  
    u : {T : Obj} {t : obj coeqⁱ ⇒ T} (eq : t ∘ f⇒i₁ ≈ t ∘ f⇒i₂)
      → obj coeqʰ ⇒ T
    u eq = coequalize coeqʰ (commutes eq)

    uEqualizes∘arr : {T : Obj} {t : obj coeqⁱ ⇒ T} (eq : t ∘ f⇒i₁ ≈ t ∘ f⇒i₂)
                   → (u eq ∘ g⇒h₁) ∘ arr coeqᵍ ≈ (u eq ∘ g⇒h₂) ∘ arr coeqᵍ
    uEqualizes∘arr {t = t} eq = begin
      (u eq ∘ g⇒h₁) ∘ arr coeqᵍ ≈⟨ extendˡ (⟺ sq₁ᵍʰ) ⟩
      (u eq ∘ arr coeqʰ) ∘ i₁   ≈⟨ ⟺ (universal coeqʰ) ⟩∘⟨refl ⟩
      (t ∘ arr coeqⁱ) ∘ i₁      ≈⟨ extendˡ (equality coeqⁱ) ⟩
      (t ∘ arr coeqⁱ) ∘ i₂      ≈⟨ universal coeqʰ ⟩∘⟨refl ⟩
      (u eq ∘ arr coeqʰ) ∘ i₂   ≈⟨ extendˡ sq₂ᵍʰ ⟩
      (u eq ∘ g⇒h₂) ∘ arr coeqᵍ ∎
      where
        open MR 𝒞

    uEqualizes : {T : Obj} {t : obj coeqⁱ ⇒ T} (eq : t ∘ f⇒i₁ ≈ t ∘ f⇒i₂)
               → u eq ∘ g⇒h₁ ≈ u eq ∘ g⇒h₂
    uEqualizes eq = Coequalizer⇒Epi coeqᵍ (u eq ∘ g⇒h₁) (u eq ∘ g⇒h₂) (uEqualizes∘arr eq)

    coequalizeᶠⁱ : {T : Obj} {t : obj coeqⁱ ⇒ T} → t ∘ f⇒i₁ ≈ t ∘ f⇒i₂ → objᶠⁱ ⇒ T
    coequalizeᶠⁱ eq = coequalize coeqcoeqᵍʰ (uEqualizes eq)

    universalᶠⁱ∘arr : {T : Obj} {t : obj coeqⁱ ⇒ T} {eq : t ∘ f⇒i₁ ≈ t ∘ f⇒i₂}
                    → t ∘ arr coeqⁱ ≈ (coequalizeᶠⁱ eq ∘ arrᶠⁱ) ∘ arr coeqⁱ
    universalᶠⁱ∘arr {t = t} {eq} = begin
      t ∘ arr coeqⁱ                                  ≈⟨ universal coeqʰ ⟩
      u eq ∘ arr coeqʰ                               ≈⟨ universal coeqcoeqᵍʰ ⟩∘⟨refl ⟩
      (coequalizeᶠⁱ eq ∘ arr coeqcoeqᵍʰ) ∘ arr coeqʰ ≈⟨ extendˡ arrSq ⟩
      (coequalizeᶠⁱ eq ∘ arrᶠⁱ) ∘ arr coeqⁱ          ∎
      where
        open MR 𝒞

    universalᶠⁱ : {T : Obj} {t : obj coeqⁱ ⇒ T} {eq : t ∘ f⇒i₁ ≈ t ∘ f⇒i₂}
                → t ≈ coequalizeᶠⁱ eq ∘ arrᶠⁱ
    universalᶠⁱ {t = t} {eq} = Coequalizer⇒Epi coeqⁱ t (coequalizeᶠⁱ eq ∘ arrᶠⁱ) universalᶠⁱ∘arr

    uniqueᶠⁱ∘arr∘arr : {T : Obj} {t : obj coeqⁱ ⇒ T} {i : objᶠⁱ ⇒ T} {eq : t ∘ f⇒i₁ ≈ t ∘ f⇒i₂}
                     → t ≈ i ∘ arrᶠⁱ
                     → (i ∘ arr coeqcoeqᵍʰ) ∘ arr coeqʰ
                     ≈ (coequalizeᶠⁱ eq  ∘ arr coeqcoeqᵍʰ) ∘ arr coeqʰ
    uniqueᶠⁱ∘arr∘arr {t = t} {i} {eq} factors = begin
      (i ∘ arr coeqcoeqᵍʰ) ∘ arr coeqʰ                ≈⟨ extendˡ arrSq ⟩
      (i ∘ arrᶠⁱ) ∘ arr coeqⁱ                         ≈⟨ ⟺ factors ⟩∘⟨refl ⟩
      t ∘ arr coeqⁱ                                   ≈⟨ universalᶠⁱ ⟩∘⟨refl ⟩
      (coequalizeᶠⁱ eq ∘ arrᶠⁱ) ∘ arr coeqⁱ           ≈⟨ extendˡ (⟺ arrSq) ⟩
      (coequalizeᶠⁱ eq  ∘ arr coeqcoeqᵍʰ) ∘ arr coeqʰ ∎
      where
        open MR 𝒞

    uniqueᶠⁱ : {T : Obj} {t : obj coeqⁱ ⇒ T} {i : objᶠⁱ ⇒ T} {eq : t ∘ f⇒i₁ ≈ t ∘ f⇒i₂}
             → t ≈ i ∘ arrᶠⁱ
             → i ≈ coequalizeᶠⁱ eq
    uniqueᶠⁱ {i = i} {eq} factors = Coequalizer⇒Epi coeqcoeqᵍʰ i (coequalizeᶠⁱ eq) (
                                          Coequalizer⇒Epi coeqʰ
                                          (i ∘ arr coeqcoeqᵍʰ)
                                          (coequalizeᶠⁱ eq  ∘ arr coeqcoeqᵍʰ)
                                          (uniqueᶠⁱ∘arr∘arr factors)
                                        )
  -- end abstract --

  coeqcoeqᶠⁱ : Coequalizer f⇒i₁ f⇒i₂
  coeqcoeqᶠⁱ = record
    { obj = objᶠⁱ
    ; arr = arrᶠⁱ
    ; isCoequalizer = record
      { equality = equalityᶠⁱ
      ; coequalize = coequalizeᶠⁱ
      ; universal = universalᶠⁱ
      ; unique = uniqueᶠⁱ
      }
    }

  CoeqsAreIsomorphic : (coeq : Coequalizer f⇒i₁ f⇒i₂) → obj coeq ≅ obj coeqcoeqᵍʰ
  CoeqsAreIsomorphic coeq = up-to-iso coeq coeqcoeqᶠⁱ

  -- The Isomorphism of coequalizers fits into a commutative pentagon --
  -- We need this for proving some coherences in the bicategory of monads and bimodules --
  IsoFitsInPentagon : (coeq : Coequalizer f⇒i₁ f⇒i₂)
                    → arr coeqcoeqᵍʰ ∘ arr coeqʰ
                      ≈ from (CoeqsAreIsomorphic coeq) ∘ arr coeq  ∘ arr coeqⁱ
  IsoFitsInPentagon coeq = begin
    arr coeqcoeqᵍʰ ∘ arr coeqʰ                               ≈⟨ arrSq ⟩
    arrᶠⁱ ∘ arr coeqⁱ                                        ≈⟨ universal coeq ⟩∘⟨refl ⟩
    (from (CoeqsAreIsomorphic coeq) ∘ arr coeq) ∘ arr coeqⁱ  ≈⟨ assoc ⟩
    from (CoeqsAreIsomorphic coeq) ∘ arr coeq ∘ arr coeqⁱ    ∎

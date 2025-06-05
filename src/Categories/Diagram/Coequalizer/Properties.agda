{-# OPTIONS --without-K --safe #-}

open import Categories.Category

-- we use duality to prove properties about coequalizer
module Categories.Diagram.Coequalizer.Properties {o ℓ e} (C : Category o ℓ e) where

open Category C

open import Categories.Diagram.Coequalizer C using (Coequalizer; IsCoequalizer; Coequalizer⇒Epi; up-to-iso)
open import Categories.Morphism C using (_RetractOf_; _≅_)
import Categories.Morphism.Reasoning as MR
open import Categories.Diagram.Equalizer op using (Equalizer)
open import Categories.Diagram.Equalizer.Properties op using (section-equalizer)
open import Categories.Diagram.Duality C using (Coequalizer⇒coEqualizer; IscoEqualizer⇒IsCoequalizer)
open import Categories.Diagram.KernelPair C using (KernelPair)
open import Categories.Diagram.Pullback C using (Pullback; IsPullback)
open import Categories.Morphism.Regular C using (RegularEpi)


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
        open Category.HomReasoning C
        open MR C

retract-coequalizer : ∀ {X Y} {f : Y ⇒ X} {g : X ⇒ Y} → f RetractOf g → IsCoequalizer (g ∘ f) id f
retract-coequalizer f∘g≈id = IscoEqualizer⇒IsCoequalizer (section-equalizer f∘g≈id)

-- split coequalizer are coequalizer --
splitCoequalizer⇒Coequalizer : {A B C : Obj} {f g : A ⇒ B} {e : B ⇒ C}
                               (t : B ⇒ A) (s : C ⇒ B)
                               (eq : e ∘ f ≈ e ∘ g)
                               (tisSection : f ∘ t ≈ id)
                               (sisSection : e ∘ s ≈ id)
                               (sq : s ∘ e ≈ g ∘ t)
                               → IsCoequalizer f g e
splitCoequalizer⇒Coequalizer {f = f} {g} {e} t s eq tisSection sisSection sq = record
  { equality = eq
  ; coequalize = λ {T} {h} _ → h ∘ s
  ; universal = λ {T} {h} {h∘f≈h∘g} → begin
    h           ≈⟨ introʳ tisSection ⟩
    h ∘ f ∘ t   ≈⟨ extendʳ h∘f≈h∘g ⟩
    h ∘ g ∘ t   ≈⟨ pushʳ (⟺ sq) ⟩
    (h ∘ s) ∘ e ∎
  ; unique = λ {C} {h} {i} {h∘f≈h∘g} h≈i∘e → begin
    i ≈⟨ introʳ sisSection ⟩
    i ∘ e ∘ s ≈⟨ pullˡ (⟺ h≈i∘e) ⟩
    h ∘ s ∎
  }
  where
    open HomReasoning
    open MR C

splitCoequalizer⇒Coequalizer-sym : {A B C : Obj} {f g : A ⇒ B} {e : B ⇒ C}
                               (t : B ⇒ A) (s : C ⇒ B)
                               (eq : e ∘ f ≈ e ∘ g)
                               (tisSection : g ∘ t ≈ id)
                               (sisSection : e ∘ s ≈ id)
                               (sq : s ∘ e ≈ f ∘ t)
                               → IsCoequalizer f g e
splitCoequalizer⇒Coequalizer-sym {f = f} {g} {e} t s eq tisSection sisSection sq = record
  { equality = eq
  ; coequalize = λ {T} {h} _ → h ∘ s
  ; universal = λ {T} {h} {h∘f≈h∘g} → begin
    h           ≈⟨ introʳ tisSection ⟩
    h ∘ g ∘ t   ≈⟨ extendʳ (⟺ h∘f≈h∘g) ⟩
    h ∘ f ∘ t   ≈⟨ pushʳ (⟺ sq) ⟩
    (h ∘ s) ∘ e ∎
  ; unique = λ {C} {h} {i} {h∘f≈h∘g} h≈i∘e → begin
    i ≈⟨ introʳ sisSection ⟩
    i ∘ e ∘ s ≈⟨ pullˡ (⟺ h≈i∘e) ⟩
    h ∘ s ∎
  }
  where
    open HomReasoning
    open MR C


open Categories.Category.Definitions C

module MapBetweenCoequalizers where

  ⇒coequalize : {A₁ B₁ A₂ B₂ : Obj}
              → {f₁ g₁ : A₁ ⇒ B₁} → {f₂ g₂ : A₂ ⇒ B₂}
              → (α : A₁ ⇒ A₂) → (β : B₁ ⇒ B₂)
              → CommutativeSquare α f₁ f₂ β                -- f₂ ∘ α ≈ β ∘ f₁
              → CommutativeSquare α g₁ g₂ β                -- g₂ ∘ α ≈ β ∘ g₁
              → (coeq₂ : Coequalizer f₂ g₂)
              → (Coequalizer.arr coeq₂ ∘ β) ∘ f₁ ≈ (Coequalizer.arr coeq₂ ∘ β) ∘ g₁
  ⇒coequalize {A₁} {B₁} {A₂} {B₂} {f₁} {g₁} {f₂} {g₂} α β sq₁ sq₂ coeq₂ = begin
    (Coequalizer.arr coeq₂ ∘ β) ∘ f₁ ≈⟨ extendˡ (⟺ sq₁) ⟩
    (Coequalizer.arr coeq₂ ∘ f₂) ∘ α ≈⟨ equality₂ ⟩∘⟨refl ⟩
    (Coequalizer.arr coeq₂ ∘ g₂) ∘ α ≈⟨ extendˡ sq₂ ⟩
    (Coequalizer.arr coeq₂ ∘ β) ∘ g₁ ∎
    where
      open HomReasoning
      open MR C
      open Coequalizer coeq₂
      open IsCoequalizer isCoequalizer renaming (equality to equality₂)

  ⇒MapBetweenCoeq : {A₁ B₁ A₂ B₂ : Obj}
                  → {f₁ g₁ : A₁ ⇒ B₁}
                  → {f₂ g₂ : A₂ ⇒ B₂}
                  → (α : A₁ ⇒ A₂)
                  → (β : B₁ ⇒ B₂)
                  → CommutativeSquare α f₁ f₂ β                -- f₂ ∘ α ≈ β ∘ f₁
                  → CommutativeSquare α g₁ g₂ β                -- g₂ ∘ α ≈ β ∘ g₁
                  → (coeq₁ : Coequalizer f₁ g₁)
                  → (coeq₂ : Coequalizer f₂ g₂)
                  → Coequalizer.obj coeq₁ ⇒ Coequalizer.obj coeq₂
  ⇒MapBetweenCoeq α β sq₁ sq₂ coeq₁ coeq₂ = coequalize₁ (⇒coequalize α β sq₁ sq₂ coeq₂)
    where
      open Coequalizer coeq₁ renaming (isCoequalizer to isCoequalizer₁)
      open IsCoequalizer isCoequalizer₁ renaming (coequalize to coequalize₁)
      open Category.HomReasoning C

  ⇒MapBetweenCoeqSq : {A₁ B₁ A₂ B₂ : Obj}
                  → {f₁ g₁ : A₁ ⇒ B₁}
                  → {f₂ g₂ : A₂ ⇒ B₂}
                  → (α : A₁ ⇒ A₂)
                  → (β : B₁ ⇒ B₂)
                  → (sq₁ : CommutativeSquare α f₁ f₂ β)               -- f₂ ∘ α ≈ β ∘ f₁
                  → (sq₂ : CommutativeSquare α g₁ g₂ β)               -- g₂ ∘ α ≈ β ∘ g₁
                  → (coeq₁ : Coequalizer f₁ g₁)
                  → (coeq₂ : Coequalizer f₂ g₂)
                  → CommutativeSquare
                      β (Coequalizer.arr coeq₁)
                      (Coequalizer.arr coeq₂) (⇒MapBetweenCoeq α β sq₁ sq₂ coeq₁ coeq₂)
  ⇒MapBetweenCoeqSq α β sq₁ sq₂ coeq₁ coeq₂ = universal₁
    where
      open Coequalizer coeq₁ renaming (isCoequalizer to isCoequalizer₁)
      open IsCoequalizer isCoequalizer₁ renaming (universal to universal₁)

open MapBetweenCoequalizers public

CoeqOfIsomorphicDiagram : {A B : Obj} {f g : A ⇒ B} (coeq : Coequalizer f g )
                        → {A' B' : Obj}
                        → (a : A ≅ A') (b : B ≅ B')
                        → Coequalizer (_≅_.from b ∘ f ∘ _≅_.to a) (_≅_.from b ∘ g ∘ _≅_.to a)
CoeqOfIsomorphicDiagram {A} {B} {f} {g} coeq {A'} {B'} a b = record
  { arr = arr ∘ _≅_.to b
  ; isCoequalizer = record
    { equality = begin
        (arr ∘ _≅_.to b) ∘ _≅_.from b ∘ f ∘ _≅_.to a ≈⟨ sym-assoc ⟩
        ((arr ∘ _≅_.to b) ∘ _≅_.from b) ∘ f ∘ _≅_.to a ≈⟨ assoc ⟩∘⟨refl ⟩
        (arr ∘ _≅_.to b ∘ _≅_.from b) ∘ f ∘ _≅_.to a ≈⟨ elimʳ (_≅_.isoˡ b) ⟩∘⟨refl ⟩
        arr ∘ f ∘ _≅_.to a ≈⟨ extendʳ equality ⟩
        arr ∘ g ∘ _≅_.to a ≈⟨ introʳ (_≅_.isoˡ b) ⟩∘⟨refl ⟩
        (arr ∘ _≅_.to b ∘ _≅_.from b) ∘ g ∘ _≅_.to a ≈⟨ sym-assoc ⟩∘⟨refl ⟩
        ((arr ∘ _≅_.to b) ∘ _≅_.from b) ∘ g ∘ _≅_.to a ≈⟨ assoc ⟩
        (arr ∘ _≅_.to b) ∘ _≅_.from b ∘ g ∘ _≅_.to a ∎
    ; coequalize = coequalize'
    ; universal =  λ {C} {h} {eq} → begin
        h ≈⟨ switch-fromtoʳ b universal ⟩
        (coequalize' eq ∘ arr) ∘ _≅_.to b ≈⟨ assoc ⟩
        coequalize' eq ∘ (arr ∘ _≅_.to b) ∎
    ; unique = λ {C} {h} {i} {eq} e → unique (⟺ (switch-tofromʳ b (begin
        (i ∘ arr) ∘ _≅_.to b ≈⟨ assoc ⟩
        i ∘ arr ∘ _≅_.to b ≈⟨ ⟺ e ⟩
        h ∎)))
    }
  }
  where
    open Coequalizer coeq
    open HomReasoning
    open MR C
    
    f' g' : A' ⇒ B'
    f' = _≅_.from b ∘ f ∘ _≅_.to a
    g' = _≅_.from b ∘ g ∘ _≅_.to a

    equalize'⇒equalize : {C : Obj} {h : B' ⇒ C}
                         (eq : h ∘ f' ≈ h ∘ g')
                       → (h ∘ _≅_.from b) ∘ f ≈ (h ∘ _≅_.from b) ∘ g
    equalize'⇒equalize {C} {h} eq = cancel-toʳ a (begin
      ((h ∘ _≅_.from b) ∘ f) ∘ _≅_.to a ≈⟨ assoc ⟩
      (h ∘ _≅_.from b) ∘ f ∘ _≅_.to a ≈⟨ assoc ⟩
      h ∘ f' ≈⟨ eq ⟩
      h ∘ g' ≈⟨ sym-assoc ⟩
      (h ∘ _≅_.from b) ∘ g ∘ _≅_.to a ≈⟨ sym-assoc ⟩
      ((h ∘ _≅_.from b) ∘ g) ∘ _≅_.to a ∎)

    coequalize' : {C : Obj} {h : B' ⇒ C}
                  (eq : h ∘ _≅_.from b ∘ f ∘ _≅_.to a ≈ h ∘ _≅_.from b ∘ g ∘ _≅_.to a)
                  → obj ⇒ C
    coequalize' {C} {h} eq = coequalize (equalize'⇒equalize eq)


-- coequalizer commutes with coequalizer
module CoequalizerOfCoequalizer
  {A B C D : Obj} {f₁ f₂ : A ⇒ B} {g₁ g₂ : A ⇒ C} {h₁ h₂ : B ⇒ D} {i₁ i₂ : C ⇒ D}
  (coeqᶠ : Coequalizer f₁ f₂) (coeqᵍ : Coequalizer g₁ g₂)
  (coeqʰ : Coequalizer h₁ h₂) (coeqⁱ : Coequalizer i₁ i₂)
  (f⇒i₁ f⇒i₂ : Coequalizer.obj coeqᶠ ⇒ Coequalizer.obj coeqⁱ)
  (g⇒h₁ g⇒h₂ : Coequalizer.obj coeqᵍ ⇒ Coequalizer.obj coeqʰ)
  (sq₁ᶠⁱ : CommutativeSquare (Coequalizer.arr coeqᶠ) h₁ f⇒i₁ (Coequalizer.arr coeqⁱ))
  (sq₂ᶠⁱ : CommutativeSquare (Coequalizer.arr coeqᶠ) h₂ f⇒i₂ (Coequalizer.arr coeqⁱ))
  (sq₁ᵍʰ : CommutativeSquare i₁ (Coequalizer.arr coeqᵍ) (Coequalizer.arr coeqʰ) g⇒h₁)
  (sq₂ᵍʰ : CommutativeSquare i₂ (Coequalizer.arr coeqᵍ) (Coequalizer.arr coeqʰ) g⇒h₂)
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

  open HomReasoning

  obj : Obj
  obj = Coequalizer.obj coeqcoeqᵍʰ

  arr : Coequalizer.obj coeqⁱ ⇒ obj
  arr = ⇒MapBetweenCoeq (Coequalizer.arr coeqᵍ) (Coequalizer.arr coeqʰ)
                        (⟺ sq₁ᵍʰ) (⟺ sq₂ᵍʰ) coeqⁱ coeqcoeqᵍʰ

  abstract
    arrSq : Coequalizer.arr coeqcoeqᵍʰ ∘ Coequalizer.arr coeqʰ
            ≈ arr ∘ Coequalizer.arr coeqⁱ
    arrSq = ⇒MapBetweenCoeqSq (Coequalizer.arr coeqᵍ) (Coequalizer.arr coeqʰ)
                              (⟺ sq₁ᵍʰ) (⟺ sq₂ᵍʰ) coeqⁱ coeqcoeqᵍʰ

    equality∘arr : (arr ∘ f⇒i₁) ∘ Coequalizer.arr coeqᶠ  ≈ (arr ∘ f⇒i₂) ∘ Coequalizer.arr coeqᶠ
    equality∘arr = begin
      (arr ∘ f⇒i₁) ∘ Coequalizer.arr coeqᶠ ≈⟨ assoc ⟩
      arr ∘ f⇒i₁ ∘ Coequalizer.arr coeqᶠ ≈⟨ refl⟩∘⟨ sq₁ᶠⁱ ⟩
      arr ∘ Coequalizer.arr coeqⁱ ∘ h₁ ≈⟨ ⟺ assoc ⟩
      (arr ∘ Coequalizer.arr coeqⁱ) ∘ h₁ ≈⟨ ⟺ arrSq ⟩∘⟨refl ⟩
      (Coequalizer.arr coeqcoeqᵍʰ ∘ Coequalizer.arr coeqʰ) ∘ h₁ ≈⟨ assoc ⟩
      Coequalizer.arr coeqcoeqᵍʰ ∘ Coequalizer.arr coeqʰ ∘ h₁ ≈⟨ refl⟩∘⟨ Coequalizer.equality coeqʰ ⟩
      Coequalizer.arr coeqcoeqᵍʰ ∘ Coequalizer.arr coeqʰ ∘ h₂ ≈⟨ ⟺ assoc ⟩
      (Coequalizer.arr coeqcoeqᵍʰ ∘ Coequalizer.arr coeqʰ) ∘ h₂ ≈⟨ arrSq ⟩∘⟨refl ⟩
      (arr ∘ Coequalizer.arr coeqⁱ) ∘ h₂ ≈⟨ assoc ⟩
      arr ∘ Coequalizer.arr coeqⁱ ∘ h₂ ≈⟨ refl⟩∘⟨ ⟺ sq₂ᶠⁱ ⟩
      arr ∘ f⇒i₂ ∘ Coequalizer.arr coeqᶠ ≈⟨ ⟺ assoc ⟩
      (arr ∘ f⇒i₂) ∘ Coequalizer.arr coeqᶠ ∎

    equality : arr ∘ f⇒i₁ ≈ arr ∘ f⇒i₂
    equality = Coequalizer⇒Epi coeqᶠ (arr ∘ f⇒i₁) (arr ∘ f⇒i₂) equality∘arr


    commutes : {T : Obj} {t : Coequalizer.obj coeqⁱ ⇒ T} (eq : t ∘ f⇒i₁ ≈ t ∘ f⇒i₂)
               → (t ∘ Coequalizer.arr coeqⁱ) ∘ h₁ ≈ (t ∘ Coequalizer.arr coeqⁱ) ∘ h₂
    commutes {T} {t} eq = begin
      (t ∘ Coequalizer.arr coeqⁱ) ∘ h₁ ≈⟨ assoc ⟩
      t ∘ Coequalizer.arr coeqⁱ ∘ h₁ ≈⟨ refl⟩∘⟨ ⟺ sq₁ᶠⁱ ⟩
      t ∘ f⇒i₁ ∘ Coequalizer.arr coeqᶠ ≈⟨ ⟺ assoc ⟩
      (t ∘ f⇒i₁) ∘ Coequalizer.arr coeqᶠ ≈⟨ eq ⟩∘⟨refl ⟩
      (t ∘ f⇒i₂) ∘ Coequalizer.arr coeqᶠ ≈⟨ assoc ⟩
      t ∘ f⇒i₂ ∘ Coequalizer.arr coeqᶠ ≈⟨ refl⟩∘⟨ sq₂ᶠⁱ ⟩
      t ∘ Coequalizer.arr coeqⁱ ∘ h₂ ≈⟨ ⟺ assoc ⟩
      (t ∘ Coequalizer.arr coeqⁱ) ∘ h₂ ∎
  
    u : {T : Obj} {t : Coequalizer.obj coeqⁱ ⇒ T} (eq : t ∘ f⇒i₁ ≈ t ∘ f⇒i₂)
        → Coequalizer.obj coeqʰ ⇒ T
    u {T} {t} eq = Coequalizer.coequalize coeqʰ {h = t ∘ Coequalizer.arr coeqⁱ} (commutes eq)

    uEqualizes∘arr : {T : Obj} {t : Coequalizer.obj coeqⁱ ⇒ T} (eq : t ∘ f⇒i₁ ≈ t ∘ f⇒i₂)
                     → (u eq ∘ g⇒h₁) ∘ Coequalizer.arr coeqᵍ ≈ (u eq ∘ g⇒h₂) ∘ Coequalizer.arr coeqᵍ
    uEqualizes∘arr {T} {t} eq = begin
      (u eq ∘ g⇒h₁) ∘ Coequalizer.arr coeqᵍ ≈⟨ assoc ⟩
      u eq ∘ g⇒h₁ ∘ Coequalizer.arr coeqᵍ ≈⟨ refl⟩∘⟨ ⟺ sq₁ᵍʰ ⟩
      u eq ∘ Coequalizer.arr coeqʰ ∘ i₁ ≈⟨ sym-assoc ⟩
      (u eq ∘ Coequalizer.arr coeqʰ) ∘ i₁ ≈⟨ ⟺ (Coequalizer.universal coeqʰ) ⟩∘⟨refl ⟩
      (t ∘ Coequalizer.arr coeqⁱ) ∘ i₁ ≈⟨ assoc ⟩
      t ∘ Coequalizer.arr coeqⁱ ∘ i₁ ≈⟨ refl⟩∘⟨ Coequalizer.equality coeqⁱ ⟩
      t ∘ Coequalizer.arr coeqⁱ ∘ i₂ ≈⟨ ⟺ assoc ⟩
      (t ∘ Coequalizer.arr coeqⁱ) ∘ i₂ ≈⟨ Coequalizer.universal coeqʰ ⟩∘⟨refl ⟩
      (u eq ∘ Coequalizer.arr coeqʰ) ∘ i₂ ≈⟨ assoc ⟩
      u eq ∘ Coequalizer.arr coeqʰ ∘ i₂ ≈⟨ refl⟩∘⟨ sq₂ᵍʰ ⟩
      u eq ∘ g⇒h₂ ∘ Coequalizer.arr coeqᵍ ≈⟨ ⟺ assoc ⟩
      (u eq ∘ g⇒h₂) ∘ Coequalizer.arr coeqᵍ ∎

    uEqualizes : {T : Obj} {t : Coequalizer.obj coeqⁱ ⇒ T} (eq : t ∘ f⇒i₁ ≈ t ∘ f⇒i₂) → u eq ∘ g⇒h₁ ≈ u eq ∘ g⇒h₂
    uEqualizes {T} {t} eq = Coequalizer⇒Epi coeqᵍ (u eq ∘ g⇒h₁) (u eq ∘ g⇒h₂) (uEqualizes∘arr eq)

    coequalize : {T : Obj} {t : Coequalizer.obj coeqⁱ ⇒ T} → t ∘ f⇒i₁ ≈ t ∘ f⇒i₂ → obj ⇒ T
    coequalize {T} {t} eq = Coequalizer.coequalize coeqcoeqᵍʰ {h = u eq} (uEqualizes eq)

    universal∘arr : {T : Obj} {t : Coequalizer.obj coeqⁱ ⇒ T} {eq : t ∘ f⇒i₁ ≈ t ∘ f⇒i₂}
                → t ∘ Coequalizer.arr coeqⁱ ≈ (coequalize eq ∘ arr) ∘ Coequalizer.arr coeqⁱ
    universal∘arr {T} {t} {eq} = begin
      t ∘ Coequalizer.arr coeqⁱ ≈⟨ Coequalizer.universal coeqʰ ⟩
      u eq ∘ Coequalizer.arr coeqʰ ≈⟨ Coequalizer.universal coeqcoeqᵍʰ ⟩∘⟨refl ⟩
      (coequalize eq ∘ Coequalizer.arr coeqcoeqᵍʰ) ∘ Coequalizer.arr coeqʰ ≈⟨ assoc ⟩
      coequalize eq ∘ Coequalizer.arr coeqcoeqᵍʰ ∘ Coequalizer.arr coeqʰ ≈⟨ refl⟩∘⟨ arrSq ⟩
      coequalize eq ∘ arr ∘ Coequalizer.arr coeqⁱ ≈⟨ ⟺ assoc ⟩
      (coequalize eq ∘ arr) ∘ Coequalizer.arr coeqⁱ ∎

    universal : {T : Obj} {t : Coequalizer.obj coeqⁱ ⇒ T} {eq : t ∘ f⇒i₁ ≈ t ∘ f⇒i₂}
                → t ≈ coequalize eq ∘ arr
    universal {T} {t} {eq} = Coequalizer⇒Epi coeqⁱ t (coequalize eq ∘ arr) universal∘arr

    unique∘arr∘arr : {T : Obj} {t : Coequalizer.obj coeqⁱ ⇒ T} {i : obj ⇒ T} {eq : t ∘ f⇒i₁ ≈ t ∘ f⇒i₂}
                     → t ≈ i ∘ arr
                     → (i ∘ Coequalizer.arr coeqcoeqᵍʰ) ∘ Coequalizer.arr coeqʰ
                       ≈ (coequalize eq  ∘ Coequalizer.arr coeqcoeqᵍʰ) ∘ Coequalizer.arr coeqʰ
    unique∘arr∘arr {T} {t} {i} {eq} factors = begin
      (i ∘ Coequalizer.arr coeqcoeqᵍʰ) ∘ Coequalizer.arr coeqʰ ≈⟨ assoc ⟩
      i ∘ Coequalizer.arr coeqcoeqᵍʰ ∘ Coequalizer.arr coeqʰ ≈⟨ refl⟩∘⟨ arrSq ⟩
      i ∘ arr ∘ Coequalizer.arr coeqⁱ ≈⟨ ⟺ assoc ⟩
      (i ∘ arr) ∘ Coequalizer.arr coeqⁱ ≈⟨ ⟺ factors ⟩∘⟨refl ⟩
      t ∘ Coequalizer.arr coeqⁱ ≈⟨ universal ⟩∘⟨refl ⟩
      (coequalize eq ∘ arr) ∘ Coequalizer.arr coeqⁱ ≈⟨ assoc ⟩
      coequalize eq ∘ arr ∘ Coequalizer.arr coeqⁱ ≈⟨ refl⟩∘⟨ ⟺ arrSq ⟩
      coequalize eq ∘ Coequalizer.arr coeqcoeqᵍʰ ∘ Coequalizer.arr coeqʰ ≈⟨ ⟺ assoc ⟩
      (coequalize eq  ∘ Coequalizer.arr coeqcoeqᵍʰ) ∘ Coequalizer.arr coeqʰ ∎

    unique : {T : Obj} {t : Coequalizer.obj coeqⁱ ⇒ T} {i : obj ⇒ T} {eq : t ∘ f⇒i₁ ≈ t ∘ f⇒i₂}
             → t ≈ i ∘ arr → i ≈ coequalize eq
    unique {T} {t} {i} {eq} factors = Coequalizer⇒Epi coeqcoeqᵍʰ i (coequalize eq) (
                                        Coequalizer⇒Epi coeqʰ
                                        (i ∘ Coequalizer.arr coeqcoeqᵍʰ)
                                        (coequalize eq  ∘ Coequalizer.arr coeqcoeqᵍʰ)
                                        (unique∘arr∘arr factors)
                                      )
  -- end abstract --

  coeqcoeqᶠⁱ : Coequalizer f⇒i₁ f⇒i₂
  coeqcoeqᶠⁱ = record
    { obj = obj
    ; arr = arr
    ; isCoequalizer = record
      { equality = equality
      ; coequalize = coequalize
      ; universal = universal
      ; unique = unique
      }
    }

  CoeqsAreIsomorphic : (coeq : Coequalizer f⇒i₁ f⇒i₂) → Coequalizer.obj coeq ≅ Coequalizer.obj coeqcoeqᵍʰ
  CoeqsAreIsomorphic coeq = up-to-iso coeq coeqcoeqᶠⁱ

  -- The Isomorphism of coequalizers fits into a commutative pentagon --
  -- We need this for proving some coherences in the bicategory of monads and bimodules --
  IsoFitsInPentagon : (coeq : Coequalizer f⇒i₁ f⇒i₂)
                      → Coequalizer.arr coeqcoeqᵍʰ ∘ Coequalizer.arr coeqʰ ≈
                        _≅_.from (CoeqsAreIsomorphic coeq) ∘ Coequalizer.arr coeq  ∘ Coequalizer.arr coeqⁱ 
  IsoFitsInPentagon coeq = begin
    Coequalizer.arr coeqcoeqᵍʰ ∘ Coequalizer.arr coeqʰ ≈⟨ arrSq ⟩
    arr ∘ Coequalizer.arr coeqⁱ                        ≈⟨ (Coequalizer.universal coeq ⟩∘⟨refl) ⟩
    (_≅_.from (CoeqsAreIsomorphic coeq)
      ∘ Coequalizer.arr coeq) ∘ Coequalizer.arr coeqⁱ  ≈⟨ assoc ⟩
    _≅_.from (CoeqsAreIsomorphic coeq)
      ∘ Coequalizer.arr coeq ∘ Coequalizer.arr coeqⁱ  ∎

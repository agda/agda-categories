{-# OPTIONS --without-K --safe #-}

open import Categories.Category

-- we use duality to prove properties about coequalizer
module Categories.Diagram.Coequalizer.Properties {o ℓ e} (C : Category o ℓ e) where

open Category C

open import Categories.Diagram.Coequalizer C using (Coequalizer; IsCoequalizer; Coequalizer⇒Epi; up-to-iso)
open import Categories.Morphism C
import Categories.Morphism.Reasoning as MR
open import Categories.Diagram.Equalizer op hiding (up-to-iso)
open import Categories.Diagram.Equalizer.Properties op
open import Categories.Diagram.Duality C
open import Categories.Diagram.KernelPair C
open import Categories.Diagram.Pullback C hiding (up-to-iso)
open import Categories.Morphism.Regular C


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
    h           ≈⟨ ⟺ identityʳ ⟩
    h ∘ id      ≈⟨ refl⟩∘⟨ ⟺ tisSection ⟩
    h ∘ f ∘ t   ≈⟨ sym-assoc ⟩
    (h ∘ f) ∘ t ≈⟨ h∘f≈h∘g ⟩∘⟨refl ⟩
    (h ∘ g) ∘ t ≈⟨ assoc ⟩
    h ∘ g ∘ t   ≈⟨ refl⟩∘⟨ ⟺ sq ⟩
    h ∘ s ∘ e   ≈⟨ sym-assoc ⟩
    (h ∘ s) ∘ e ∎
  ; unique = λ {C} {h} {i} {h∘f≈h∘g} h≈i∘e → begin
    i ≈⟨ ⟺ identityʳ ⟩
    i ∘ id ≈⟨ refl⟩∘⟨ ⟺ sisSection ⟩
    i ∘ e ∘ s ≈⟨ sym-assoc ⟩
    (i ∘ e) ∘ s ≈⟨ ⟺ h≈i∘e ⟩∘⟨refl ⟩
    h ∘ s ∎
  }
  where
    open HomReasoning

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
    h           ≈⟨ ⟺ identityʳ ⟩
    h ∘ id      ≈⟨ refl⟩∘⟨ ⟺ tisSection ⟩
    h ∘ g ∘ t   ≈⟨ sym-assoc ⟩
    (h ∘ g) ∘ t ≈⟨ ⟺ h∘f≈h∘g ⟩∘⟨refl ⟩
    (h ∘ f) ∘ t ≈⟨ assoc ⟩
    h ∘ f ∘ t   ≈⟨ refl⟩∘⟨ ⟺ sq ⟩
    h ∘ s ∘ e   ≈⟨ sym-assoc ⟩
    (h ∘ s) ∘ e ∎
  ; unique = λ {C} {h} {i} {h∘f≈h∘g} h≈i∘e → begin
    i ≈⟨ ⟺ identityʳ ⟩
    i ∘ id ≈⟨ refl⟩∘⟨ ⟺ sisSection ⟩
    i ∘ e ∘ s ≈⟨ sym-assoc ⟩
    (i ∘ e) ∘ s ≈⟨ ⟺ h≈i∘e ⟩∘⟨refl ⟩
    h ∘ s ∎
  }
  where
    open HomReasoning


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
    (Coequalizer.arr coeq₂ ∘ β) ∘ f₁ ≈⟨ assoc ⟩
    Coequalizer.arr coeq₂ ∘ (β ∘ f₁) ≈⟨ refl⟩∘⟨ ⟺ sq₁ ⟩
    Coequalizer.arr coeq₂ ∘ (f₂ ∘ α) ≈⟨ ⟺ assoc ⟩
    (Coequalizer.arr coeq₂ ∘ f₂) ∘ α ≈⟨ equality₂ ⟩∘⟨refl ⟩
    (Coequalizer.arr coeq₂ ∘ g₂) ∘ α ≈⟨ assoc ⟩
    Coequalizer.arr coeq₂ ∘ (g₂ ∘ α) ≈⟨ refl⟩∘⟨ sq₂ ⟩
    Coequalizer.arr coeq₂ ∘ (β ∘ g₁) ≈⟨ ⟺ assoc ⟩
    (Coequalizer.arr coeq₂ ∘ β) ∘ g₁ ∎
    where
      open HomReasoning
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
        (arr ∘ _≅_.to b ∘ _≅_.from b) ∘ f ∘ _≅_.to a ≈⟨ (refl⟩∘⟨ _≅_.isoˡ b) ⟩∘⟨refl ⟩
        (arr ∘ id) ∘ f ∘ _≅_.to a ≈⟨ identityʳ ⟩∘⟨refl ⟩
        arr ∘ f ∘ _≅_.to a ≈⟨ sym-assoc ⟩
        (arr ∘ f) ∘ _≅_.to a ≈⟨ equality ⟩∘⟨refl ⟩
        (arr ∘ g) ∘ _≅_.to a ≈⟨ assoc ⟩
        arr ∘ g ∘ _≅_.to a ≈⟨ ⟺ identityʳ ⟩∘⟨refl ⟩
        (arr ∘ id) ∘ g ∘ _≅_.to a ≈⟨ (refl⟩∘⟨ ⟺ (_≅_.isoˡ b)) ⟩∘⟨refl ⟩
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
    open MR C using (switch-fromtoʳ; switch-tofromʳ; cancel-toʳ)
    
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

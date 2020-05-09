{-# OPTIONS --without-K --safe #-}
module Categories.Category.Construction.Grothendieck where

-- The construction of a 1-Category from a (contravariant)
-- pseudofunctor into Cats (as a bicategory)

open import Level
open import Data.Product using (Σ; _,_; proj₁)
open import Data.Unit using (tt)
open import Function.Base using (_$_)
open import Relation.Binary.Structures using (IsEquivalence)

open import Categories.Category using (Category; _[_,_]; _[_≈_])
open import Categories.Bicategory using (Bicategory)
open import Categories.Bicategory.Instance.Cats
open import Categories.Bicategory.Construction.1-Category
open import Categories.Functor renaming (id to idF)
open import Categories.Morphism using (Iso)
import Categories.Morphism.Reasoning as MR
open import Categories.Pseudofunctor
open import Categories.NaturalTransformation hiding (id)

private
  variable
    o ℓ e o′ ℓ′ e′ : Level

module _ {C : Category o ℓ e} {b : Level}
         (P : Pseudofunctor (1-Category b (Category.op C)) (Cats o′ ℓ′ e′)) where

  open Pseudofunctor P
    using (P₀; unitaryʳ; unitaryˡ; module unitˡ; module Hom)
    renaming (P₁ to PF; assoc to P-assoc)
  open Functor using () renaming (F₀ to _$₀_; F₁ to _$₁_)
  open NaturalTransformation

  private
    infix  4 _≈_ _⇒_
    infixr 9 _∘_

    module C = Category C
    module _ {x y} where
      open Functor (PF {x} {y}) public
        renaming (F₀ to P₁; F₁ to P₂; F-resp-≈ to P-resp-≈)

    open Functor

    module _ {x y : C.Obj} {f g : C [ x , y ]} where
      open Category (P₀ x)
      open HomReasoning hiding (⟺; _○_)
      open C.HomReasoning using (⟺; _○_)

      -- A helper lemma.

      P-resp-Iso : (eq : C [ f ≈ g ]) {a : Category.Obj (P₀ y)} →
                   Iso (P₀ x) (η (P₂ eq) a) (η (P₂ $ ⟺ eq) a)
      P-resp-Iso eq {a} = record
        { isoˡ = begin
            η (P₂ $ ⟺ eq) a ∘ η (P₂ eq) a ≈˘⟨ homomorphism PF ⟩
            η (P₂ $ eq ○ (⟺ eq)) a        ≈⟨ P-resp-≈ _ ⟩
            η (P₂ C.Equiv.refl) a          ≈⟨ identity PF ⟩
            id                             ∎
        ; isoʳ = begin
            η (P₂ eq) a ∘ η (P₂ $ ⟺ eq) a  ≈˘⟨ homomorphism PF ⟩
            η (P₂ $ (⟺ eq) ○ eq) a         ≈⟨ P-resp-≈ _ ⟩
            η (P₂ C.Equiv.refl) a           ≈⟨ identity PF ⟩
            id                              ∎
        }

    -- Objects and morphism

    Obj : Set (o ⊔ o′)
    Obj = Σ C.Obj (λ x → Category.Obj $ P₀ x)

    _⇒_ : Obj → Obj → Set (ℓ ⊔ ℓ′)
    (x₁ , a₁) ⇒ (x₂ , a₂) = Σ (x₁ C.⇒ x₂) λ f → P₀ x₁ [ a₁ , P₁ f $₀ a₂ ]

    -- Pairwise equivalence
    --
    -- The second components of equal morphisms don't live in the same
    -- homset because their domains don't agree 'on the nose'.  Hence
    -- the second components are equal only up to coherent iso.  This
    -- substantially complicates the proofs of associativity, the unit
    -- laws and functionality of composition.

    _≈_ : ∀ {A B} (f₁ f₂ : A ⇒ B) → Set (e ⊔ e′)
    _≈_ {x₁ , a₁} {x₂ , a₂} (f₁ , g₁) (f₂ , g₂) =
      Σ (f₁ C.≈ f₂) λ eq → η (P₂ $ eq) a₂ D.∘ g₁ D.≈ g₂
      where module D = Category (P₀ x₁) using (_∘_; _≈_)

    -- a particular natural transformation recurs, name it
    λP : {A : Obj} → let (x , a) = A in
         Category._⇒_ (P₀ x) a (F₀ (F₀ PF C.id) a)
    λP {_ , a} = η (unitˡ.η (lift tt)) a

    -- Identity and composition

    id : ∀ {A} → A ⇒ A
    id = C.id , λP

    _∘_ : ∀ {A B C} → B ⇒ C → A ⇒ B → A ⇒ C
    _∘_ {x₁ , a₁} {_ , a₂} {_ , a₃} (f₁ , g₁) (f₂ , g₂) =
      f₁ C.∘ f₂ , (η (Hom.η (f₂ , f₁)) a₃ D.∘ P₁ f₂ $₁ g₁) D.∘ g₂
      where module D = Category (P₀ x₁) using (_∘_; _≈_)

    -- Associativity and unit laws.
    --
    -- Because the second component of equality only holds up to
    -- coherent iso, we need to invoke the coherence conditions
    -- associated with the pseudofunctor P to establish associativity.
    --
    -- Once we realize this, the proofs are not particularly hard, but
    -- long and tedious (especially that of associativity). Using the
    -- 'right' combinators helps with the tediousness of it all.
    -- Lots of renaming also helps keep things "readable".

    assoc : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} →
            (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
    assoc {x₁ , _} {x₂ , _} {x₃ , a₃} {_ , a₄} {f₁ , g₁} {f₂ , g₂} {f₃ , g₃} =
      C.assoc , ( Equiv.trans (pullˡ before-g₁ {f = g₁}) D.assoc)
      where
        module D = Category (P₀ x₁)
        module E = Category (P₀ x₂) using (_∘_; assoc)
        module F = Category (P₀ x₃) using (id)
        open D renaming (_∘_ to _∙_)
        open MR (P₀ x₁)
        -- Provide pseudo-mnemonic short names
        assoc₄ : F₀ (F₀ PF ((f₃ C.∘ f₂) C.∘ f₁)) a₄ D.⇒ F₀ (F₀ PF (f₃ C.∘ f₂ C.∘ f₁)) a₄
        assoc₄   = η (P₂ C.assoc) a₄
        Hom₁₃₂   = η (Hom.η (f₁ , f₃ C.∘ f₂)) a₄
        Hom₂₃    = η (Hom.η (f₂ , f₃)) a₄
        Hom₂₁₃   = η (Hom.η (f₂ C.∘ f₁ , f₃)) a₄
        Hom₁₂    = η (Hom.η (f₁ , f₂)) a₃
        P₂₃      = P₁ f₂ $₁ g₃
        P₁H₂₃    = P₁ f₁ $₁ Hom₂₃
        P₁₂₃₂    = P₁ f₁ $₁ (P₂₃ E.∘ g₂)
        P₂₁$id   = P₁ (f₂ C.∘ f₁) $₁ F.id
        P₃₄      = P₁ f₃ $₀ a₄
        Hom₁₂P₃₄ = η (Hom.η (f₁ , f₂)) P₃₄
        P₁₂      = P₁ f₁ $₁ g₂
        P₂₁₃     = P₁ (f₂ C.∘ f₁) $₁ g₃
        open HomReasoning
        -- The full proof has ... ∙ g₁ D.≈ ... ∙ g₁ , so abstract that out
        before-g₁ : assoc₄ ∙ (Hom₁₃₂ ∙ P₁ f₁ $₁ ((Hom₂₃ E.∘ P₂₃) E.∘ g₂)) D.≈
                    (Hom₂₁₃ ∙ (P₁ (f₂ C.∘ f₁) $₁ g₃)) ∙ Hom₁₂ ∙ (P₁ f₁ $₁ g₂)
        before-g₁ =
         (begin
          assoc₄ ∙ Hom₁₃₂ ∙ P₁ f₁ $₁ ((Hom₂₃ E.∘ P₂₃) E.∘ g₂)                ≈⟨ refl⟩∘⟨ ( refl⟩∘⟨ F-resp-≈ (P₁ f₁) E.assoc ) ⟩
          assoc₄ ∙ Hom₁₃₂ ∙ P₁ f₁ $₁ (Hom₂₃ E.∘ P₂₃ E.∘ g₂)                  ≈⟨ refl⟩∘⟨ ( refl⟩∘⟨ homomorphism (P₁ f₁) ) ⟩
          assoc₄ ∙ Hom₁₃₂ ∙ P₁H₂₃ ∙ P₁ f₁ $₁ (P₂₃ E.∘ g₂)                    ≈⟨ pushʳ D.sym-assoc ⟩
          (assoc₄ ∙ Hom₁₃₂ ∙ P₁H₂₃) ∙ P₁ f₁ $₁ (P₂₃ E.∘ g₂)                  ≈˘⟨ (refl⟩∘⟨ refl⟩∘⟨ D.identityʳ) ⟩∘⟨refl ⟩
          (assoc₄ ∙ Hom₁₃₂ ∙ (P₁H₂₃ ∙ D.id)) ∙ P₁₂₃₂                         ≈˘⟨ (refl⟩∘⟨ refl⟩∘⟨ D.identityʳ) ⟩∘⟨refl ⟩
          (assoc₄ ∙ Hom₁₃₂ ∙ (P₁H₂₃ ∙ D.id) ∙ D.id) ∙ P₁₂₃₂                  ≈˘⟨ (refl⟩∘⟨ P-assoc) ⟩∘⟨refl ⟩
          (assoc₄ ∙ η (P₂ C.sym-assoc) a₄ ∙ Hom₂₁₃ ∙ P₂₁$id ∙
             Hom₁₂P₃₄) ∙ P₁₂₃₂                                               ≈⟨ pullˡ (⟺ (homomorphism PF)) ⟩∘⟨refl ⟩
          (η (P₂ (C.Equiv.trans C.sym-assoc C.assoc)) a₄
             ∙ Hom₂₁₃ ∙ P₂₁$id ∙ Hom₁₂P₃₄) ∙ P₁₂₃₂                           ≈⟨ P-resp-≈ _ ⟩∘⟨refl ⟩∘⟨refl ⟩
         (η (P₂ C.Equiv.refl) a₄ ∙ Hom₂₁₃ ∙ P₂₁$id ∙ Hom₁₂P₃₄) ∙ P₁₂₃₂       ≈⟨ elimˡ (identity PF) ⟩∘⟨refl ⟩
         (Hom₂₁₃ ∙ P₂₁$id ∙ Hom₁₂P₃₄) ∙ P₁₂₃₂                                ≈⟨ refl⟩∘⟨ homomorphism (P₁ f₁) ⟩
         (Hom₂₁₃ ∙ P₂₁$id ∙ Hom₁₂P₃₄) ∙ (P₁ f₁ $₁ P₂₃ ∙ P₁₂)                 ≈⟨ D.sym-assoc ⟩∘⟨refl ⟩
         ((Hom₂₁₃ ∙ P₂₁$id) ∙ Hom₁₂P₃₄) ∙ (P₁ f₁ $₁ P₂₃ ∙ P₁₂)               ≈⟨ center (commute (Hom.η (f₁ , f₂)) g₃) ⟩
         (Hom₂₁₃ ∙ P₂₁$id) ∙ (P₂₁₃ ∙ Hom₁₂) ∙ P₁₂                            ≈⟨ elimʳ (identity (P₁ _)) ⟩∘⟨refl ⟩
         Hom₂₁₃ ∙ (P₂₁₃ ∙ Hom₁₂) ∙ P₁₂                                       ≈⟨ pushʳ D.assoc ⟩
         (Hom₂₁₃ ∙ P₂₁₃) ∙ Hom₁₂ ∙ P₁₂
         ∎)

    identityˡ : ∀ {A B} {f : A ⇒ B} → id ∘ f ≈ f
    identityˡ {x₁ , _} {_ , a₂} {f , g} =
      C.identityˡ ,
      (begin
        η Pˡ a₂ ∙ (η (Hom.η (f , C.id)) a₂ ∙ P₁ f $₁ λP) ∙ g             ≈⟨ pullˡ $ refl⟩∘⟨ refl⟩∘⟨ D.Equiv.sym D.identityʳ ⟩
        (η Pˡ a₂ ∙ (η (Hom.η (f , C.id)) a₂ ∙ (P₁ f $₁ λP ∙ D.id))) ∙ g  ≈⟨ elimˡ unitaryʳ ⟩
        g
      ∎)
      where
        Pˡ = P₂ C.identityˡ
        module D = Category (P₀ x₁)
        open D renaming (_∘_ to _∙_)
        open HomReasoning
        open MR (P₀ x₁)

    identityʳ : ∀ {A B} {f : A ⇒ B} → f ∘ id ≈ f
    identityʳ {x₁ , a₁} {_ , a₂} {f , g} =
      C.identityʳ ,
      (begin
        P-identityʳ ∙ (Hom-1*f ∙ Pid) ∙ η-unitˡ                  ≈⟨ refl⟩∘⟨ pullʳ (⟺ $ commute (unitˡ.η _) g) ⟩
        P-identityʳ ∙ Hom-1*f ∙ η-unitˡ₂ ∙ g                     ≈⟨ pushʳ D.sym-assoc ⟩
        (P-identityʳ ∙ Hom-1*f ∙ η-unitˡ₂) ∙ g                   ≈⟨ (refl⟩∘⟨ refl⟩∘⟨ introˡ (identity (P₁ C.id))) ⟩∘⟨refl ⟩
        (P-identityʳ ∙ Hom-1*f ∙ P₁ C.id $₁ D.id ∙ η-unitˡ₂) ∙ g ≈⟨ elimˡ unitaryˡ ⟩
        g
      ∎)
      where
        module D = Category (P₀ x₁)
        open D renaming (_∘_ to _∙_)
        open HomReasoning
        open MR (P₀ x₁)
        P-identityʳ = η (P₂ C.identityʳ) a₂
        Hom-1*f     = η (Hom.η (C.id , f)) a₂
        Pid         = P₁ C.id $₁ g
        η-unitˡ     = η (unitˡ.η _) a₁
        Pfa₂        = P₁ f $₀ a₂
        η-unitˡ₂    = η (unitˡ.η _) Pfa₂

    -- Pair-wise equality is an equivalence

    refl : ∀ {A B} {f : A ⇒ B} → f ≈ f
    refl {x , _} = C.Equiv.refl , MR.elimˡ (P₀ x) (identity PF)


    sym : ∀ {A B} {f g : A ⇒ B} → f ≈ g → g ≈ f
    sym {x₁ , _} {_ , a₂} {_ , g₁} {_ , g₂} (f₁≈f₂ , g₁≈g₂) =
      C.Equiv.sym f₁≈f₂ ,
      (begin
         η (P₂ f₂≈f₁) a₂ ∙ g₂                      ≈⟨ MR.pushʳ (P₀ x₁) ( Equiv.sym g₁≈g₂ ) ⟩
         (η (P₂ f₂≈f₁) a₂ ∙ η (P₂ f₁≈f₂) a₂) ∙ g₁  ≈⟨ elimˡ (Iso.isoˡ $ P-resp-Iso f₁≈f₂) ⟩
         g₁
       ∎)
      where
        f₂≈f₁ = C.Equiv.sym f₁≈f₂
        module D = Category (P₀ x₁)
        open D renaming (_∘_ to _∙_)
        open HomReasoning
        open MR (P₀ x₁)


    trans : ∀ {A B} {f g h : A ⇒ B} → f ≈ g → g ≈ h → f ≈ h
    trans {x₁ , _} {_ , a₂} {_ , g₁} {_ , g₂} {_ , g₃}
          (f₁≈f₂ , g₁≈g₂) (f₂≈f₃ , g₂≈g₃) =
      C.Equiv.trans f₁≈f₂ f₂≈f₃ ,
      (begin
         η (P₂ $ C.Equiv.trans f₁≈f₂ f₂≈f₃) a₂ ∙ g₁    ≈⟨ MR.pushˡ (P₀ x₁) $ homomorphism PF ⟩
         η (P₂ f₂≈f₃) a₂ ∙ η (P₂ f₁≈f₂) a₂ ∙ g₁        ≈⟨ refl⟩∘⟨ g₁≈g₂ ⟩
         η (F₁ PF f₂≈f₃) a₂ ∙ g₂                       ≈⟨ g₂≈g₃ ⟩
         g₃
       ∎)
      where
        module D = Category (P₀ x₁)
        open D renaming (_∘_ to _∙_)
        open HomReasoning

    ≈-equiv : ∀ {A B} → IsEquivalence (_≈_ {A} {B})
    ≈-equiv = record
      { refl  = refl
      ; sym   = sym
      ; trans = trans
      }

    -- Functoriality of composition
    --
    -- The key here is to use naturality of P-homomorphism to relate
    -- functoriality of composition (∘) in C to functoriality of
    -- composition (⊚) in (P₀ x₁).

    ∘-resp-≈ : ∀ {A B C} {f h : B ⇒ C} {g i : A ⇒ B} →
               f ≈ h → g ≈ i → f ∘ g ≈ h ∘ i
    ∘-resp-≈ {x₁ , _} {x₂ , a₂} {_ , a₃}
             {f₁ , g₁} {f₂ , g₂} {f₃ , g₃} {f₄ , g₄}
             (f₁≈f₂ , g₁≈g₂) (f₃≈f₄ , g₃≈g₄) =
      C.∘-resp-≈ f₁≈f₂ f₃≈f₄ ,
      (begin
         η (P₂ $ C.∘-resp-≈ f₁≈f₂ f₃≈f₄) a₃ ∙ (Hom₃₁ ∙ P₃₁) ∙ g₃    ≈⟨ pushʳ D.assoc ⟩
         (η (P₂ $ C.∘-resp-≈ f₁≈f₂ f₃≈f₄) a₃ ∙ Hom₃₁) ∙ P₃₁ ∙ g₃    ≈˘⟨ Hom.commute (f₃≈f₄ , f₁≈f₂) ⟩∘⟨refl ⟩
         (Hom₄₂ ∙ P₁ f₄ $₁ η₁≈₂ ∙ η (P₂ f₃≈f₄) P₁₃) ∙ P₃₁ ∙ g₃      ≈⟨ pullʳ D.assoc ⟩
         Hom₄₂ ∙ P₁ f₄ $₁ η₁≈₂ ∙ η (P₂ f₃≈f₄) P₁₃ ∙ P₃₁ ∙ g₃        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ D.sym-assoc ⟩
         Hom₄₂ ∙ P₁ f₄ $₁ η₁≈₂ ∙ (η (P₂ f₃≈f₄) P₁₃ ∙ P₃₁) ∙ g₃      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (commute (P₂ f₃≈f₄) g₁ ⟩∘⟨refl) ⟩
         Hom₄₂ ∙ P₁ f₄ $₁ η₁≈₂ ∙ (P₄₁ ∙ η₃≈₄) ∙ g₃                  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ D.assoc ⟩
         Hom₄₂ ∙ P₁ f₄ $₁ η₁≈₂ ∙ P₄₁ ∙ η₃≈₄ ∙ g₃                    ≈⟨ pushʳ D.sym-assoc ⟩
         (Hom₄₂ ∙ P₁ f₄ $₁ η₁≈₂ ∙ P₄₁) ∙ η₃≈₄ ∙ g₃                  ≈˘⟨ ∘-resp-≈ˡ $ ∘-resp-≈ʳ $ homomorphism (P₁ f₄) ⟩
         (Hom₄₂ ∙ P₁ f₄ $₁ (η₁≈₂ E.∘ g₁)) ∙ η₃≈₄ ∙ g₃               ≈⟨ (refl⟩∘⟨ (F-resp-≈ (P₁ f₄) g₁≈g₂)) ⟩∘⟨ g₃≈g₄ ⟩
         (Hom₄₂ ∙ P₁ f₄ $₁ g₂) ∙ g₄
       ∎)
      where
        module D = Category (P₀ x₁)
        module E = Category (P₀ x₂)
        open D renaming (_∘_ to _∙_)
        infixl -5 _then_
        _then_ = Equiv.trans
        open HomReasoning
        open MR (P₀ x₁)
        Hom₄₂ = η (Hom.η (f₄ , f₂)) a₃
        Hom₃₁ = η (Hom.η (f₃ , f₁)) a₃
        P₃₁   = P₁ f₃ $₁ g₁
        P₁₃   = P₁ f₁ $₀ a₃
        P₄₁   = P₁ f₄ $₁ g₁
        η₃≈₄  = η (P₂ f₃≈f₄) a₂
        η₁≈₂  = η (P₂ f₁≈f₂) a₃

  Grothendieck : Category (o ⊔ o′) (ℓ ⊔ ℓ′) (e ⊔ e′)
  Grothendieck = record
    { Obj       = Obj
    ; _⇒_       = _⇒_
    ; _≈_       = _≈_
    ; id        = id
    ; _∘_       = _∘_
    ; assoc     = assoc
    ; sym-assoc = sym assoc
    ; identityˡ = identityˡ
    ; identityʳ = identityʳ
    ; identity² = identityˡ -- this is cheating, TODO
    ; equiv     = ≈-equiv
    ; ∘-resp-≈  = ∘-resp-≈
    }

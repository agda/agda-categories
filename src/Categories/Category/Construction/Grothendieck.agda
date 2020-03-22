{-# OPTIONS --without-K --safe #-}
module Categories.Category.Construction.Grothendieck where

-- The construction of a 1-Category from a (contravariant)
-- pseudofunctor into Cats (as a bicategory)

open import Level
open import Data.Product using (Σ; _,_)
open import Function using (_$_)
open import Relation.Binary using (IsEquivalence)

open import Categories.Category
open import Categories.Bicategory using (Bicategory)
open import Categories.Bicategory.Instance.Cats
open import Categories.Bicategory.Construction.1-Category
open import Categories.Functor renaming (id to idF)
open import Categories.Morphism using (Iso)
open import Categories.Pseudofunctor
open import Categories.NaturalTransformation hiding (id)

private
  variable
    o ℓ e o′ ℓ′ e′ : Level

module _ {C : Category o ℓ e} {b}
         (P : Pseudofunctor (1-Category b (Category.op C)) (Cats o′ ℓ′ e′)) where

  open Pseudofunctor P renaming (P₁ to PF; assoc to P-assoc)
  open Functor using () renaming (F₀ to _$₀_; F₁ to _$₁_)
  open NaturalTransformation

  private
    infix  4 _≈_ _⇒_
    infixr 9 _∘_

    module B = Bicategory (1-Category b (Category.op C))
    module C = Category C
    module _ {x y} where
      open Functor (PF {x} {y}) public
        renaming (F₀ to P₁; F₁ to P₂; F-resp-≈ to P-resp-≈)

    open Functor

    module _ {x y : C.Obj} where
      open Category (P₀ x)
      open HomReasoning

      -- A helper lemma.

      P-resp-Iso : ∀ {f g : C [ x , y ]} (eq : C [ f ≈ g ]) {a} →
                   Iso (P₀ x) (η (P₂ eq) a) (η (P₂ $ C.Equiv.sym eq) a)
      P-resp-Iso eq {a} = record
        { isoˡ = begin
            η (P₂ $ C.Equiv.sym eq) a ∘ η (P₂ eq) a       ≈˘⟨ homomorphism PF ⟩
            η (P₂ $ C.Equiv.trans eq (C.Equiv.sym eq)) a  ≈⟨ P-resp-≈ _ ⟩
            η (P₂ C.Equiv.refl) a                         ≈⟨ identity PF ⟩
            id                                            ∎
        ; isoʳ = begin
            η (P₂ eq) a ∘ η (P₂ $ C.Equiv.sym eq) a       ≈˘⟨ homomorphism PF ⟩
            η (P₂ $ C.Equiv.trans (C.Equiv.sym eq) eq) a  ≈⟨ P-resp-≈ _ ⟩
            η (P₂ C.Equiv.refl) a                         ≈⟨ identity PF ⟩
            id                                            ∎
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
      where module D = Category (P₀ x₁)

    -- Identity and composition

    id : ∀ {A} → A ⇒ A
    id {_ , a} = C.id , η (unitˡ.η _) a

    _∘_ : ∀ {A B C} → B ⇒ C → A ⇒ B → A ⇒ C
    _∘_ {x₁ , a₁} {_ , a₂} {_ , a₃} (f₁ , g₁) (f₂ , g₂) =
      f₁ C.∘ f₂ , (η (Hom.η (f₂ , f₁)) a₃ D.∘ P₁ f₂ $₁ g₁) D.∘ g₂
      where module D = Category (P₀ x₁)

    -- Associativity and unit laws.
    --
    -- Because the second component of equality only holds up to
    -- coherent iso, we need to invoke the coherence conditions
    -- associated with the pseudofunctor P to establish associativity.
    --
    -- Once we realize this, the proofs are not particularly hard, but
    -- long and tedious (especially that of associativity), mostly
    -- because they involve re-arranging lots of parentheses via
    -- manual application of the underlying associativity laws.

    assoc : ∀ {A B C D} {f : A ⇒ B} {g : B ⇒ C} {h : C ⇒ D} →
            (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
    assoc {x₁ , _} {x₂ , _} {x₃ , a₃} {_ , a₄} {f₁ , g₁} {f₂ , g₂} {f₃ , g₃} =
      C.assoc ,
      (begin
        η (P₂ C.assoc) a₄ ∙
        (η (Hom.η (f₁ , f₃ C.∘ f₂)) a₄ ∙
         P₁ f₁ $₁ ((η (Hom.η (f₂ , f₃)) a₄ E.∘ P₁ f₂ $₁ g₃) E.∘ g₂)) ∙ g₁
      ≈⟨ ∘-resp-≈ʳ $ ∘-resp-≈ˡ $ ∘-resp-≈ʳ $ F-resp-≈ (P₁ f₁) E.assoc  ⟩
        η (P₂ C.assoc) a₄ ∙
        (η (Hom.η (f₁ , f₃ C.∘ f₂)) a₄ ∙
         P₁ f₁ $₁ (η (Hom.η (f₂ , f₃)) a₄ E.∘ P₁ f₂ $₁ g₃ E.∘ g₂)) ∙ g₁
      ≈⟨ ∘-resp-≈ʳ $ ∘-resp-≈ˡ $ ∘-resp-≈ʳ $ homomorphism (P₁ f₁) ⟩
        η (P₂ C.assoc) a₄ ∙
        (η (Hom.η (f₁ , f₃ C.∘ f₂)) a₄ ∙
         P₁ f₁ $₁ η (Hom.η (f₂ , f₃)) a₄ ∙
         P₁ f₁ $₁ (P₁ f₂ $₁ g₃ E.∘ g₂)) ∙ g₁
      ≈⟨ ∘-resp-≈ʳ $ ∘-resp-≈ˡ $ D.sym-assoc then
         ∘-resp-≈ʳ D.assoc                   then
         D.sym-assoc                         ⟩
        (η (P₂ C.assoc) a₄ ∙
         η (Hom.η (f₁ , f₃ C.∘ f₂)) a₄ ∙
         P₁ f₁ $₁ η (Hom.η (f₂ , f₃)) a₄) ∙
        P₁ f₁ $₁ (P₁ f₂ $₁ g₃ E.∘ g₂) ∙ g₁
      ≈˘⟨ ∘-resp-≈ˡ $ ∘-resp-≈ʳ $ ∘-resp-≈ʳ (D.identityʳ then D.identityʳ) ⟩
        (η (P₂ C.assoc) a₄ ∙
         η (Hom.η (f₁ , f₃ C.∘ f₂)) a₄ ∙
         (P₁ f₁ $₁ η (Hom.η (f₂ , f₃)) a₄ ∙ D.id) ∙ D.id) ∙
        P₁ f₁ $₁ ((P₁ f₂ $₁ g₃) E.∘ g₂) ∙ g₁
      ≈˘⟨ ∘-resp-≈ˡ $ ∘-resp-≈ʳ P-assoc ⟩
        (η (P₂ C.assoc) a₄ ∙
         η (P₂ C.sym-assoc) a₄ ∙
         η (Hom.η (f₂ C.∘ f₁ , f₃)) a₄ ∙ P₁ (f₂ C.∘ f₁) $₁ F.id ∙
         η (Hom.η (f₁ , f₂)) (P₁ f₃ $₀ a₄)) ∙
        P₁ f₁ $₁ ((P₁ f₂ $₁ g₃) E.∘ g₂) ∙ g₁
      ≈⟨ ∘-resp-≈ˡ D.sym-assoc ⟩
        ((η (P₂ C.assoc) a₄ ∙ η (P₂ C.sym-assoc) a₄) ∙
         η (Hom.η (f₂ C.∘ f₁ , f₃)) a₄ ∙ P₁ (f₂ C.∘ f₁) $₁ F.id ∙
         η (Hom.η (f₁ , f₂)) (P₁ f₃ $₀ a₄)) ∙
        P₁ f₁ $₁ ((P₁ f₂ $₁ g₃) E.∘ g₂) ∙ g₁
      ≈⟨ ∘-resp-≈ˡ $ ∘-resp-≈ˡ $
         (sym (homomorphism PF) then P-resp-≈ _ then identity PF) ⟩
        (D.id ∙
         η (Hom.η (f₂ C.∘ f₁ , f₃)) a₄ ∙ P₁ (f₂ C.∘ f₁) $₁ F.id ∙
         η (Hom.η (f₁ , f₂)) (P₁ f₃ $₀ a₄)) ∙
        P₁ f₁ $₁ ((P₁ f₂ $₁ g₃) E.∘ g₂) ∙ g₁
      ≈⟨ ∘-resp-≈ D.identityˡ (∘-resp-≈ˡ $ homomorphism (P₁ f₁) ) ⟩
        (η (Hom.η (f₂ C.∘ f₁ , f₃)) a₄ ∙ P₁ (f₂ C.∘ f₁) $₁ F.id ∙
         η (Hom.η (f₁ , f₂)) (P₁ f₃ $₀ a₄)) ∙
        (P₁ f₁ $₁ (P₁ f₂ $₁ g₃) ∙ P₁ f₁ $₁ g₂) ∙ g₁
      ≈⟨ ∘-resp-≈ (D.Equiv.sym D.assoc) D.assoc  then
         D.assoc                                 then
         ∘-resp-≈ʳ (D.Equiv.sym D.assoc)         ⟩
        (η (Hom.η (f₂ C.∘ f₁ , f₃)) a₄ ∙ P₁ (f₂ C.∘ f₁) $₁ F.id) ∙
        (η (Hom.η (f₁ , f₂)) (P₁ f₃ $₀ a₄) ∙ P₁ f₁ $₁ (P₁ f₂ $₁ g₃)) ∙
        P₁ f₁ $₁ g₂ ∙ g₁
      ≈⟨ ∘-resp-≈ʳ $ ∘-resp-≈ˡ (commute (Hom.η (f₁ , f₂)) g₃) ⟩
        (η (Hom.η (f₂ C.∘ f₁ , f₃)) a₄ ∙ P₁ (f₂ C.∘ f₁) $₁ F.id) ∙
        (P₁ (f₂ C.∘ f₁) $₁ g₃ ∙ η (Hom.η (f₁ , f₂)) a₃) ∙
        P₁ f₁ $₁ g₂ ∙ g₁
      ≈⟨ ∘-resp-≈ˡ (∘-resp-≈ʳ (identity (P₁ (f₂ C.∘ f₁))) then D.identityʳ) ⟩
        η (Hom.η (f₂ C.∘ f₁ , f₃)) a₄ ∙
        (P₁ (f₂ C.∘ f₁) $₁ g₃ ∙ η (Hom.η (f₁ , f₂)) a₃) ∙
        P₁ f₁ $₁ g₂ ∙ g₁
      ≈⟨ ∘-resp-≈ʳ D.assoc                then
         D.Equiv.sym D.assoc              then
         ∘-resp-≈ʳ (D.Equiv.sym D.assoc)  ⟩
        (η (Hom.η (f₂ C.∘ f₁ , f₃)) a₄ ∙ (P₁ (f₂ C.∘ f₁) $₁ g₃)) ∙
        (η (Hom.η (f₁ , f₂)) a₃ ∙ (P₁ f₁ $₁ g₂)) ∙ g₁
      ∎)
      where
        module D = Category (P₀ x₁)
        module E = Category (P₀ x₂)
        module F = Category (P₀ x₃)
        open D renaming (_∘_ to _∙_)
        infixl -5 _then_
        _then_ = Equiv.trans
        open HomReasoning

    identityˡ : ∀ {A B} {f : A ⇒ B} → id ∘ f ≈ f
    identityˡ {x₁ , _} {_ , a₂} {f , g} =
      C.identityˡ ,
      (begin
        η (P₂ C.identityˡ) a₂ ∙
        ((η (Hom.η (f , C.id)) a₂ ∙ P₁ f $₁ η (unitˡ.η _) a₂) ∙ g)
      ≈⟨ D.sym-assoc ⟩
        (η (P₂ C.identityˡ) a₂ ∙
         (η (Hom.η (f , C.id)) a₂ ∙ P₁ f $₁ η (unitˡ.η _) a₂)) ∙ g
      ≈˘⟨ ∘-resp-≈ˡ (∘-resp-≈ʳ (∘-resp-≈ʳ D.identityʳ)) ⟩
        (η (P₂ C.identityˡ) a₂ ∙
         (η (Hom.η (f , C.id)) a₂ ∙ (P₁ f $₁ η (unitˡ.η _) a₂ ∙ D.id))) ∙ g
      ≈⟨ ∘-resp-≈ˡ unitaryʳ ⟩
        D.id ∙ g
      ≈⟨ D.identityˡ ⟩
        g
      ∎)
      where
        module D = Category (P₀ x₁)
        open D renaming (_∘_ to _∙_)
        open HomReasoning

    identityʳ : ∀ {A B} {f : A ⇒ B} → f ∘ id ≈ f
    identityʳ {x₁ , a₁} {_ , a₂} {f , g} =
      C.identityʳ ,
      (begin
        η (P₂ C.identityʳ) a₂ ∙
        ((η (Hom.η (C.id , f)) a₂ ∙ P₁ C.id $₁ g) ∙ η (unitˡ.η _) a₁)
      ≈⟨ ∘-resp-≈ʳ D.assoc ⟩
        η (P₂ C.identityʳ) a₂ ∙
        (η (Hom.η (C.id , f)) a₂ ∙ (P₁ C.id $₁ g ∙ η (unitˡ.η _) a₁))
      ≈˘⟨ ∘-resp-≈ʳ $ ∘-resp-≈ʳ $ commute (unitˡ.η _) g ⟩
        η (P₂ C.identityʳ) a₂ ∙
        (η (Hom.η (C.id , f)) a₂ ∙ (η (unitˡ.η _) (P₁ f $₀ a₂) ∙ g))
      ≈⟨ ∘-resp-≈ʳ D.sym-assoc ⟩
        η (P₂ C.identityʳ) a₂ ∙
        ((η (Hom.η (C.id , f)) a₂ ∙ η (unitˡ.η _) (P₁ f $₀ a₂)) ∙ g)
      ≈⟨ D.sym-assoc ⟩
        (η (P₂ C.identityʳ) a₂ ∙
         (η (Hom.η (C.id , f)) a₂ ∙ η (unitˡ.η _) (P₁ f $₀ a₂))) ∙ g
      ≈˘⟨ ∘-resp-≈ˡ $ ∘-resp-≈ʳ $ ∘-resp-≈ʳ D.identityˡ ⟩
        (η (P₂ C.identityʳ) a₂ ∙
         (η (Hom.η (C.id , f)) a₂ ∙ (D.id ∙ η (unitˡ.η _) (P₁ f $₀ a₂)))) ∙ g
      ≈˘⟨ ∘-resp-≈ˡ $ ∘-resp-≈ʳ $ ∘-resp-≈ʳ $
          ∘-resp-≈ˡ $ identity (P₁ C.id) ⟩
        (η (P₂ C.identityʳ) a₂ ∙
         (η (Hom.η (C.id , f)) a₂ ∙
          ((P₁ C.id $₁ D.id) ∙ η (unitˡ.η _) (P₁ f $₀ a₂)))) ∙ g
      ≈⟨ ∘-resp-≈ˡ unitaryˡ ⟩
        D.id ∙ g
      ≈⟨ D.identityˡ ⟩
        g
      ∎)
      where
        module D = Category (P₀ x₁)
        open D renaming (_∘_ to _∙_)
        open HomReasoning

    -- Pair-wise equality is an equivalence

    refl : ∀ {A B} {f : A ⇒ B} → f ≈ f
    refl {x , _} =
      C.Equiv.refl , D.Equiv.trans (D.∘-resp-≈ˡ (identity PF)) D.identityˡ
      where module D = Category (P₀ x)

    sym : ∀ {A B} {f g : A ⇒ B} → f ≈ g → g ≈ f
    sym {x₁ , _} {_ , a₂} {_ , g₁} {_ , g₂} (f₁≈f₂ , g₁≈g₂) =
      C.Equiv.sym f₁≈f₂ ,
      (begin
         η (P₂ $ C.Equiv.sym f₁≈f₂) a₂ ∙ g₂
       ≈˘⟨ ∘-resp-≈ʳ g₁≈g₂ ⟩
         η (P₂ $ C.Equiv.sym f₁≈f₂) a₂ ∙ η (P₂ f₁≈f₂) a₂ ∙ g₁
       ≈⟨ D.sym-assoc ⟩
         (η (P₂ $ C.Equiv.sym f₁≈f₂) a₂ ∙ η (P₂ f₁≈f₂) a₂) ∙ g₁
       ≈⟨ ∘-resp-≈ˡ $ Iso.isoˡ $ P-resp-Iso f₁≈f₂ ⟩
         D.id ∙ g₁
       ≈⟨ D.identityˡ ⟩
         g₁
       ∎)
      where
        module D = Category (P₀ x₁)
        open D renaming (_∘_ to _∙_)
        open HomReasoning

    trans : ∀ {A B} {f g h : A ⇒ B} → f ≈ g → g ≈ h → f ≈ h
    trans {x₁ , _} {_ , a₂} {_ , g₁} {_ , g₂} {_ , g₃}
          (f₁≈f₂ , g₁≈g₂) (f₂≈f₃ , g₂≈g₃) =
      C.Equiv.trans f₁≈f₂ f₂≈f₃ ,
      (begin
         η (P₂ $ C.Equiv.trans f₁≈f₂ f₂≈f₃) a₂ ∙ g₁
       ≈⟨ ∘-resp-≈ˡ $ homomorphism PF ⟩
         (η (P₂ f₂≈f₃) a₂ ∙ η (P₂ f₁≈f₂) a₂) ∙ g₁
       ≈⟨ D.assoc ⟩
         η (P₂ f₂≈f₃) a₂ ∙ η (P₂ f₁≈f₂) a₂ ∙ g₁
       ≈⟨ ∘-resp-≈ʳ g₁≈g₂ ⟩
         η (F₁ PF f₂≈f₃) a₂ ∙ g₂
       ≈⟨ g₂≈g₃ ⟩
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

    -- Functionality of composition
    --
    -- The key here is to use naturality of P-homomorphism to relate
    -- functionality of composition (∘) in C to functoriality of
    -- composition (⊚) in (P₀ x₁).

    ∘-resp-≈ : ∀ {A B C} {f h : B ⇒ C} {g i : A ⇒ B} →
               f ≈ h → g ≈ i → f ∘ g ≈ h ∘ i
    ∘-resp-≈ {x₁ , _} {x₂ , a₂} {_ , a₃}
             {f₁ , g₁} {f₂ , g₂} {f₃ , g₃} {f₄ , g₄}
             (f₁≈f₂ , g₁≈g₂) (f₃≈f₄ , g₃≈g₄) =
             C.∘-resp-≈ f₁≈f₂ f₃≈f₄ ,
             (begin
                η (P₂ $ C.∘-resp-≈ f₁≈f₂ f₃≈f₄) a₃ ∙
                (η (Hom.η (f₃ , f₁)) a₃ ∙ P₁ f₃ $₁ g₁) ∙ g₃
              ≈⟨ ∘-resp-≈ʳ D.assoc  then D.sym-assoc ⟩
                (η (P₂ $ C.∘-resp-≈ f₁≈f₂ f₃≈f₄) a₃ ∙ η (Hom.η (f₃ , f₁)) a₃) ∙
                P₁ f₃ $₁ g₁ ∙ g₃
              ≈˘⟨ ∘-resp-≈ˡ $ Hom.commute (f₃≈f₄ , f₁≈f₂) ⟩
                (η (Hom.η (f₄ , f₂)) a₃ ∙
                 P₁ f₄ $₁ (η (P₂ f₁≈f₂) a₃) ∙ η (P₂ f₃≈f₄) (P₁ f₁ $₀ a₃)) ∙
                P₁ f₃ $₁ g₁ ∙ g₃
              ≈⟨ D.assoc                                   then
                 ∘-resp-≈ʳ D.assoc                         then
                 ∘-resp-≈ʳ $ ∘-resp-≈ʳ $ D.sym-assoc ⟩
                η (Hom.η (f₄ , f₂)) a₃ ∙
                P₁ f₄ $₁ (η (P₂ f₁≈f₂) a₃) ∙
                (η (P₂ f₃≈f₄) (P₁ f₁ $₀ a₃) ∙ P₁ f₃ $₁ g₁) ∙ g₃
              ≈⟨ ∘-resp-≈ʳ $ ∘-resp-≈ʳ $ ∘-resp-≈ˡ (commute (P₂ f₃≈f₄) g₁) ⟩
                η (Hom.η (f₄ , f₂)) a₃ ∙
                P₁ f₄ $₁ (η (P₂ f₁≈f₂) a₃) ∙
                (P₁ f₄ $₁ g₁ ∙ η (P₂ f₃≈f₄) a₂) ∙ g₃
              ≈⟨ ∘-resp-≈ʳ $ ∘-resp-≈ʳ D.assoc then
                 ∘-resp-≈ʳ $ D.sym-assoc       then
                 D.sym-assoc                   ⟩
                (η (Hom.η (f₄ , f₂)) a₃ ∙
                 P₁ f₄ $₁ (η (P₂ f₁≈f₂) a₃) ∙ P₁ f₄ $₁ g₁) ∙
                η (P₂ f₃≈f₄) a₂ ∙ g₃
              ≈˘⟨ ∘-resp-≈ˡ $ ∘-resp-≈ʳ $ homomorphism (P₁ f₄) ⟩
                (η (Hom.η (f₄ , f₂)) a₃ ∙
                 P₁ f₄ $₁ (η (P₂ f₁≈f₂) a₃ E.∘ g₁)) ∙
                η (P₂ f₃≈f₄) a₂ ∙ g₃
              ≈⟨ D.∘-resp-≈ (∘-resp-≈ʳ (F-resp-≈ (P₁ f₄) g₁≈g₂)) g₃≈g₄ ⟩
                (η (Hom.η (f₄ , f₂)) a₃ ∙ P₁ f₄ $₁ g₂) ∙ g₄
              ∎)
      where
        module D = Category (P₀ x₁)
        module E = Category (P₀ x₂)
        open D renaming (_∘_ to _∙_)
        infixl -5 _then_
        _then_ = Equiv.trans
        open HomReasoning

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
    ; identity² = identityˡ
    ; equiv     = ≈-equiv
    ; ∘-resp-≈  = ∘-resp-≈
    }

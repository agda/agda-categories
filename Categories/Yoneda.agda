{-# OPTIONS --without-K --safe #-}
module Categories.Yoneda where

-- Yoneda Lemma.  In total, provides:
-- * the Yoneda Embedding (called embed here) from any Category C into Presheaves C
--   Worth noticing that there is no 'locally small' condition here; however, if one looks at
--   the levels involved, there is indeed a raise from that of C to that of Presheaves C.
-- * The traditional Yoneda lemma (yoneda-inverse) which says that for any object a of C, and
--   any Presheaf F over C (where our presheaves are over Setoids), then
--   Hom[ Presheaves C] (Functor.F₀ embed a , F) ≅ Functor.F₀ F a
--   as Setoids. In addition, Yoneda (yoneda) also says that this isomorphism is natural in a and F.
open import Level
open import Function.Core using (_$_) -- else there's a conflict with the import below
open import Function.Inverse using (Inverse)
open import Function.Equality using (Π; _⟨$⟩_; cong)
open import Relation.Binary using (module Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidR
open import Data.Product using (_,_; Σ)

open import Categories.Category using (Category; _[_,_])
open import Categories.Category.Product
open import Categories.Category.Construction.Presheaves
open import Categories.Category.Construction.Functors
open import Categories.Category.Instance.Setoids
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Hom using (module Hom; Hom[_][-,_]; Hom[_][-,-])
open import Categories.Functor.Bifunctor
open import Categories.Functor.Presheaf
open import Categories.Functor.Construction.LiftSetoids
open import Categories.NaturalTransformation using (NaturalTransformation) renaming (id to idN)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)

import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR

private
  variable
    o ℓ e : Level

module _ (C : Category o ℓ e) where
  open Category C
  open HomReasoning
  open Functor
  open NaturalTransformation
  private
    module CE = Category.Equiv C
    module C = Category C

  -- This NaturalTransformation should probably got into NaturalTransformation.Hom,
  -- in analogy with Functor.Hom above.
  Hom[A,C]⇒Hom[B,C] : {A B : Obj} → (A ⇒ B) → NaturalTransformation Hom[ C ][-, A ] Hom[ C ][-, B ]
  Hom[A,C]⇒Hom[B,C] {A} A⇒B = record
    { η       = λ X → record { _⟨$⟩_ = λ X⇒A → A⇒B ∘ X⇒A ; cong = ∘-resp-≈ʳ }
    ; commute = λ {X} {Y} f {g} {h} g≈h → begin
        A⇒B ∘ id ∘ g ∘ f   ≈˘⟨ assoc ⟩
        (A⇒B ∘ id) ∘ g ∘ f ≈⟨ ∘-resp-≈ id-comm (∘-resp-≈ˡ g≈h) ⟩
        (id ∘ A⇒B) ∘ h ∘ f ≈⟨ assoc ○ ⟺ (∘-resp-≈ʳ assoc) ⟩ -- TODO: MR.Reassociate
        id ∘ (A⇒B ∘ h) ∘ f ∎
    }

  -- The Yoneda embedding functor
  embed : Functor C (Presheaves C)
  embed = record
    { F₀           = Hom[ C ][-,_]
    ; F₁           = Hom[A,C]⇒Hom[B,C] -- A⇒B induces a NatTrans on the Homs.
    ; identity     = identityˡ ○_
    ; homomorphism = λ h₁≈h₂ → ∘-resp-≈ʳ h₁≈h₂ ○ assoc
    ; F-resp-≈     = λ f≈g h≈i → ∘-resp-≈ f≈g h≈i
    }

  -- Using the adjunction between product and product, we get a kind of contravariant Bifunctor
  yoneda-inverse : (a : Obj) (F : Presheaf C (Setoids ℓ e)) →
    Inverse (Category.hom-setoid (Presheaves C) {Functor.F₀ embed a} {F}) (Functor.F₀ F a)
  yoneda-inverse a F = record
    { to         = record
      { _⟨$⟩_ = λ nat → η nat a ⟨$⟩ id
      ; cong  = λ i≈j → i≈j CE.refl
      }
    ; from       = record
      { _⟨$⟩_ = λ x → record
        { η       = λ X → record
          { _⟨$⟩_ = λ X⇒a → F₁ F X⇒a ⟨$⟩ x
          ; cong  = λ i≈j → F-resp-≈ F i≈j SE.refl
          }
        ; commute = λ {X} {Y} Y⇒X {f} {g} f≈g →
          let module SFY = Setoid (F₀ F Y) in
          let module SR = SetoidR (F₀ F Y) in
          SR.begin
             F₁ F (id ∘ f ∘ Y⇒X) ⟨$⟩ x   SR.≈⟨ F-resp-≈ F (identityˡ ○ ∘-resp-≈ˡ f≈g) (SE.refl {x}) ⟩
             F₁ F (g ∘ Y⇒X) ⟨$⟩ x        SR.≈⟨ homomorphism F SE.refl ⟩
             F₁ F Y⇒X ⟨$⟩ (F₁ F g ⟨$⟩ x)
           SR.∎
        }
      ; cong  = λ i≈j y≈z → F-resp-≈ F y≈z i≈j
      }
    ; inverse-of = record
      { left-inverse-of  = λ nat {x} {z} z≈y →
        let module S     = Setoid (F₀ F x) in
        S.trans (S.sym (commute nat z CE.refl))
                (cong (η nat x) (identityˡ ○ identityˡ ○ z≈y))
      ; right-inverse-of = λ Fa → identity F SE.refl
      }
    }
    where module SE = Setoid (F₀ F a)

  private
    -- in this bifunctor, a presheaf from Presheaves C goes from C to Setoids ℓ e,
    -- but the over Setoids has higher level than the hom setoids.
    Nat[Hom[C][-,c],F] : Bifunctor (Presheaves C) (Category.op C) (Setoids _ _)
    Nat[Hom[C][-,c],F] = Hom[ Presheaves C ][-,-] ∘F (Functor.op embed ∘F πʳ ※ πˡ)

    -- in this bifunctor, it needs to go from Presheaves which maps C to Setoids ℓ e,
    -- so the universe level needs to be lifted.
    FC : Bifunctor (Presheaves C) (Category.op C) (Setoids _ _)
    FC = LiftSetoids (o ⊔ suc ℓ ⊔ suc e) (o ⊔ ℓ) ∘F eval {C = Category.op C} {D = Setoids ℓ e}

    module yoneda-inverse {a} {F} = Inverse (yoneda-inverse a F)

  -- the two bifunctors above are naturally isomorphic.
  -- it is easy to show yoneda-inverse first then to yoneda.
  yoneda : NaturalIsomorphism Nat[Hom[C][-,c],F] FC
  yoneda = record
    { F⇒G = record
      { η       = λ where
        (F , A) → record
          { _⟨$⟩_ = λ α → lift (yoneda-inverse.to ⟨$⟩ α)
          ; cong  = λ i≈j → lift (i≈j CE.refl)
          }
      ; commute = λ where
        {_} {G , B} (α , f) {β} {γ} β≈γ → lift $ cong (η α B) (helper f β γ β≈γ)
      }
    ; F⇐G = record
      { η       = λ where
        (F , A) → record
          { _⟨$⟩_ = λ where
            (lift x) → yoneda-inverse.from ⟨$⟩ x
          ; cong  = λ where
            (lift i≈j) y≈z → F-resp-≈ F y≈z i≈j
          }
      ; commute = λ where
        (α , f) (lift eq) eq′ → helper′ α f eq eq′
      }
    ; iso = λ where
      (F , A) → record
        { isoˡ = λ {α β} i≈j {X} y≈z →
          let module S = Setoid (F₀ F X)
          in S.trans (yoneda-inverse.left-inverse-of α {x = X} y≈z) (i≈j CE.refl)
        ; isoʳ = λ where
          (lift eq) →
            let module S = Setoid (F₀ F A)
            in lift (S.trans (yoneda-inverse.right-inverse-of {F = F} _) eq)
        }
    }
    where helper : ∀ {F : Functor (Category.op C) (Setoids ℓ e)}
                     {A B : Obj} (f : B ⇒ A)
                     (β γ : NaturalTransformation Hom[ C ][-, A ] F) →
                   Setoid._≈_ (F₀ Nat[Hom[C][-,c],F] (F , A)) β γ →
                   Setoid._≈_ (F₀ F B) (η β B ⟨$⟩ f ∘ id) (F₁ F f ⟨$⟩ (η γ A ⟨$⟩ id))
          helper {F} {A} {B} f β γ β≈γ = S.begin
            η β B ⟨$⟩ f ∘ id          S.≈⟨ cong (η β B) (id-comm ○ (⟺ identityˡ)) ⟩
            η β B ⟨$⟩ id ∘ id ∘ f     S.≈⟨ commute β f CE.refl ⟩
            F₁ F f ⟨$⟩ (η β A ⟨$⟩ id) S.≈⟨ cong (F₁ F f) (β≈γ CE.refl) ⟩
            F₁ F f ⟨$⟩ (η γ A ⟨$⟩ id) S.∎
            where module S where
                    open Setoid (F₀ F B) public
                    open SetoidR (F₀ F B) public

          helper′ : ∀ {F G : Functor (Category.op C) (Setoids ℓ e)}
                      {A B Z : Obj}
                      {h i : Z ⇒ B}
                      {X Y : Setoid.Carrier (F₀ F A)}
                      (α : NaturalTransformation F G)
                      (f : B ⇒ A) →
                      Setoid._≈_ (F₀ F A) X Y →
                      h ≈ i →
                      Setoid._≈_ (F₀ G Z) (F₁ G h ⟨$⟩ (η α B ⟨$⟩ (F₁ F f ⟨$⟩ X)))
                                          (η α Z ⟨$⟩ (F₁ F (f ∘ i) ⟨$⟩ Y))
          helper′ {F} {G} {A} {B} {Z} {h} {i} {X} {Y} α f eq eq′ = S.begin
            F₁ G h ⟨$⟩ (η α B ⟨$⟩ (F₁ F f ⟨$⟩ X)) S.≈˘⟨ commute α h (S′.sym (cong (F₁ F f) eq)) ⟩
            η α Z ⟨$⟩ (F₁ F h ⟨$⟩ (F₁ F f ⟨$⟩ Y)) S.≈⟨ cong (η α Z) (F-resp-≈ F eq′ S′.refl) ⟩
            η α Z ⟨$⟩ (F₁ F i ⟨$⟩ (F₁ F f ⟨$⟩ Y)) S.≈˘⟨ cong (η α Z) (homomorphism F (Setoid.refl (F₀ F A))) ⟩
            η α Z ⟨$⟩ (F₁ F (f ∘ i) ⟨$⟩ Y)        S.∎
            where module S where
                    open Setoid (F₀ G Z) public
                    open SetoidR (F₀ G Z) public
                  module S′ = Setoid (F₀ F B)

  module yoneda = NaturalIsomorphism yoneda

  YoFull : Full embed
  YoFull {X} {Y} = record
      { to         = record
        { _⟨$⟩_ = Hom[A,C]⇒Hom[B,C]
        ; cong  = λ i≈j f≈g → ∘-resp-≈ i≈j f≈g
        }
      ; surjective = record
        { from             = record { _⟨$⟩_ = λ ε → η ε X ⟨$⟩ id ; cong = λ i≈j → i≈j CE.refl }
        ; right-inverse-of = λ ε {x} {z} {y} z≈y →
          begin
            (η ε X ⟨$⟩ id) ∘ z      ≈˘⟨ identityˡ ⟩
            id ∘ (η ε X ⟨$⟩ id) ∘ z ≈˘⟨ commute ε z CE.refl ⟩
            η ε x ⟨$⟩ id ∘ id ∘ z   ≈⟨ cong (η ε x) (identityˡ ○ identityˡ ○ z≈y) ⟩
            η ε x ⟨$⟩ y             ∎
        }
      }

  YoFaithful : Faithful embed
  YoFaithful _ _ pres-≈ = ⟺ identityʳ ○ pres-≈ {_} {id} CE.refl ○ identityʳ

  YoFullyFaithful : FullyFaithful embed
  YoFullyFaithful = YoFull , YoFaithful

  open Mor C

  yoneda-iso : ∀ {A B : Obj} → NaturalIsomorphism Hom[ C ][-, A ] Hom[ C ][-, B ] → A ≅ B
  yoneda-iso {A} {B} niso = record
    { from = ⇒.η A ⟨$⟩ id
    ; to   = ⇐.η B ⟨$⟩ id
    ; iso  = record
      { isoˡ = begin
        (⇐.η B ⟨$⟩ id) ∘ (⇒.η A ⟨$⟩ id)      ≈˘⟨ identityˡ ⟩
        id ∘ (⇐.η B ⟨$⟩ id) ∘ (⇒.η A ⟨$⟩ id) ≈⟨ B⇒A.left-inverse-of F⇐G refl ⟩
        ⇐.η A ⟨$⟩ (⇒.η A ⟨$⟩ id)             ≈⟨ isoX.isoˡ refl ⟩
        id                                   ∎
      ; isoʳ = begin
        (⇒.η A ⟨$⟩ id) ∘ (⇐.η B ⟨$⟩ id)      ≈˘⟨ identityˡ ⟩
        id ∘ (⇒.η A ⟨$⟩ id) ∘ (⇐.η B ⟨$⟩ id) ≈⟨ A⇒B.left-inverse-of F⇒G refl ⟩
        ⇒.η B ⟨$⟩ (⇐.η B ⟨$⟩ id)             ≈⟨ isoX.isoʳ refl ⟩
        id                                   ∎
      }
    }
    where open NaturalIsomorphism niso
          A⇒B = yoneda-inverse A (Functor.F₀ embed B)
          B⇒A = yoneda-inverse B (Functor.F₀ embed A)
          module A⇒B = Inverse A⇒B
          module B⇒A = Inverse B⇒A
          module isoX {X} = Mor.Iso (iso X)

  module _ {o′ ℓ′ e′} {D : Category o′ ℓ′ e′} where
    private
      module D = Category D
  
      module _ {F G : Functor D C} where
        private
          module F = Functor F
          module G = Functor G
          Hom[-,F-] : Bifunctor C.op D (Setoids ℓ e)
          Hom[-,F-] = Hom[ C ][-,-] ∘F (idF ⁂ F)
  
          Hom[-,G-] : Bifunctor C.op D (Setoids ℓ e)
          Hom[-,G-] = Hom[ C ][-,-] ∘F (idF ⁂ G)

        nat-appʳ : ∀ X → NaturalTransformation Hom[-,F-] Hom[-,G-] →  NaturalTransformation Hom[ C ][-, F.F₀ X ] Hom[ C ][-, G.F₀ X ]
        nat-appʳ X α = record
          { η       = λ Y → η α (Y , X)
          ; commute = λ {_ Y} f eq → cong (η α (Y , X)) (∘-resp-≈ˡ (⟺ F.identity)) ○ commute α (f , D.id) eq ○ ∘-resp-≈ˡ G.identity
          }
          
        transform : NaturalTransformation Hom[-,F-] Hom[-,G-] → NaturalTransformation F G
        transform α = record
          { η       = λ X → η α (F.F₀ X , X) ⟨$⟩ id
          ; commute = λ {X Y} f → begin
            (η α (F.F₀ Y , Y) ⟨$⟩ id) ∘ F.F₁ f      ≈˘⟨ identityˡ ⟩
            id ∘ (η α (F.F₀ Y , Y) ⟨$⟩ id) ∘ F.F₁ f ≈˘⟨ lower (yoneda.⇒.commute {Y = Hom[ C ][-, G.F₀ Y ] , _} (idN , F.F₁ f) {nat-appʳ Y α} {nat-appʳ Y α} (cong (η α _))) ⟩
            η α (F.F₀ X , Y) ⟨$⟩ F.F₁ f ∘ id        ≈⟨ cong (η α (F.F₀ X , Y)) (∘-resp-≈ʳ (⟺ identityˡ)) ⟩
            η α (F.F₀ X , Y) ⟨$⟩ F.F₁ f ∘ id ∘ id   ≈⟨ commute α (id , f) refl ⟩
            G.F₁ f ∘ (η α (F.F₀ X , X) ⟨$⟩ id) ∘ id ≈⟨ refl ⟩∘⟨ identityʳ ⟩
            G.F₁ f ∘ (η α (F.F₀ X , X) ⟨$⟩ id)      ∎
          }

    module _ (F G : Functor D C) where
      private
        module F = Functor F
        module G = Functor G
        Hom[-,F-] : Bifunctor C.op D (Setoids ℓ e)
        Hom[-,F-] = Hom[ C ][-,-] ∘F (idF ⁂ F)
  
        Hom[-,G-] : Bifunctor C.op D (Setoids ℓ e)
        Hom[-,G-] = Hom[ C ][-,-] ∘F (idF ⁂ G)
  
      yoneda-NI : NaturalIsomorphism Hom[-,F-] Hom[-,G-] → NaturalIsomorphism F G
      yoneda-NI ni = record
        { F⇒G = transform F⇒G
        ; F⇐G = transform F⇐G
        ; iso = λ X → record
          { isoˡ = begin
            (⇐.η (G.F₀ X , X) ⟨$⟩ id) ∘ (⇒.η (F.F₀ X , X) ⟨$⟩ id)      ≈˘⟨ identityˡ ⟩
            id ∘ (⇐.η (G.F₀ X , X) ⟨$⟩ id) ∘ (⇒.η (F.F₀ X , X) ⟨$⟩ id) ≈˘⟨ lower (yoneda.⇒.commute {Y = Hom[ C ][-, F.F₀ X ] , _} (idN , (⇒.η (F.F₀ X , X) ⟨$⟩ C.id))
                                                                                                   {nat-appʳ X F⇐G} {nat-appʳ X F⇐G} (cong (⇐.η _))) ⟩
            ⇐.η (F.F₀ X , X) ⟨$⟩ (⇒.η (F.F₀ X , X) ⟨$⟩ id) ∘ id        ≈⟨ cong (⇐.η _) identityʳ ⟩
            ⇐.η (F.F₀ X , X) ⟨$⟩ (⇒.η (F.F₀ X , X) ⟨$⟩ id)             ≈⟨ iso.isoˡ _ refl ⟩
            id                                                         ∎
          ; isoʳ = begin
            (⇒.η (F.F₀ X , X) ⟨$⟩ id) ∘ (⇐.η (G.F₀ X , X) ⟨$⟩ id)      ≈˘⟨ identityˡ ⟩
            id ∘ (⇒.η (F.F₀ X , X) ⟨$⟩ id) ∘ (⇐.η (G.F₀ X , X) ⟨$⟩ id) ≈˘⟨ lower (yoneda.⇒.commute {Y = Hom[ C ][-, G.F₀ X ] , _} (idN , (⇐.η (G.F₀ X , X) ⟨$⟩ C.id))
                                                                                                   {nat-appʳ X F⇒G} {nat-appʳ X F⇒G} (cong (⇒.η _))) ⟩
            ⇒.η (G.F₀ X , X) ⟨$⟩ (⇐.η (G.F₀ X , X) ⟨$⟩ id) ∘ id        ≈⟨ cong (⇒.η _) identityʳ ⟩
            ⇒.η (G.F₀ X , X) ⟨$⟩ (⇐.η (G.F₀ X , X) ⟨$⟩ id)             ≈⟨ iso.isoʳ _ refl ⟩
            id                                                         ∎
          }
        }
        where open NaturalIsomorphism ni

(*********************************************

Author: Jesús Héctor Domínguez Sánchez
June 2016

IMPORTANT: READ FILE "README.md" FIRST!!!!!!!!!!

This script is intended to be read side by side with the dissertation.
This is why the author decided to place all results in one big script
file instead of splitting the script into modules. Of course, there are
small differences on how the results on the dissertation are implemented
on this script, but the author hopes those differences are sufficiently
minimal so that a reader can still follow the script and the 
dissertation without trouble.

Modularity, reusability, or proof automation is not a concern here, as
this script is intended to be read by a person that is following the 
dissertation. This is the reason of why the author tried to use one
tactic per line inside proofs (and no automatic tactics, unless it is 
obvious by computation) so that each step in the proof can clearly be seen 
during execution of the script.

Of course, the author assumes the reader is already familiar with Coq.

*********************************************)

Require Import HoTT.

(*********************************
Chapter 2: Homotopy Type Theory
*********************************)

(* This part of the script includes results that are not directly available in the
HoTT library, so we need to prove them to be able to formalize Chapters 3 and 4 
later. 

I provide a quick reference of concepts available in the library.

Coq syntax                         Meaning

Empty                              Empty type

------------------------------------------------------------------------------

Unit                               Unit type

------------------------------------------------------------------------------

A * B                              Product type 

------------------------------------------------------------------------------

A + B                              Sum type

------------------------------------------------------------------------------

A -> B                             Non-dependent function type

------------------------------------------------------------------------------

forall x: A, P x                   Dependent function type

Alternative syntax 
for multiple inputs:

forall (x: A) (y: B), P x y

------------------------------------------------------------------------------

{x: A & P x}                       Depedent pair type

Alternative syntax:

{x: A | P x}

or:

exists x: A, P x

or for nested sigmas:

exists (x: A) (y: B), P x y

------------------------------------------------------------------------------

Type                               Universe at some level. It is left to Coq
                                   to assign the level.

------------------------------------------------------------------------------

Type@{i}                           Universe at level i. Here, i is a variable.
                                   
                                   Coq does not allow explicit assignment of
                                   levels (it is Coq the one that assigns the 
                                   levels), but we can at least refer to the 
                                   level assigned by Coq by using universe 
                                   variables like i.

------------------------------------------------------------------------------

a = b                              Identity type

Alternative syntax:

paths a b

------------------------------------------------------------------------------

nat                                Natural number type

------------------------------------------------------------------------------

f == g                             Pointwise identifiable functions.
                                   (See Definition 2.6.7)

                                   This is an abbreviation for type:
                                   forall x: A, f x = g x

------------------------------------------------------------------------------

IsEquiv e                          e is an equivalence. 
                                   (See Definition 2.6.10)

                                   The library uses the "half-adjoint" 
                                   definition of equivalence instead of the 
                                   "bi-invertible" map the the author used in 
                                   the dissertation. These two definitions are 
                                   equivalent (see Chapter 4 in the HoTT book)

------------------------------------------------------------------------------

A <~> B                            Equivalent types.
                                   (See Definition 2.6.16)

                                   This is an abbreviation for type: 
                                   {f: A -> B & IsEquiv f}, although the
                                   library uses a record to represent the 
                                   sigma.

------------------------------------------------------------------------------

A <-> B                            Logical equivalence.
                                   (See Definition 2.8.7)

                                   This is an abbreviation for type:
                                   (A -> B) * (B -> A)

------------------------------------------------------------------------------

~A                                 Not.

                                   This is an abbreviation for type:
                                   A -> Empty

------------------------------------------------------------------------------

tt                                 The unique term in Unit (the "star" term)

------------------------------------------------------------------------------

(a, b)                             Non-dependent pair

                                   Coq treats differently sigma types and
                                   product types, while in the dissertation
                                   product types are a special case of a sigma.
                                   This is just a technicality, since one can
                                   easily prove that types
                                   {_: A & B} and A * B are equivalent. 
                                   
------------------------------------------------------------------------------

(a ; b)                            Dependent pair 
                                   
                                   See note on the previous item.

------------------------------------------------------------------------------

fst p                              Projection functions for the product type

snd p

------------------------------------------------------------------------------

pr1 p                              Projection fuctions for the dependent pair
                                   type
pr2 p

Alternative syntax:

p.1

p.2

------------------------------------------------------------------------------

inl a                              Injection functions for the sum type

inr b

------------------------------------------------------------------------------

fun x: A => g x                    Function (lambda term)

Alternative syntax for
multiple inputs:

fun (x: A) (y: B) => g x y

------------------------------------------------------------------------------

idpath                             Trivial proof of identity (trivial loop)

Alternative syntax:

1

------------------------------------------------------------------------------

p^                                 Symmetry operator
                                   (See Lemma 2.5.60)

------------------------------------------------------------------------------

p @ q                              Transitivity operator
                                   (See Lemma 2.5.61)

------------------------------------------------------------------------------

transport P q a                    Transport operator
                                   (See Lemma 2.5.62)
Alternative syntax when
P is automatically inferred:

q # a

------------------------------------------------------------------------------

ap f p                             Application operator
                                   (Lemma 2.5.63)

------------------------------------------------------------------------------

apD f p                            Dependent application operator
                                   (Lemma 2.5.64)

------------------------------------------------------------------------------

e^-1                               Inverse of equivalence e
                                   (See Definition 2.6.12)

                                   It can be applied when type IsEquiv e is
                                   inhabited.

                                   The notation can also be used on terms 
                                   e: A <~> B

------------------------------------------------------------------------------

f o g                              Function composition
                                   (See Definition 2.5.12)

------------------------------------------------------------------------------

idmap                              Identity function

------------------------------------------------------------------------------

0                                  The natural number zero

Alternative syntax:

O (capital letter o)

------------------------------------------------------------------------------

S n                                Succesor of natural number n

Alternative syntax:

n.+1

*)


(*------ Section 2.6 ------- *)

(* Lemma 2.6.22

   Here, "functor_sigma" is the Sigma_map function of 
   Lemma 2.5.28  *)
Lemma sigmas_assoc {A: Type} (P: A -> Type) (Q: {w: A & P w} -> Type) :
 let T := fun w: A => {y: P w & Q (w ; y)} in
    exists (fib: forall y: {w: A & P w}, Q y -> T y.1),
         IsEquiv (functor_sigma pr1 fib).
Proof.
intro T.
transparent assert (fib: (forall y: {w: A & P w}, Q y -> T y.1)).
          (* Lemma 2.5.24 *)
 refine (sig_ind _ _ _ _).
 intros w y q.
 exact (y ; q).

exists fib.

transparent assert (inv: ({w: A & T w} -> {q: {w: A & P w} & Q q})).
 refine (sig_ind _ _ _ _).
 intros a b.
 exact ((a ; b.1) ; b.2). 

         (* Lemma 2.6.15 *)
refine (isequiv_adjointify (functor_sigma pr1 fib) inv _ _).

          (* Apply sigma induction twice *)
 refine (sig_ind _ _ _ _).
 intro a.
 refine (sig_ind _ _ _ _).
 intros c d. (* By computation *)
 reflexivity.

          (* Again, apply sigma induction *)
 refine (sig_ind _ _ _ _).
 refine (sig_ind _ _ _ _).
 intros a c d. (* By computation *)
 reflexivity.
Qed.

(*------ Section 2.8 ------- *)

(* There are two ways of representing subtypes. One is (as in the report):

Subtype S := S -> hProp

Another way is by using a sigma type:

Subtype S := {f: S -> Type & forall w: S, IsHProp (f w)}

First, we prove these two representations are equivalent (we will use this fact
later).
*)
Lemma subtype_repr_equiv (S: Type) : 
  (S -> hProp) <~> {f: S -> Type & forall w: S, IsHProp (f w)}.
Proof. (* By Lemma 2.6.17 we need to provide 
          two functions that are inverses of each other. *)
transparent assert (f1: ((S -> hProp) -> {f : S -> Type & forall w : S, IsHProp (f w)})).
 intro f. (* Here, "trunctype_type" and "istrunc_trunctype_type" are the accessor 
            functions for the first and second components on the sigma "hProp" 
            (which is encoded as a record type). *)
 refine (fun w: S => trunctype_type (f w) ; _).
 exact (fun w: S => istrunc_trunctype_type (f w)).

transparent assert (f2: ({f : S -> Type & forall w : S, IsHProp (f w)} -> (S -> hProp))).
 intro p. (* Here, BuildhProp is the constructor for the "hProp" record. *)
 exact (fun w: S => @BuildhProp (p.1 w) (p.2 w)).

refine (equiv_adjointify f1 f2 _ _).        
         (* By induction on sigma types *)
refine (sig_ind _ _ _ _).
intros w p. (* The rest is just computation *)
simpl. (* Notice this will use uniqueness of Pi-types *)
reflexivity.

intro f. (* Again, the rest is computation *)
simpl.
reflexivity.
Qed.

(* 
On this script I prefer the sigma representation for subtypes, because sigmas can be 
encoded as record types in Coq. And record types are more "reader-friendly" in the sense 
that records allow access to the components of a sigma by using accesor functions 
instead of nested projection functions as when using a sigma directly.

Also, records allow automatic coercion, so that when we have a subtype P: Subtype S
we can treat P automatically as a function P: S -> Type when necessary.
*)

Record Subtype (S: Type) := BuildSubtype {
 subtype_func  : S -> Type ;
 subtype_hprop : forall w: S, IsHProp (subtype_func w)
}.

(* Make some arguments implicit. *)
Arguments BuildSubtype {_} _ {_}.
Arguments subtype_func {_} _ _.
Arguments subtype_hprop {_} _ _ _ _.

(* Make automatically available the proof that any subtype is a predicate. *)
Global Existing Instance subtype_hprop.

(* Treat subtypes as if they were functions when necessary *)
Coercion subtype_func : Subtype >-> Funclass.

(* The Subtype record is equivalent to a Sigma type. *)
Lemma subtype_as_sigma (S: Type) : {f: S -> Type & forall x: S, IsHProp (f x)} 
                                     <~> Subtype S.
Proof. (* Just apply the "issig" tactic available in the HoTT library.
          This tactic transforms automatically between records and sigmas. *)
issig (@BuildSubtype S) (@subtype_func S) (@subtype_hprop S).
Defined.

(* If the underlying functions on two subtypes are equal, the subtypes are equal. *)
Lemma path_subtype {fext: Funext} {S: Type} {A B: Subtype S} : 
 subtype_func A = subtype_func B -> A = B.
Proof.
intro p. (* We prove that "A" and "B" seeing as elements on the Sigma are equal, since
            the Sigma and Record forms are the same. 

            "@paths A a b" is just another way of writing "a = b" but the "@paths"
            term allows specifying type A when Coq cannot deduce it from "a" and "b"
            alone, as in this case. *) 
assert ( @paths {f: S -> Type & forall x: S, IsHProp (f x)} 
                (subtype_func A ; subtype_hprop A) 
                (subtype_func B ; subtype_hprop B) 
       ) as p1. (* The second components on both pairs are terms on mere propositions. 
                   So, apply Lemma 2.8.14. *)
 refine (path_sigma_hprop _ _ _).
 exact p. (* Apply the equivalence of the record form and the Sigma form. *)
exact (ap (subtype_as_sigma S) p1).
Qed.

(* The subtype record is a set. *) 
Global Instance subtype_is_set {univ: Univalence} (S: Type) : IsHSet (Subtype S).
Proof. (* We know the record and sigma forms are equivalent, and equivalences preserve
          sets.
          So, apply Lemma 2.8.16 *)
refine (trunc_equiv' _ (subtype_as_sigma S)). (* But we know the sigma is equivalent to
          type "S -> hProp". *)
pose proof (subtype_repr_equiv S) as p1.
       (* By Lemma 2.8.18, "hProp" is a set, which
          implies that type "S -> hProp" is a set by the same Lemma.
          Also, sets are preserved under equivalences by 
          Lemma 2.8.16 *)
exact (trunc_equiv' (S -> hProp) p1).
Qed.

(* Lemma 2.8.20 

   We use "Subtype A" instead of "A -> hProp" as this will be more convenient 
   for us. *)
Lemma cantor {fext: Funext} (A: Type) : ~(Subtype A <~> A).
Proof.
intro e.
set (k := BuildSubtype (fun a: A => ~(e^-1 a a))).
pose proof (ap subtype_func (eissect e k))^ as p1.
set (delta := e k).
pose proof (happly p1) as p2.
change (k == e^-1 delta) in p2.
assert (forall C: Type, (~C) = C -> Empty) as f.
  intros C h1. (* equiv_path is function "idtoequiv" in the report *)
  pose proof (equiv_path _ _ h1) as g1.
  set (g3 := fun w: C => g1^-1 w w).
  exact (g3 (g1 g3)).
exact (f (e^-1 delta delta) (p2 delta)).
Qed.

(*------ Section 2.8.1 ------- *)

(* To state the propositional rezising axiom, we need to follow the strategy explained 
at "https://github.com/HoTT/HoTT/issues/783".

We will use a tag "PropResize" whenever we want to use 
the propositional resizing axiom, in the same way as tags "Funext" and "Univalence" 
are used in the HoTT library (I just copied the strategy from the HoTT library). *)

Monomorphic Axiom dummy_propresize_type : Type0.
Monomorphic Class PropResize := {dummy_propresize_value : dummy_propresize_type}.

(* In the report, we use GPRopR^-1 to resize a proposition into a lower
level. 

But here, since GPRopR is not being treated as an equivalence, usages of GPRopR on this
script will correspond to usages of GPRopR^-1 in the report. This is just a
mere technical issue due to limitations on Coq. However, this way of representing 
propositional resizing is not fundamentally different to the way it is done in HoTT.

So, this axiom corresponds to Lemma 2.8.22

This axiom is saying that any proposition can be sent to some type at some universe 
level that is independent of the level of the original proposition
(due to universe polymorphism in Coq).

So, this axiom is not relating the resized proposition with the original proposition.
We need another axiom to relate them. *)  
Axiom GPropR : forall `{PropResize} (A : Type) {Aprop : IsHProp A}, Type.

(* This axiom corresponds to Lemma 2.8.23

This is the axiom that relates the resized proposition to the original proposition,
by saying that the resized proposition is equivalent to the original proposition. *)
Axiom equiv_propresize : forall {propRes: PropResize} (P : Type) {Pprop : IsHProp P}, 
  P <~> GPropR P.

(* Lemma 2.8.24

Notice how in the report the conclusion is written as "(GPropR P)^-1 -> A". *)
Lemma prop_resize_rec {propRes: PropResize} {P A: Type} {Pprop: IsHProp P} (f: P -> A) : 
 GPropR P -> A.
Proof.
intro p.
exact (f ((equiv_propresize _)^-1 p)).
Qed.

(* This is another part of Lemma 2.8.22
which says that the resized proposition IS a proposition.

We mark it as a global instance so that Coq can use it in automatic proofs. *)
Global Instance resized_is_prop {propRes: PropResize} (A: Type) {HA: IsHProp A} :
 IsHProp (GPropR A).
Proof.
exact (trunc_equiv' A (equiv_propresize A)).
Qed.

(*------ Section 2.9 ------- *)

(* Definition 2.9.1 

   Again, we are using a record to represent a sigma.

   The difference between a record and a class is that classes allow us to register
   instances of the record (by using the commands "Global Instance" or "Local Instance")
   into a database, so that they can be used in automatic proofs. *)
Class FunctorStr (H: Type -> Type) := BuildFunctorStr {
map         : forall A B: Type@{i}, (A -> B) -> H A -> H B ;
id_preser   : forall A: Type@{i}, map A A idmap == idmap ;
comp_preser : forall (A B C: Type@{i}) (g: A -> B) (h: B -> C),
                map A C (h o g) == (map B C h) o (map A B g)
}.

(* Make some arguments implicit. *)
Arguments BuildFunctorStr {_} _ _ _.
Arguments map  _ {_} {_} {_} _ _.
Arguments id_preser _ {_} {_} _.
Arguments comp_preser _ {_} {_} {_} {_} _ _ _.

(* Lemma 2.9.3 *)
Lemma funct_preserve_equiv {fext: Funext} (H: Type -> Type) {FH: FunctorStr H} {A B: Type}
 (e: A -> B) {equiv: IsEquiv e} : IsEquiv (map H e).
Proof. (* Lemma 2.6.15 *)
refine (isequiv_adjointify (map H e) (map H e^-1) _ _).

intro b.
rewrite <- comp_preser. (* Function extensionality and
                           Lemma 2.6.14 *)
rewrite (path_forall _ _ (eisretr e)).
exact (id_preser H b).

intro a.
rewrite <- comp_preser. (* Function extensionality and
                           Lemma 2.6.14 *)
rewrite (path_forall _ _ (eissect e)).
exact (id_preser H a).
Qed.

(* Many Sigmas in the report consist of a type together with a property they need
to satisfy. For example, in the report an algebra was defined as:

Alg H := {A: Type & H A -> A}

It turns out that we can have greater flexibility in the code if we split these
definitions into two concepts: the property and those elements satisfying the property. 
For example, we can split "Alg H" into two types:

IsAlg A H := H A -> A
Alg H := {A: Type & IsAlg A H} 
 
We will follow this convention for almost all concepts on this script.
*)

(* Property part of Definition 2.9.4 *)
Class IsAlg (A: Type) (H: Type -> Type) {FH: FunctorStr H} := 
 In : H A -> A.

(* Make some arguments implicit *)
Arguments In _ {_} {_} {_} _.

(* Definition 2.9.4 encoded as a record. *)
Record Alg (H: Type -> Type) {FH: FunctorStr H} := BuildAlg {
 alg_obj         : Type ;
 alg_obj_is_alg  : IsAlg alg_obj H
}.

(* Make some arguments implicit *)
Arguments BuildAlg {_} {_} _ _.
Arguments alg_obj {_} {_} _.

(* Make automatically available the proof IsAlg. *)
Global Existing Instance alg_obj_is_alg.

(* Treat an algebra as if it were a type when necessary. *)
Coercion alg_obj : Alg >-> Sortclass.

(* Property part of Definition 2.9.5 *)
Class IsAlgMor {H: Type -> Type} {FH: FunctorStr H} {A B: Type} {AA: IsAlg A H} 
{AB: IsAlg B H} (f: A -> B) := 
 alg_mor : f o (In A) == (In B) o (map H f).

(* Make some arguments implicit *)
Arguments alg_mor {_} {_} {_} {_} {_} {_} _ {_} _.

(* Definition 2.9.5 encoded as a record *)
Record AlgMor {H: Type -> Type} {FH: FunctorStr H} (A B: Type) {AA: IsAlg A H} 
{AB: IsAlg B H} := BuildAlgMor {
  alg_mor_fun    : A -> B ;
  fun_is_alg_mor : IsAlgMor alg_mor_fun
}.

(* Make some arguments implicit. *)
Arguments BuildAlgMor {_} {_} {_} {_} {_} {_} _ _.
Arguments alg_mor_fun {_} {_} {_} {_} {_} {_} _ _.

(* Make automatically available the proof IsAlgMor *)
Global Existing Instance fun_is_alg_mor.

(* Treat an AlgMor as if it were a function, when necessary. *)
Coercion alg_mor_fun : AlgMor >-> Funclass.

(* The AlgMor record is equivalent to a Sigma type. *)
Lemma algmor_as_sigma {H: Type -> Type} {FH: FunctorStr H} (A B: Type) {AA: IsAlg A H} 
{AB: IsAlg B H} : {f: A -> B & IsAlgMor f} <~> AlgMor A B.
Proof. (* Just apply the "issig" tactic available in the HoTT library.
          This tactic transforms automatically between records and sigmas. *)
issig (@BuildAlgMor H FH A B AA AB) 
      (@alg_mor_fun H FH A B AA AB) 
      (@fun_is_alg_mor H FH A B AA AB).
Defined.

(* Lemma 2.9.6 *)
Lemma alg_mor_compose {H: Type -> Type} {FH: FunctorStr H} {A B C: Type} {AA: IsAlg A H}
{AB: IsAlg B H} {AC: IsAlg C H} (f: AlgMor A B) (g: AlgMor B C) : IsAlgMor (g o f).
Proof.
intro w.
rewrite comp_preser. 
rewrite <- (alg_mor g).
rewrite <- (alg_mor f).
reflexivity.
Qed.

(* Lemma 2.9.7 *)
Lemma id_alg_mor {H: Type -> Type} {FH: FunctorStr H} (A: Type) {AA: IsAlg A H} : 
 IsAlgMor idmap.
Proof.
intro w.
rewrite id_preser.
reflexivity.
Qed.

(*------ Section 2.10 ------- *)

(* Property part of Definition 2.10.1 *)
Class IsCoAlg (A: Type) (H: Type -> Type) {FH: FunctorStr H} := 
 Out : A -> H A.

(* Make some arguments implicit *)
Arguments Out _ {_} {_} {_} _.

(* Definition 2.10.1 encoded as a record. *)
Record CoAlg (H: Type -> Type) {FH: FunctorStr H} := BuildCoAlg {
 coalg_obj           : Type ;
 coalg_obj_is_coalg  : IsCoAlg coalg_obj H
}.

(* Make some arguments implicit *)
Arguments BuildCoAlg {_} {_} _ _.
Arguments coalg_obj {_} {_} _.

(* Make automatically available the proof IsCoAlg. *)
Global Existing Instance coalg_obj_is_coalg.

(* Treat a coalgebra as if it were a type when necessary. *)
Coercion coalg_obj : CoAlg >-> Sortclass.

(* Property part of Definition 2.10.2 *)
Class IsCoAlgMor {H: Type -> Type} {FH: FunctorStr H} {A B: Type} {CA: IsCoAlg A H} 
{CB: IsCoAlg B H} (f: A -> B) := 
 coalg_mor : (map H f) o (Out A) == (Out B) o f.

(* Make some arguments implicit *)
Arguments coalg_mor {_} {_} {_} {_} {_} {_} _ {_} _.

(* Definition 2.10.2 encoded as a record *)
Record CoAlgMor {H: Type -> Type} {FH: FunctorStr H} (A B: Type) {CA: IsCoAlg A H} 
{CB: IsCoAlg B H} := BuildCoAlgMor {
  coalg_mor_fun    : A -> B ;
  fun_is_coalg_mor : IsCoAlgMor coalg_mor_fun
}.

(* Make some arguments implicit. *)
Arguments BuildCoAlgMor {_} {_} {_} {_} {_} {_} _ _.
Arguments coalg_mor_fun {_} {_} {_} {_} {_} {_} _ _.

(* Make automatically available the proof IsAlgMor *)
Global Existing Instance fun_is_coalg_mor.

(* Treat an AlgMor as if it were a function, when necessary. *)
Coercion coalg_mor_fun : CoAlgMor >-> Funclass.

(* The CoAlgMor record is equivalent to a Sigma type. *)
Lemma coalgmor_as_sigma {H: Type -> Type} {FH: FunctorStr H} (A B: Type) 
{CA: IsCoAlg A H} {CB: IsCoAlg B H} : {f: A -> B & IsCoAlgMor f} <~> CoAlgMor A B.
Proof. (* Just apply the "issig" tactic available in the HoTT library.
          This tactic transforms automatically between records and sigmas. *)
issig (@BuildCoAlgMor H FH A B CA CB) 
      (@coalg_mor_fun H FH A B CA CB) 
      (@fun_is_coalg_mor H FH A B CA CB).
Defined.

(* Lemma 2.10.3 *)
Lemma coalg_mor_compose {H: Type -> Type} {FH: FunctorStr H} {A B C: Type} 
{CA: IsCoAlg A H} {CB: IsCoAlg B H} {CC: IsCoAlg C H} (f: CoAlgMor A B) 
(g: CoAlgMor B C) : IsCoAlgMor (g o f).
Proof.
intro w.
rewrite comp_preser. 
rewrite (coalg_mor f).
rewrite (coalg_mor g).
reflexivity.
Qed.

(* Lemma 2.10.4 *)
Lemma id_coalg_mor {H: Type -> Type} {FH: FunctorStr H} (A: Type) {CA: IsCoAlg A H} : 
 IsCoAlgMor idmap.
Proof.
intro w.
rewrite id_preser.
reflexivity.
Qed.

(*------ Section 2.11.1 ------- *)

(* (-1)-truncations are defined by "Trunc -1" in the HoTT library.
   The (-1)-truncation constructor is "tr". *)

(* Theorem 2.11.6 *)
Theorem choice_thm {A: Type} {B: A -> Type} (P: forall w: A, B w -> Type) :
 (forall w: A, exists a: B w, P w a) ->
     exists (g: forall y: A, B y),
         forall w: A, P w (g w).
Proof.
intro f.
set (g := fun y: A => (f y).1).
exists g.
intro w.
exact (f w).2.
Defined.

(* Lemma 2.11.8  *)
Lemma uni_choice {A: Type} (P: A -> Type) :
  (forall w: A, IsHProp (P w)) -> 
  (forall w: A, Trunc -1 (P w)) ->
        forall w: A, P w.
Proof.
intros h1 h2 w. (* Lemma 2.11.7

                   This is expressing that the (-1)-constructor
                   "tr: P w -> Trunc (-1) (P w)" is an equivalence. In the report
                   this is expressed as "P w <~> Trunc (-1) (P w)" *)
pose proof (isequiv_tr -1 (P w)).
pose proof (h2 w) as h.
exact (tr^-1 h).
Qed.

(* Definition 2.11.9 *)
Definition IsSurjection {A B: Type} (f: A -> B) :=
 forall b: B, Trunc -1 (exists a: A, f a = b).

(* Lemma 2.11.10 *)
Lemma idmap_is_surjection (A: Type) : @IsSurjection A A idmap.
Proof.
intro a.
exact (tr (a ; idpath)).
Qed.

(* Lemma 2.11.11 *)
Lemma surjections_compose {A B C: Type} {f: A -> B} {g: B -> C} (fsur: IsSurjection f)
(gsur: IsSurjection g) : IsSurjection (g o f).
Proof.
intro c.
cut (Trunc -1 (exists b: B, g b = c)). (* (-1)-recursion *)
refine (Trunc_rec _). (* Induction on sigmas *)
refine (sig_ind _ _ _ _).
intros b p1.
cut (Trunc -1 (exists a: A, f a = b)). (* (-1)-recursion *)
refine (Trunc_rec _). (* Induction on sigmas *)
refine (sig_ind _ _ _ _).
intros a p2.
pose proof (ap g p2) as p3.
exact (tr (a ; p3 @ p1)).
exact (fsur b).
exact (gsur c).
Qed.

(*------ Section 2.11.3 ------- *)

(* Coequalizers are written as "Coeq f g" in the HoTT library.
   The constructor is "coeq" *)
 
(* Lemma 2.11.17 
   
   This is the simplified induction principle for coequalizers. *)
Lemma coeq_ind_hprop {A B: Type} (f g: A -> B) (P: Coeq f g -> Type) 
{Pprop: forall x: Coeq f g, IsHProp (P x)} :
   (forall b: B, P (coeq b)) -> forall w: Coeq f g, P w.
Proof.
intro h. (* By the general induction principle for coequalizers 
            Definition 2.11.16 *)
refine (Coeq_ind P h _).
intro a. (* P is a mere proposition *)
apply path_ishprop.
Defined.

(* Lemma 2.11.19 *)
Lemma coeq_constructor_surjective {A B: Type} (f g: A -> B) :
 IsSurjection (@coeq _ _ f g).
Proof. (* By the simplified induction principle *)
refine (coeq_ind_hprop _ _ _ _).
intro a.
exact (tr (a ; idpath)).
Qed.

(*------ Section 2.11.4 ------- *)

(* Pushouts are written as "pushout f g" in the HoTT library.
   We need to do a little rewording so that definitions in the library look like the
definitions in the report. *)

(* These are the three constructors in Lemma 2.11.20.
   Function "push" in the HoTT Library is defined by using "coeq", the constructor for
   coequalizers. *)
Definition pushleft {A B C: Type} (g: A -> B) (f: A -> C) : B -> pushout g f := 
 push o inl.

Definition pushright {A B C: Type} (g: A -> B) (f: A -> C) : C -> pushout g f := 
 push o inr.

(* The higher constructor for pushouts is called "pp" in the library. We just reword it
   for our pushleft and pushright functions. *)
Definition pushiden {A B C: Type} (g: A -> B) (f: A -> C) (a: A) :
 pushleft g f (g a) = pushright g f (f a) := pp a.

(* Lemma 2.11.21 *)
Lemma pushout_ind_hprop {A B C: Type} (g: A -> B) (f: A -> C) 
  (P: pushout g f -> Type) {Pprop: forall x: pushout g f, IsHProp (P x)} :
         (forall b: B, P (pushleft g f b)) ->
         (forall c: C, P (pushright g f c)) -> 
                             forall w: pushout g f, P w.
Proof.
intros pushB pushC.
refine (pushout_ind g f P (sum_ind _ pushB pushC) _).
intro a. (* P is a mere proposition *)
apply path_ishprop.
Defined.

(* Lemma 2.11.22 
   
   This is just a rewording of the recursion principle available in the library. *)
Lemma pushout_rec' {A B C: Type} {g: A -> B} {f: A -> C} {D: Type} 
(h1: B -> D) (h2: C -> D) : 
    (forall a: A, h1 (g a) = h2 (f a)) -> (pushout g f) -> D.
Proof.
intro hyp.
refine (pushout_rec _ (sum_ind _ h1 h2) _).
exact hyp.
Defined.

(* First part of Lemma 2.11.23 *)
Lemma pushright_surjective {A B C: Type} (g: A -> B) (f: A -> C) :
 IsSurjection g -> IsSurjection (pushright g f).
Proof.
intros gsur.
refine (pushout_ind_hprop g f _ _ _).

intro b.
cut (Trunc -1 (exists y: A, g y = b)). (* (-1)-recursion *)
refine (Trunc_rec _). (* Induction on sigmas *)
refine (sig_ind _ _ _ _).
intros y p1.
pose proof (ap (pushleft g f) p1) as p2.
pose proof (pushiden g f y)^ as p3.
exact (tr (f y ; p3 @ p2)).
exact (gsur b).

intro c.
exact (tr (c ; idpath)).
Qed.

(* Second part of Lemma 2.11.23 *)
Lemma pushleft_surjective {A B C: Type} (g: A -> B) (f: A -> C) :
 IsSurjection f -> IsSurjection (pushleft g f).
Proof.
intros fsur.
refine (pushout_ind_hprop g f _ _ _).

intro b.
exact (tr (b ; idpath)).

intro c.
cut (Trunc -1 (exists y: A, f y = c)). (* (-1)-recursion *)
refine (Trunc_rec _). (* Induction on sigmas *)
refine (sig_ind _ _ _ _).
intros y p1.
pose proof (ap (pushright g f) p1) as p2.
pose proof (pushiden g f y) as p3.
exact (tr (g y ; p3 @ p2)).
exact (fsur c).
Qed.

(*------ Section 2.11.5 ------- *)

(* Quotients are written as "quotient R" in the library, where R is the mere relation.

   The constructor is "class_of" and the higher constructor is
   "related_classes_eq".

   The library already provides a simplified induction principle "quotient_ind_prop" 
   and a recursion principle "quotient_rec". *)

(* Lemma 2.11.27 *)
Lemma class_of_surjective {A: Type} (R: A -> A -> Type) 
 {rprop: forall x y: A, IsHProp (R x y)} : IsSurjection (class_of R).
Proof. (* By the simplified induction principle *)
refine (quotient_ind_prop R _ _).
intro a.
exact (tr (a ; idpath)).
Qed.

(****************************************************
Chapter 3: Complete lattices and fixpoints in HoTT
****************************************************)

(*------ Section 3.1 ------- *)

(* Definition 3.1.1

   Again, we are representing a sigma as a record.
*)
Class PosetStr (P: Type) := BuildPosetStr {
 brel_p     : P -> P -> Type ; (* It has a binary relation. *)
 refle_p    : forall w: P, brel_p w w ; (* Reflexivity. *)
 antisym_p  : forall w y: P, brel_p w y -> brel_p y w -> w = y ; (* Antisymmetry. *)
 trans_p    : forall w y z: P, brel_p w y -> brel_p y z -> brel_p w z ; (* Transitivity. *)
 dom_p_hset : IsHSet P ; (* The domain is a set. *)
 brel_hprop : forall w y: P, IsHProp (brel_p w y) (* The relation is a mere relation. *)
}.

(*
Notice that PosetStr could alternatively be defined as follows, which looks closer to the 
definition in the report.

Class PosetStr (P: hSet) := BuildPosetStr {
  brel_p     : P -> P -> hProp ; (* It has a mere binary relation. *)
  refle_p    : forall w: P, brel_p w w ; (* Reflexivity. *)
  antisym_p  : forall w y: P, brel_p w y -> brel_p y w -> w = y ; (* Antisymmetry. *)
  trans_p    : forall w y z: P, brel_p w y -> brel_p y z -> brel_p w z (* Transitivity. *)
}.

But I prefer the first version because this second version will rely on implicit coercion,
for example, when using brel_p.

I prefer to work on base types on records and add explicit declarations for whether or 
not a type is a set, or a proposition, or any other structure, as coercion hides whether 
or not a term can be used as a type.
*)

(* We make some arguments implicit. *)
Arguments BuildPosetStr {_} _ _ _ _ _ _.
Arguments brel_p {_} {_} _ _.
Arguments refle_p {_} {_} _.
Arguments antisym_p {_} {_} {_} {_} _ _.
Arguments trans_p {_} {_} {_} {_} {_} _ _.

(* Make automatically available the proofs that a poset is a set and its
relation is a mere relation. *)
Global Existing Instance dom_p_hset.
Global Existing Instance brel_hprop.

(* We introduce a notation for the binary relation. *)
Notation "a <= b" := (brel_p a b) (at level 70) : fix_point.

(* We open the fix_point scope to be able to use the "<=" notation. *)
Open Scope fix_point.

(* Example 3.1.3 *)
Example DualPoset (P: Type) {PS: PosetStr P} : PosetStr P.
Proof.
refine (BuildPosetStr (fun w y: P => y <= w) _ _ _ _ _).
exact refle_p.
intros w y h1 h2.
exact (antisym_p h2 h1).
intros w y z h1 h2.
exact (trans_p h2 h1).
Defined.

(* Example 3.1.4 *)
Example SubsetPoset {P: Type} {PS: PosetStr P} (S: Subtype P) : PosetStr {w: P & S w}.
Proof.
refine (BuildPosetStr (fun w y => w.1 <= y.1) _ _ _ _ _).
intro w.
exact (refle_p w.1).
intros w y h1 h2. (* Lemma 2.8.14 *)
refine (path_sigma_hprop _ _ _).
exact (antisym_p h1 h2).
intros w y z h1 h2.
exact (trans_p h1 h2).
Defined.

(* Example 3.1.5
The powertype poset: The poset of all subtypes of a type ordered by inclusion.
We need univalence to be able to prove antisymmetry. 

We declare it as a global instance so that this poset will be automatically
available to the proof assistant. *)
Global Instance PowertypePoset {univ: Univalence} (T: Type) : PosetStr (Subtype T).
Proof. (* For the inclusion relation, given "A" and "B" subtypes of "T", we say "A" is 
          contained in "B" if every element of "T" that is in "A" is also in "B". 
          This is expressed as "forall w: T, A w -> B w". *)
refine (BuildPosetStr (fun A B: Subtype T => forall w: T, A w -> B w) _ _ _ _ _).
intros A w.
exact (idmap).
intros A B h1 h2. (* To prove equality in the Subtype record, is the same as proving
                     equality on the underlying functions. *) 
refine (path_subtype _). (* So, we know "A" is contained in "B" and "B" is contained in "A".
                     First, apply function extensionality, 
                     see Section 2.6.1. *)
apply path_arrow.
intro w. (* Observe we have an equality between propositions, so it is enough to prove an 
            equivalence in the underlying types by univalence, 
            see Section 2.6.2. *)
refine (path_universe_uncurried _). (* To prove equivalence between mere propositions 
            it is enough to prove logical equivalence,
            Lemma 2.8.8. *)
refine (equiv_iff_hprop _ _).
exact (h1 w).
exact (h2 w).
intros A B C h1 h2. 
intros w h3. 
exact (h2 w (h1 w h3)).
Defined.

(* Definition 3.1.6 *)
Class IsMonotone {P Q: Type} {PS: PosetStr P} {QS: PosetStr Q} (f: P -> Q) := 
 mono_cond : forall w y: P, w <= y -> f w <= f y.

(* Make some arguments implicit. *)
Arguments mono_cond {_} {_} {_} {_} _ {_} {_} {_} _.

(* Lemma 3.1.8  *)
Definition DualPosetMonoFun {P: Type} {PS: PosetStr P} (f: P -> P) {mono: IsMonotone f} :
  @IsMonotone P P (DualPoset P) (DualPoset P) f.
Proof.
intros w y h1.
exact (@mono_cond _ _ _ _ f mono _ _ h1).
Defined.

(* ------- Section 3.2 ------- *)

(* Definition 3.2.1(i)  *)
Definition IsUpperBound {P: Type} {PS: PosetStr P} (w: P) (S: Subtype P) := 
 forall y: P, S y -> y <= w.

Arguments IsUpperBound {_} {_} _ _ /.

(* Definition 3.2.1(ii)   *)
Definition IsLowerBound {P: Type} {PS: PosetStr P} (w: P) (S: Subtype P) := 
 forall y: P, S y -> w <= y.

Arguments IsLowerBound {_} {_} _ _ /.

(* Definition 3.2.3(i)   *)
Record IsLUB {P: Type} {PS: PosetStr P} (w: P) (S: Subtype P) := BuildIsLUB {
upper_bound_pr       : IsUpperBound w S ;
least_upper_bound_pr : forall y: P, IsUpperBound y S -> w <= y
}.

(* Make some arguments implicit. *)
Arguments BuildIsLUB {_} {_} {_} {_} _ _.
Arguments upper_bound_pr {_} {_} {_} {_} _ _ _.
Arguments least_upper_bound_pr {_} {_} {_} {_} _ {_} _.

(* Definition 3.2.3(ii)    *)
Record IsGLB {P: Type} {PS: PosetStr P} (w: P) (S: Subtype P) := BuildIsGLB {
lower_bound_pr          : IsLowerBound w S ;
greatest_lower_bound_pr : forall y: P, IsLowerBound y S -> y <= w
}.

(* Make some arguments implicit. *)
Arguments BuildIsGLB {_} {_} {_} {_} _ _.
Arguments lower_bound_pr {_} {_} {_} {_} _ _ _.
Arguments greatest_lower_bound_pr {_} {_} {_} {_} _ {_} _.

(* Definition 3.2.5    *)
Class CLatticeStr (L: Type) {PS: PosetStr L} := BuildCLatticeStr {
 lubs_cl : Subtype L -> L ; (* Any subset has a least upper bound. *)
 glbs_cl : Subtype L -> L ; (* Any subset has a greatest lower bound. *)
 lubs_pr : forall S: Subtype L, IsLUB (lubs_cl S) S ; (* Proof that "lubs_cl"
                                                        outputs the least upper bound. *)
 glbs_pr : forall S: Subtype L, IsGLB (glbs_cl S) S (* Proof that "glbs_cl"
                                                      outputs the greatest lower bound. *)
}.

(* Make some arguments implicit. *)
Arguments BuildCLatticeStr {_} {_} _ _ _ _.
Arguments lubs_cl {_} {_} {_} _.
Arguments glbs_cl {_} {_} {_} _.
Arguments lubs_pr {_} {_} {_} _.
Arguments glbs_pr {_} {_} {_} _.

(* We declare some notation for lubs and glbs in a complete lattice. 
We want these notations to bind with higher precedence than "<=". *)
Notation "\/ S" := (lubs_cl S) (at level 65) : fix_point.
Notation "/\ S" := (glbs_cl S) (at level 65) : fix_point.

(* Example 3.2.7    *)
Definition DualCLattice (L: Type) {PS: PosetStr L} {LS: CLatticeStr L} : 
 @CLatticeStr L (DualPoset L).
Proof. (* We simply interchange the functions "glbs_cl" and "lubs_cl". *)
refine (BuildCLatticeStr glbs_cl lubs_cl _ _).
intro S.
refine (BuildIsLUB _ _).
simpl.
intros y h1.
exact (lower_bound_pr (glbs_pr S) y h1).
simpl.
intros y h1.
exact (greatest_lower_bound_pr (glbs_pr S) h1).
intro S.
refine (BuildIsGLB _ _).
simpl.
intros y p1.
exact (upper_bound_pr (lubs_pr S) y p1).
simpl.
intros y p1.
exact (least_upper_bound_pr (lubs_pr S) p1).
Defined.

(* Example 3.2.8

Univalence is required, since it was used to define the poset. 

Also, we require propositional resizing since we are making an impredicative definition
when constructing the least upper bound and greatest lower bound functions.

Coq automatically finds the poset structure for "Subtype T" we previously constructed. 
*)
Global Instance PowertypeCLattice {univ: Univalence} {pres: PropResize} (T: Type) : 
 CLatticeStr (Subtype T).
Proof. (* Introduce an abbreviation. *) 
set (P := Subtype T). 
            (* Supremum function *)
set (fun F: Subtype P =>
            (BuildSubtype 
                 (fun w: T => 
                     GPropR (Trunc -1 (exists B: P, F B * B w))
                 )
            )
    ) as s. 
            (* Infimum function *)
set (fun F: Subtype P => 
            (BuildSubtype 
                 (fun w: T => 
                     GPropR (forall B: P, F B -> B w)
                 )
            )
    ) as i.
refine (BuildCLatticeStr s i _ _).
        (* So, given a family "F", we need to prove that our construction is the least
           upper bound. *)
intro F.
refine (BuildIsLUB _ _).

        (* First, we prove that our construction is an upper bound for the family "F". *)
 intros E h1. (* Now, we show "E" is contained in the construction. *) 
 intros w p1. 
 simpl. (* To prove something about a resized proposition is the same as proving 
           the property for the equivalent unresized proposition.
           See Lemma 2.8.23 *)
 refine (equiv_propresize _ _).
 exact (tr (E ; (h1, p1))).

         (* Now, given an upper bound "E" for the family "F", we need to prove that our
            construction is contained (i.e. is smaller) in "E". *)
 intros E h1. 
 intros w.
 simpl. (* Lemma 2.8.24 *)
 refine (prop_resize_rec _). 
        (* Corollary 2.11.4  *)
 refine (Trunc_rec _). (* Lemma 2.5.25 *)
 refine (sig_rec _ _ _ _).
 intro B. (* Lemma 2.5.25 *)
 refine (prod_ind _ _).
 intros p1 p2. 
 exact (h1 B p1 w p2).
 
        (* The arguments for the case of the greatest lower bound for a family "F" 
           are similar. *)
intro F.
refine (BuildIsGLB _ _).

 intros E h1.
 intros w. 
 simpl. (* Lemma 2.8.24 *)
 refine (prop_resize_rec _).
 intro p1.
 exact (p1 E h1).

 intros E h1.
 intros w p1.
 simpl. (* Lemma 2.8.23 *)
 refine (equiv_propresize _ _).
 intros B p2.
 exact (h1 B p2 w p1).
Defined.

(* Definition 3.2.10 
We also introduce notation for binary lubs and glbs, also called joins and meets. 
These notations need to bind with lower precedence than "/\" and "\/", but with higher
precedence than "<=". *)
Notation "a '\./' b" := (\/ (BuildSubtype (fun w => Trunc -1 ((w = a) + (w = b)))))
                           (at level 67) : fix_point.
Notation "a '/.\' b" := (/\ (BuildSubtype (fun w => Trunc -1 ((w = a) + (w = b))))) 
                           (at level 66) : fix_point.

(* Lemma 3.2.11(i) *) 
Lemma meet_lower_bound_1 {L: Type} {PS: PosetStr L} {LS: CLatticeStr L} (a b: L) : 
 a /.\ b <= a.
Proof.
refine (lower_bound_pr (glbs_pr _) a _).
simpl.
exact (tr (inl idpath)).
Qed.

(* Lemma 3.2.11(ii) *)
Lemma join_upper_bound_1 {L: Type} {PS: PosetStr L} {LS: CLatticeStr L} (a b: L) : 
 a <= a \./ b.
Proof. (* By previous lemma, but using the dual lattice. *)
exact (@meet_lower_bound_1 _ _ (DualCLattice L) a b).
Qed.

(* Lemma 3.2.11(iii) *)
Lemma meet_lower_bound_2 {L: Type} {PS: PosetStr L} {LS: CLatticeStr L} (a b: L) : 
 a /.\ b <= b.
Proof.
refine (lower_bound_pr (glbs_pr _) b _).
simpl.
exact (tr (inr idpath)).
Qed.

(* Lemma 3.2.11(iv) *)
Lemma join_upper_bound_2 {L: Type} {PS: PosetStr L} {LS: CLatticeStr L} (a b: L) : 
 b <= a \./ b.
Proof. (* By previous lemma, but using the dual lattice. *)
exact (@meet_lower_bound_2 _ _ (DualCLattice L) a b).
Qed.

(* Lemma 3.2.12(i) *)
Lemma leq_meet_preservation {L: Type} {PS: PosetStr L} {LS: CLatticeStr L} {a b c d: L} : 
 a <= c -> b <= d -> a /.\ b <= c /.\ d.
Proof.
set (G := BuildSubtype (fun w: L => Trunc -1 ((w = c) + (w = d)))).
intros h1 h2. 

assert (IsLowerBound (a /.\ b) G) as t.
 intro w. (* Corollary 2.11.4 *)
 refine (Trunc_rec _). (* Lemma 2.5.37 *)
 refine (sum_ind _ _ _).
 intro p. (* Lemma 3.2.11(i) *)
 pose proof (meet_lower_bound_1 a b) as t1. (* Transitivity *)
 pose proof (trans_p t1 h1) as t2.
 exact (p^ # t2).
 intro p. (* Lemma 3.2.11(iii) *)
 pose proof (meet_lower_bound_2 a b) as t1. (* Transitivity *)
 pose proof (trans_p t1 h2) as t2.
 exact (p^ # t2). 

exact (greatest_lower_bound_pr (glbs_pr G) t).
Qed.

(* Lemma 3.2.12(ii) *)
Lemma leq_join_preservation {L: Type} {PS: PosetStr L} {LS: CLatticeStr L} {a b c d: L} : 
 a <= c -> b <= d -> a \./ b <= c \./ d.
Proof.
intros h1 h2. (* By previous lemma, but using the dual lattice. *)
exact (@leq_meet_preservation _ _ (DualCLattice L) _ _ _ _ h1 h2).
Qed.

(* Lemma 3.2.13(i) *)
Lemma meet_idempotent {L: Type} {PS: PosetStr L} {LS: CLatticeStr L} (a: L) : a /.\ a = a.
Proof. 
set (G := BuildSubtype (fun w: L => Trunc -1 ((w = a) + (w = a)))).
pose proof (meet_lower_bound_1 a a) as t1.
refine (antisym_p t1 _).

assert (IsLowerBound a G) as t.
 intro w. (* Corollary 2.11.4 *)
 refine (Trunc_rec _). (* Lemma 2.5.37 *)
 refine (sum_ind _ _ _).
 intro p. (* Reflexivity *)
 pose proof (refle_p a) as r1.
 exact (p^ # r1).
 intro p.
 pose proof (refle_p a) as r1.
 exact (p^ # r1).
 
exact (greatest_lower_bound_pr (glbs_pr G) t).
Qed.

(* Lemma 3.2.13(ii) *)
Lemma join_idempotent {L: Type} {PS: PosetStr L} {LS: CLatticeStr L} (a: L) : a \./ a = a.
Proof. (* By previous lemma, but using the dual lattice. *)
exact (@meet_idempotent _ _ (DualCLattice L) a).
Qed.

(* Corollary 3.2.14(i) *)
Corollary leq_meet_left_constant_preservation {L: Type} {PS: PosetStr L} 
{LS: CLatticeStr L} {a c d: L} : a <= c -> a <= d -> a <= c /.\ d.
Proof.
intros h1 h2. (* Lemma 3.2.12(i) *)
pose proof (leq_meet_preservation h1 h2) as p2. 
              (* Lemma 3.2.13(i) *)
pose proof (meet_idempotent a) as q.
exact (transport (fun x => x <= c /.\ d) q p2).
Qed.

(* Corollary 3.2.14(ii) *)
Corollary leq_meet_right_constant_preservation {L: Type} {PS: PosetStr L} 
{LS: CLatticeStr L} {a b c: L} : a <= c -> b <= c -> a /.\ b <= c.
Proof.
intros h1 h2. (* Lemma 3.2.11(i) *)
pose proof (meet_lower_bound_1 a b) as p1.
exact (trans_p p1 h1).
Qed.

(* Corollary 3.2.14(iii) *)
Corollary leq_join_left_constant_preservation {L: Type} {PS: PosetStr L} 
{LS: CLatticeStr L} {a c d: L} : a <= c -> a <= d -> a <= c \./ d.
Proof.
intros h1 h2. (* Lemma 3.2.11(ii) *)
pose proof (join_upper_bound_1 c d) as p1.
exact (trans_p h1 p1).
Qed.

(* Corollary 3.2.14(iv) *)
Corollary leq_join_right_constant_preservation {L: Type} {PS: PosetStr L} 
{LS: CLatticeStr L} {a b c: L} : a <= c -> b <= c -> a \./ b <= c.
Proof.
intros h1 h2. (* Lemma 3.2.12(ii) *)
pose proof (leq_join_preservation h1 h2) as p2. 
              (* Lemma 3.2.13(ii) *)
pose proof (join_idempotent c) as q.
exact (transport (fun x => a \./ b <= x) q p2).
Qed.

(* ------- Section 3.3 ------- *)

(* Definition 3.3.1(i)  *)
Definition IsPrefixpoint {P: Type} {PS: PosetStr P} (w: P) (f: P -> P) :=
 f w <= w.

Arguments IsPrefixpoint {_} {_} _ _ /.

(* Definition 3.3.1(ii)  *)
Definition IsPostfixpoint {P: Type} {PS: PosetStr P} (w: P) (f: P -> P) :=
 w <= f w.

Arguments IsPostfixpoint {_} {_} _ _ /.

(* Definition 3.3.1(iii)  *)
Definition IsFixpoint {P: Type} {PS: PosetStr P} (w: P) (f: P -> P) :=
 f w = w.

Arguments IsFixpoint {_} {_} _ _ /.

(* Lemma 3.3.3    *) 
Lemma fixp_pre_post_equiv {P: Type} {PS: PosetStr P} (w: P) (f: P -> P) : 
 IsFixpoint w f <~> (IsPrefixpoint w f * IsPostfixpoint w f).
Proof. (* To prove equivalence between mere propositions it is enough to prove logical
          equivalence. 
          Lemma 2.8.8 *)
refine (equiv_iff_hprop _ _).

intro h. (* Reflexivity *)
pose proof (refle_p (f w)) as t.
pose proof (transport (fun z => f w <= z) h t) as t1.
pose proof (transport (fun z => z <= f w) h t) as t2.
exact (t1, t2).

           (* Lemma 2.5.25 *)
refine (prod_rect _ _).
intros h1 h2. (* Antisymmetry *)
exact (antisym_p h1 h2).
Qed.

(* Definition 3.3.4(i)    *)
Record IsLFP {P: Type} {PS: PosetStr P} (w: P) (f: P -> P) := BuildIsLFP {
fixpoint_l_pr     : IsFixpoint w f ;
least_fixpoint_pr : forall y: P, IsFixpoint y f -> w <= y
}.

(* Make some arguments implicit. *)
Arguments BuildIsLFP {_} {_} {_} {_} _ _.
Arguments fixpoint_l_pr {_} {_} {_} {_} _.
Arguments least_fixpoint_pr {_} {_} {_} {_} _ {_} _.

(* Definition 3.3.4(ii)    *)
Record IsGFP {P: Type} {PS: PosetStr P} (w: P) (f: P -> P) := BuildIsGFP {
fixpoint_g_pr        : IsFixpoint w f ;
greatest_fixpoint_pr : forall y: P, IsFixpoint y f -> y <= w
}.

(* Make some arguments implicit. *)
Arguments BuildIsGFP {_} {_} {_} {_} _ _.
Arguments fixpoint_g_pr {_} {_} {_} {_} _.
Arguments greatest_fixpoint_pr {_} {_} {_} {_} _ {_} _.

(* Lemma 3.3.6(i)    *)
Lemma knaster_tarski_lemma_lfp {L: Type} {PS: PosetStr L} {LS: CLatticeStr L} (f: L -> L) 
 {mono: IsMonotone f} : exists lfp: L, IsLFP lfp f.
Proof. 
         (* Let "P" be the set of all prefixpoints of "f". *) 
set (P := BuildSubtype (fun x: L => IsPrefixpoint x f)).
set (lfp := /\ P). 
refine (lfp ; _).

assert (IsLowerBound (f lfp) P) as p3.
 intros w h1.
 pose proof (lower_bound_pr (glbs_pr P) w h1) as p1.
 pose proof (mono_cond f p1) as p2.
 exact (trans_p p2 h1).

refine (BuildIsLFP _ _).
pose proof (greatest_lower_bound_pr (glbs_pr P) p3) as p4.
refine (antisym_p p4 _).
change (lfp <= f lfp).
pose proof (mono_cond f p4) as p5.
change (IsPrefixpoint (f lfp) f) in p5.
exact (lower_bound_pr (glbs_pr P) (f lfp) p5).

intros y h.
pose proof (refle_p y) as p6.
pose proof (transport (fun x => x <= y) h^ p6) as p7.
change (P y) in p7.
exact (lower_bound_pr (glbs_pr P) y p7).
Defined.

(* Lemma 3.3.6(ii)    *)
Lemma knaster_tarski_lemma_gfp {L: Type} {PS: PosetStr L} {LS: CLatticeStr L} (f: L -> L) 
 {mono: IsMonotone f} : exists gfp: L, IsGFP gfp f.
Proof. (* We know "f" is also monotone in the dual poset. So,
          it has a least fixpoint. *)
pose proof (@knaster_tarski_lemma_lfp _ _ (DualCLattice L) f (DualPosetMonoFun f)) as h. 
destruct h as [c p1].
exists c.
refine (BuildIsGFP _ _).
exact (fixpoint_l_pr p1).
intros y h.
exact (least_fixpoint_pr p1 h).
Defined.

(* We introduce some access functions for the components of the Knaster-Tarski Lemma. *)

Definition Lfp {L: Type} {PS: PosetStr L} {LS: CLatticeStr L} (f: L -> L) 
 {mono: IsMonotone f} := (knaster_tarski_lemma_lfp f).1.

Arguments Lfp {_} {_} {_} _ {_} /.

Definition Lfp_pr {L: Type} {PS: PosetStr L} {LS: CLatticeStr L} (f: L -> L) 
 {mono: IsMonotone f} : IsLFP (Lfp f) f := (knaster_tarski_lemma_lfp f).2.

Arguments Lfp_pr {_} {_} {_} _ {_} /.

Definition Gfp {L: Type} {PS: PosetStr L} {LS: CLatticeStr L} (f: L -> L) 
 {mono: IsMonotone f} := (knaster_tarski_lemma_gfp f).1.

Arguments Gfp {_} {_} {_} _ {_} /.

Definition Gfp_pr {L: Type} {PS: PosetStr L} {LS: CLatticeStr L} (f: L -> L) 
 {mono: IsMonotone f} : IsGFP (Gfp f) f := (knaster_tarski_lemma_gfp f).2.

Arguments Gfp_pr {_} {_} {_} _ {_} /.

(* ------- Section 3.4 ------- *)

(* Corollary 3.4.1   *)
Corollary c_induction {L: Type} {PS: PosetStr L} {LS: CLatticeStr L} (f: L -> L) 
 {mono: IsMonotone f} {w: L} : f w <= w -> Lfp f <= w.
Proof.
intro h. (* The least fixpoint of "f" is the greatest lower bound of all pre-fixpoints of
            "f", and "w" is a prefixpoint of "f". *)
set (P := BuildSubtype (fun y: L => IsPrefixpoint y f)).
exact (lower_bound_pr (glbs_pr P) w h).
Qed.

(* Corollary 3.4.2    *)
Corollary c_ext_induction {L: Type} {PS: PosetStr L} {LS: CLatticeStr L} (f: L -> L) 
 {mono: IsMonotone f} {w: L} : f (Lfp f /.\ w) <= w -> Lfp f <= w.
Proof.
intro h. (* Lemma 3.2.11(i) *)
pose proof (meet_lower_bound_1 (Lfp f) w) as t1.
pose proof (mono_cond f t1) as t2.
pose proof (fixpoint_l_pr (Lfp_pr f)) as t3.
pose proof (transport (fun z => f (Lfp f /.\ w) <= z) t3 t2) as t4.
                 (* Corollary 3.2.14(i) *)
pose proof (leq_meet_left_constant_preservation t4 h) as t5.
pose proof (c_induction f t5) as t6. (* Lemma 3.2.11(iii) *)
pose proof (meet_lower_bound_2 (Lfp f) w) as t7.
exact (trans_p t6 t7).
Qed.

(* Corollary 3.4.3     *)
Corollary m_induction_mono {L: Type} {PS: PosetStr L} {LS: CLatticeStr L} (f: L -> L)
 {mono: IsMonotone f} {w: L} : (forall y: L, y <= w -> f y <= w) -> Lfp f <= w.
Proof. 
intro h. (* If we can prove "f w <= w" then by conventional induction we 
            get the result. *)
pose proof (h w (refle_p w)) as t1. 
exact (c_induction f t1).
Qed.

(* Corollary 3.4.4    *)
Corollary m_ext_induction_mono {L: Type} {PS: PosetStr L} {LS: CLatticeStr L} (f: L -> L)
 {mono: IsMonotone f} {w: L} : 
   (forall y: L, y <= Lfp f -> y <= w -> f y <= w) -> Lfp f <= w.
Proof. 
intro h.  (* Lemma 3.2.11(i) *)
pose proof (meet_lower_bound_1 (Lfp f) w) as t1.
          (* Lemma 3.2.11(iii) *)
pose proof (meet_lower_bound_2 (Lfp f) w) as t2.
pose proof (h (Lfp f /.\ w) t1 t2) as t3.
exact (c_ext_induction f t3).
Qed.

(* Corollary 3.4.5   *)
Corollary c_coinduction {L: Type} {PS: PosetStr L} {LS: CLatticeStr L} (f: L -> L) 
 {mono: IsMonotone f} {w: L} : w <= f w -> w <= Gfp f.
Proof. 
intro h. (* We use the dual lattice on the induction principle. Observe we need to 
            give the proof that "f" is monotone in the dual poset. *)
exact (@c_induction _ _ (DualCLattice L) f (DualPosetMonoFun f) w h).
Qed.

(* Corollary 3.4.6  *)
Corollary c_ext_coinduction {L: Type} {PS: PosetStr L} {LS: CLatticeStr L} (f: L -> L) 
 {mono: IsMonotone f} {w: L} : w <= f (Gfp f \./ w) -> w <= Gfp f.
Proof.
intro h. (* We use duality again. *)
exact (@c_ext_induction _ _ (DualCLattice L) f (DualPosetMonoFun f) w h).
Qed.

(* Corollary 3.4.7 *)
Corollary m_coinduction_mono {L: Type} {PS: PosetStr L} {LS: CLatticeStr L} (f: L -> L)
 {mono: IsMonotone f} {w: L} : (forall y: L, w <= y -> w <= f y) -> w <= Gfp f.
Proof. (* By dualizing Mendler induction. *)
exact (@m_induction_mono _ _ (DualCLattice L) f (DualPosetMonoFun f) _).
Qed.

(* Corollary 3.4.8 *)
Corollary m_ext_coinduction_mono {L: Type} {PS: PosetStr L} {LS: CLatticeStr L} (f: L -> L)
 {mono: IsMonotone f} {w: L} : 
    (forall y: L, Gfp f <= y -> w <= y -> w <= f y) -> w <= Gfp f.
Proof. (* By dualizing extended Mendler induction. *)
exact (@m_ext_induction_mono _ _ (DualCLattice L) f (DualPosetMonoFun f) _).
Qed.

(****************************************
Chapter 4: Constructing types in HoTT
****************************************)

(*----- Section 4.2 ----------*)

(*----- Subsection 4.2.1 --------*)

(* Property part of Definition 4.2.1 *)
Class IsCone (C: Type) {M: Type} (F: M -> Type) :=
 cone_diag : forall i: M, C -> F i.

(* Make some arguments implicit *)
Arguments cone_diag _ {_} {_} {_} _ _.

(* Definition 4.2.1 encoded as a record. *)
Record Cone {M: Type} (F: M -> Type) := BuildCone {
 cone_obj         : Type ;
 cone_obj_is_cone : IsCone cone_obj F
}.

(* Make some arguments implicit *)
Arguments BuildCone {_} {_} _ _.

(* Make automatically available the proof that it is a cone *)
Global Existing Instance cone_obj_is_cone.

(* Treat a cone as a type when necessary *)
Coercion cone_obj : Cone >-> Sortclass.

(* Definition 4.2.2 encoded as a record *)
Record WLimit {M: Type} (F: M -> Type) := BuildWLimit {
 wlimit_obj         : Type ;
 wlimit_obj_is_cone : IsCone wlimit_obj F ;
 wlimit_diag        : forall Y: Cone F, exists h: Y -> wlimit_obj,
                         forall (i: M) (w: Y), 
                               cone_diag Y i w = cone_diag wlimit_obj i (h w)
}.

(* Make some arguments implicit *)
Arguments BuildWLimit {_} {_} _ _ _.
Arguments wlimit_diag {_} {_} _ _.

(* Make automatically available the proof that a weak limit is a cone *)
Global Existing Instance wlimit_obj_is_cone.

(* Treat a weak limit as a type, when necessary *)
Coercion wlimit_obj : WLimit >-> Sortclass.

(* Lemma 4.2.3 *)
Lemma family_has_wlimit {M: Type} (F: M -> Type) : WLimit F.
Proof.
set (L := forall i: M, F i).
set (f := fun (i: M) (j: L) => j i).
refine (BuildWLimit L f _).

intro Y.
exists (fun (y: Y) (i: M) => cone_diag Y i y).
intros i w.
reflexivity.
Defined.

(* Property part of Definition 4.2.4
   
   Notice we are reusing "IsAlg A H", just adding the fact that A is a set. *) 
Class IsSAlg (A: Type) (H: Type -> Type) {FH: FunctorStr H} := BuildIsSAlg {
 dom_is_alg : IsAlg A H ;
 dom_is_set : IsHSet A
}.

(* Make some arguments implicit *)
Arguments BuildIsSAlg {_} {_} {_} _ _.

(* Make automatically available the proof that A is a set *)
Global Existing Instance dom_is_set.

(* Make automatically available the proof that A is an algebra *)
Global Existing Instance dom_is_alg.

(* Definition 4.2.4 encoded as a record. *)
Record SAlg (H: Type -> Type) {FH: FunctorStr H} := BuildSAlg {
 salg_obj         : Type ;
 salg_obj_is_salg : IsSAlg salg_obj H
}.

(* Make some arguments implicit *)
Arguments BuildSAlg {_} {_} _ _.
Arguments salg_obj {_} {_} _.

(* Make automatically available the proof that it is a set algebra *)
Global Existing Instance salg_obj_is_salg.

(* Coerce SAlgs as if they were types whenever necessary *)
Coercion salg_obj : SAlg >-> Sortclass.

(* Property part of Definition 4.2.5(i)  

   Notice the use of "let enforce_lt := Type@{l} : Type@{k} in", this will add the 
   restriction "l < k" into the definition, so that the universe level of B in the 
   universal quantification will be strictly lower than the universe level of W.
   *) 
Class IsLLWinSAlg (W: Type@{k}) (H: Type -> Type) {FH: FunctorStr H} := BuildIsLLWinSAlg { 
 llwinit_is_salg : IsSAlg W H ;
 llwinit_alg_pr  : let enforce_lt := Type@{l} : Type@{k} in
                       forall (B: Type@{l}) (WBS: IsSAlg B H), AlgMor W B
}.

(* Make some arguments implicit *)
Arguments BuildIsLLWinSAlg {_} {_} {_} _ _.
Arguments llwinit_alg_pr _ {_} {_} {_} _ {_}.

(* Make automatically available the proof that a llWinSAlg is a set algebra *)
Global Existing Instance llwinit_is_salg.

(* Definition 4.2.5(i)   *)
Record LLWinSAlg (H: Type -> Type) {FH: FunctorStr H} := BuildLLWinSAlg {
 llwinit_obj             : Type ;
 llwinit_obj_is_winitalg : IsLLWinSAlg llwinit_obj H
}.

(* Make some arguments implicit *)
Arguments BuildLLWinSAlg {_} {_} _ _.

(* Make automatically available its component proofs *)
Global Existing Instance llwinit_obj_is_winitalg.

(* Coerce a LLWinSAlg into a type when necessary *)
Coercion llwinit_obj : LLWinSAlg >-> Sortclass.

(* Property part of Definition 4.2.5(ii) 

   Notice that the universe level of B in the universal quantification must be the
   same as the universe level of W.  *) 
Class IsWinSAlg (W: Type@{k}) (H: Type -> Type) {FH: FunctorStr H} := BuildIsWinSAlg { 
 winit_is_salg : IsSAlg W H ;
 winit_alg_pr : forall (B: Type@{k}) (WBS: IsSAlg B H), AlgMor W B
}.

(* Make some arguments implicit *)
Arguments BuildIsWinSAlg {_} {_} {_} _ _.
Arguments winit_alg_pr _ {_} {_} {_} _ {_}.

(* Make automatically available the proof that a WinSAlg is a set algebra *)
Global Existing Instance winit_is_salg.

(* Definition 4.2.5(ii)   *)
Record WinSAlg (H: Type -> Type) {FH: FunctorStr H} := BuildWinSAlg {
 winit_obj             : Type ;
 winit_obj_is_winitalg : IsWinSAlg winit_obj H
}.

(* Make some arguments implicit *)
Arguments BuildWinSAlg {_} {_} _ _.

(* Make automatically available its component proofs *)
Global Existing Instance winit_obj_is_winitalg.

(* Coerce a WinSAlg into a type when necessary *)
Coercion winit_obj : WinSAlg >-> Sortclass.

(* Definition 4.2.8

   Since Coq is automatically managing the universe levels, we do not need to 
   define that a functor preserves levels, as this will be automatically handled by Coq. *)
Class PreservesSets (H: Type -> Type) {FH: FunctorStr H} :=
 set_preser_cond : forall A: Type, IsHSet A -> IsHSet (H A).

(* This will inform the automatic solver that "H A" is a set. *)
Global Existing Instance set_preser_cond.

(* Lemma 4.2.9 *)
Lemma functor_has_llwinsalg {fext: Funext} (H: Type -> Type) {FH: FunctorStr H} : 
 LLWinSAlg H.
Proof.  (* In the report, we used SAlg' := {X: hSet & H X -> X}. 
           Here, we will use SAlg := {X: Type & IsSAlg X H} as it is more amenable to the 
           encoding we did for set algebras on this script.
           Type SAlg is equivalent to SAlg', since any term of type SAlg is a type that 
           has the structure of a set algebra:
             - It is a set.
             - It has the structure of an algebra which means:
                 -- It has an In function.
           
           Conversely, any element of SAlg' is a term that:
             - It is a set.
             - It has a In function.

           So, SAlg and SAlg' are just associating the Sigma components differently.

           Also, since we are using records, instead of using the first projection 
           function to represent the family "pr1: SAlg -> Type",
           we will use the record accessor function: "salg_obj: SAlg -> Type"             
        *)
        (* First, we invoke Lemma 4.2.3, 
           so that the family salg_obj has a weak limit. *)
set (W := family_has_wlimit salg_obj).

        (* Now, we prove that H W is a cone for the family.
           We use a transparent assert because we want Coq to remember the
           constructed term.  *)
transparent assert (HWCone_pr: (IsCone (H W) salg_obj)).
 intro A.  (* Here, "cone_diag W A: W -> A" is playing the role of function 
             "f (A,In A): W -> A" in Claim 2 on the report. *) 
 exact ((In A) o (map H (cone_diag W A))).

           (* Since W is a weak limit for the family, we have a 
              "INW: H W -> W" function and a proof that INW is a function for the
              limit, i.e. Equation (4.4) in the
              report.
              
              Equation (4.4) is read as follows
              (just rename bound variables: "i" to "(A, In A)", and "w" to "y"):
              -- "cone_diag W i (INW w)" is playing the role of "f (A,In A) (In_W y)" 
                  in the report. 
              -- "cone_diag {| cone_obj := H W; cone_obj_is_cone := HWCone_pr |} i w"
                 is playing the role of "In A (map H (f (A,In A)) y)" in the report, 
                 which in this script is read as "In A (map H (cone_diag W A) y)", because
                 that is precisely how "HWCone_pr" was defined in the transparent assert
                 above.
           *) 
destruct (wlimit_diag W (BuildCone (H W) HWCone_pr)) as [INW INW_pr].
change (H W -> W) in INW.

refine (BuildLLWinSAlg W _).
refine (BuildIsLLWinSAlg (BuildIsSAlg INW _) _). (* Coq proves automatically that 
         W is a set, so we just need to provide the In function for W.  *)

       (* Finally, we need to prove that "AlgMor W A" is inhabited, for any set algebra
          B. *)
intros restriction B BAlg.
       (* First, "cone_diag W (BuildSAlg B BAlg)" will play the role of function 
          "f (B,In_B)" in the report. We name it fB. 

          It is this step the one that fails if we attempt to repeat this proof
          for a WinSAlg instead of a LLWinSAlg.*)
set (fB := cone_diag W (BuildSAlg B BAlg)).

refine (BuildAlgMor fB _).
intro y.
        (* But this is exactly Equation (4.4)
           instantiated with SAlg "(B,In_B)" and "y: H W" if we unfold and compute with
           all definitions. *)
exact (INW_pr (BuildSAlg B BAlg) y)^.
Qed.

(*----- Subsection 4.2.2 --------*)

(* Property part of Definition 4.2.10(i) 
  
   Notice again the use of "let enforce_lt := Type@{l} : Type@{k} in" again, to 
   impose the level restriction. *) 
Class IsLLInSAlg (W: Type@{k}) (H: Type -> Type) {FH: FunctorStr H} := BuildIsLLInSAlg { 
 llinit_is_salg : IsSAlg W H ;
 llinit_alg_pr : let enforce_lt := Type@{l} : Type@{k} in
                    forall (B: Type@{l}) (WBS: IsSAlg B H), Contr (AlgMor W B)
}.

(* Make some arguments implicit *)
Arguments BuildIsLLInSAlg {_} {_} {_} _ _.
Arguments llinit_alg_pr _ {_} {_} {_} _ {_}.

(* Make automatically available the proof that a llInSAlg is a set algebra *)
Global Existing Instance llinit_is_salg.

(*  Definition 4.2.10(i) *)
Record LLInSAlg (H: Type -> Type) {FH: FunctorStr H} := BuildLLInSAlg {
 llinit_obj             : Type ;
 llinit_obj_is_initalg  : IsLLInSAlg llinit_obj H
}.

(* Make some arguments implicit *)
Arguments BuildLLInSAlg {_} {_} _ _.

(* Make automatically available its component proofs *)
Global Existing Instance llinit_obj_is_initalg.

(* Treat a LLInSAlg as a type, when necessary *)
Coercion llinit_obj : LLInSAlg >-> Sortclass.

(* Property part of Definition 4.2.10(ii) 
 
   Notice again that the universe levels of W and B must be the same.  *) 
Class IsInSAlg (W: Type@{k}) (H: Type -> Type) {FH: FunctorStr H} := BuildIsInSAlg { 
 init_is_salg : IsSAlg W H ;
 init_alg_pr     : forall (B: Type@{k}) (WBS: IsSAlg B H), Contr (AlgMor W B)
}.

(* Make some arguments implicit *)
Arguments BuildIsInSAlg {_} {_} {_} _ _.
Arguments init_alg_pr _ {_} {_} {_} _ {_}.

(* Make automatically available the proof that an initial algebra is a set algebra *)
Global Existing Instance init_is_salg.

(* Definition 4.2.10(ii)  *) 
Record InSAlg (H: Type -> Type) {FH: FunctorStr H} := BuildInSAlg {
 init_obj             : Type ;
 init_obj_is_initalg  : IsInSAlg init_obj H
}.

(* Make some arguments implicit *)
Arguments BuildInSAlg {_} {_} _ _.

(* Make automatically available its component proofs *)
Global Existing Instance init_obj_is_initalg.

(* Treat a InSAlg as a type, when necessary *)
Coercion init_obj : InSAlg >-> Sortclass.

(* Lemma 4.2.12 *)
Lemma lambek_init_alg {H: Type -> Type} {FH: FunctorStr H} {Hsets: PreservesSets H} 
 (A: Type) {IA: IsInSAlg A H} : H A <~> A.
Proof.   (* H A becomes a SAlg with the "map H (In A) : H (H A) -> H A" function. 
            H A is a set because functor H preserves sets. 
            Coq proves this automatically. *)
set (HASAlg := BuildIsSAlg (map H (In A)) _). 
              (* Here, the accessor function "init_alg_pr" acts as term "mc"
                 in the report. *) 
destruct (@center _ (init_alg_pr A (H A))) as [u u_mor].

              (* We prove this early so that it will be available when
                 we prove the other equality *)
assert ((In A) o u = idmap) as T1.
 assert (IsAlgMor ((In A) o u)) as w1.
  intro w. (* Functoriality of H *)
  rewrite comp_preser.
  refine (ap (In A) _). (* u is morphism *)
  rewrite u_mor.
  reflexivity.
     (* Lemma 2.9.7 *)
 pose proof (id_alg_mor A) as w2.
        (* We have a unique morphism "gm" going out from A to A *)
 destruct (init_alg_pr A A) as [gm gm_unique].
 pose proof (gm_unique (BuildAlgMor ((In A) o u) w1)) as p1.
 pose proof (gm_unique (BuildAlgMor idmap w2)) as p2.
       (* And so, "(In A) o u" and "idmap" must be identifiable. 
          Here, instead of using projection "pr1" on both sides of the identity
          (as in the report), we use the accessor function "alg_mor_fun". *)
 exact (ap alg_mor_fun (p1^ @ p2)).

         (* Lemma 2.6.17 
            The first equality is "happly T1" *)
refine (equiv_adjointify (In A) u (happly T1) _).
intro w.
rewrite u_mor. (* unfold the definition of "In (H A)" *)
change (map H (In A) (map H u w) = w). (* Functoriality of H *)
rewrite <- comp_preser.
rewrite T1.
rewrite id_preser.
reflexivity.
Qed.

(* Definition 4.2.13 *)
Definition PIn {H: Type -> Type} {FH: FunctorStr H} (A: Type) {AA: IsSAlg A H} 
(P: A -> Type) {prop: forall x: A, IsHProp (P x)} : H {w: A & P w} -> A :=
 (In A) o (map H pr1).

(* Lemma 4.2.14 

   "functor_sigma" is the Sigma_map function of Lemma 2.5.28 *)
Lemma pin_lemma1 {fext: Funext} {H: Type -> Type} {FH: FunctorStr H} (A B: Type) 
{AA: IsSAlg A H} {BA: IsSAlg B H} {P: A -> Type} {Q: B -> Type}
{propP: forall x: A, IsHProp (P x)} {propQ: forall x: B, IsHProp (Q x)}
(g: A -> B) (fib: forall w: A, P w -> Q (g w)) :
     IsAlgMor g -> forall y: H {w: A & P w}, 
                      g (PIn A P y) = PIn B Q (map H (functor_sigma g fib) y).
Proof.
intro g_mor.
assert (pr1 o (functor_sigma g fib) == g o pr1) as D1.
 refine (sig_ind _ _ _ _).
 intros a b. (* By computation *)
 reflexivity.

assert ((map H g) o (map H pr1) == (map H pr1) o (map H (functor_sigma g fib))) as D2.
 intro w.
 rewrite <- comp_preser.
 rewrite <- (path_forall _ _ D1).
 rewrite comp_preser.
 reflexivity.

unfold PIn.
intro y.
rewrite g_mor.
refine (ap (In B) _).
exact (D2 y).
Qed.

(* Lemma 4.2.15 *)
Lemma pin_lemma2 {fext: Funext} {H: Type -> Type} {FH: FunctorStr H} (A: Type) 
{AA: IsSAlg A H} : forall y: H {_: A & Unit},
                      idmap (PIn A (fun _: A => Unit) y) = In A (map H pr1 y).
Proof.
intro y. (* By definition *)
reflexivity.
Qed.

(* Definition 4.2.16 
   
   Instead of using "A -> Prop" as in the report, we will use "Subtype A" because at
   some point we will use the Powertype lattice, which was defined using "Subtype". *)
Definition CanStep {H: Type -> Type} {FH: FunctorStr H} (A: Type) {AA: IsSAlg A H} :=
 fun T: Subtype A => BuildSubtype (fun w: A => Trunc -1 
                                     (exists y: H {z: A & T z}, w = PIn A T y)
                                  ).

(* Lemma 4.2.17 

   Notice how Coq automatically finds a proof that "Subtype A" has a poset
   structure, since we marked the "Powertype" lattice example as a Global Instance. *)
Global Instance CanStep_is_monotone {univ: Univalence} {H: Type -> Type} 
{FH: FunctorStr H} (A: Type) {AA: IsSAlg A H}: IsMonotone (CanStep A).
Proof.
intros P Q p1 w. (* Corollary 2.11.4 *)
refine (Trunc_rec _).
refine (sig_ind _ _ _ _).
intros y h1. (* Truncation constructor *)
refine (tr _).
set (t := map H (functor_sigma idmap p1) y).
exists t. 
       (* Lemma 2.9.7 *)
pose proof (id_alg_mor A) as D1. 
       (* Lemma 4.2.14 *)
pose proof (pin_lemma1 A A idmap p1 D1) as D2.
rewrite h1.
exact (D2 y).
Qed.

(* Definition 4.2.18

   In the report, this is written as A_I. In this script it will be written as
   "Init A" *)
Definition Init {univ: Univalence} {pres: PropResize} {H: Type -> Type} {FH: FunctorStr H} 
(A: Type) {AA: IsSAlg A H} := {w: A & Lfp (CanStep A) w}.

(* Lemma 4.2.20 *)
Global Instance Init_is_salg {univ: Univalence} {pres: PropResize} {H: Type -> Type} 
{FH: FunctorStr H} (A: Type) {AA: IsSAlg A H} : IsSAlg (Init A) H.
Proof.  (* Coq automatically proves that (Init A) is a set *)
refine (BuildIsSAlg _ _). (* Now, we need to provide the In function *) 
intro y.
set (a := PIn A (Lfp (CanStep A)) y).
exists a. (* Lemma 2.8.23 *)
refine (equiv_propresize _ _). 
intros P p1.  
refine (p1 a _).
refine (tr _). (* Corollary 3.4.1 *)
pose proof (c_induction (CanStep A) p1) as p2.
set (t := map H (functor_sigma idmap p2) y).
exists t.
       (* Lemma 2.9.7 *)
pose proof (id_alg_mor A) as D1. 
       (* Lemma 4.2.14 *)
pose proof (pin_lemma1 A A idmap p2 D1) as D2.
unfold a.
rewrite D2. (* By definition of t. *)
reflexivity.
Defined.

(* Lemma 4.2.21 *)
Lemma proj1_alg_morph {univ: Univalence} {pres: PropResize} {H: Type -> Type} 
{FH: FunctorStr H} (A: Type) {AA: IsSAlg A H} : IsAlgMor (pr1: (Init A) -> A).
Proof.
intro w. (* By definition of In (Init A) *)
reflexivity.
Qed.

(* Lemma 4.2.22 *)
Lemma Init_ind {univ: Univalence} {pres: PropResize} {H: Type -> Type} 
{FH: FunctorStr H} (A: Type) {AA: IsSAlg A H} (P: Init A -> Type) 
{Pprop: forall x: Init A, IsHProp (P x)} : 
    (forall (T: Init A -> Type) (Tprop: forall x: Init A, IsHProp (T x)), 
        (forall w: {y: Init A & T y}, P w.1) -> 
             (forall w: H {y: Init A & T y}, P (PIn (Init A) T w))
    ) -> forall n: Init A, P n.
Proof.
intro Hind. (* I had to use a transparent assert because Coq responds with an error 
               if we directly use the "set" command.
               Also, notice we need to define B as a "Subtype A" instead of just 
               "A -> Prop" as was done in the report, because we will use the Powertype 
               lattice over A. *)
transparent assert (B: (Subtype A)). 
exact (BuildSubtype (fun w: A => exists q: Lfp (CanStep A) w, P (w ; q))).

assert (Lfp (CanStep A) <= B) as k. (* Corollary 3.4.1 *)
 refine (c_induction (CanStep A) _).
 intro w.
 refine (Trunc_rec _).
 refine (sig_ind _ _ _ _). 
 intros y y_pr. (* Lemma 2.6.22 *)
 destruct (sigmas_assoc (Lfp (CanStep A)) P) as [fib equiv].
 change (forall z: Init A, P z -> B z.1) in fib. 
                (* Lemma 2.9.3 *)
 pose proof (funct_preserve_equiv H (functor_sigma pr1 fib)) as equiv'.
 set (s := map H (functor_sigma pr1 fib)). (* Lemma 4.2.21 *)
 pose proof (proj1_alg_morph A) as D1. (* Lemma 4.2.14 *) 
 pose proof (pin_lemma1 (Init A) A pr1 fib D1) as D2.
                (* Equation 4.8 *)
 
 assert (w = (PIn (Init A) P (s^-1 y)).1) as e1.
  rewrite D2. (* s is an equivalence *)
  rewrite eisretr.
  exact y_pr.
 
 set (r := PIn (Init A) P (s^-1 y)).
 pose proof (Hind P _ pr2 (s^-1 y)) as h1.
 change (P r) in h1. (* Lemma 2.6.1 *)
 rewrite <- eta_sigma in h1.
 pose proof ((r.2 ; h1) : B (r.1)) as h2.
 rewrite e1.
 exact h2.

intro n.
destruct ((k n.1 n.2) : B n.1) as [q h3].
          (* But "(Lfp (CanStep A)) n.1" is a mere proposition, so
             q = n.2 *)
rewrite (path_ishprop q n.2) in h3.
         (* Lemma 2.6.1 *)
rewrite eta_sigma in h3.
exact h3.
Qed.

(* Theorem 4.2.23(i) *)
Theorem Init_is_ll_init_salg {univ: Univalence} {pres: PropResize} {H: Type -> Type} 
{FH: FunctorStr H} (A: Type) {AA: IsLLWinSAlg A H} : IsLLInSAlg (Init A) H.
Proof. (* By Lemma 4.2.20 we know "Init A" is a SAlg *)
refine (BuildIsLLInSAlg (Init_is_salg A) _).
intros restriction B BAlg. 
                (* Existence *)
                (* There is a morphism from A to B, since A is a LLWinSAlg.
                  Notice the accessor function "llwinit_alg_pr" is playing the role
                  of term "m" in the report *)
pose proof (llwinit_alg_pr A B) as mor_to_B.
                (* We have to explicitly set the type of the projection function,
                   otherwise Coq will complain when defining function h *)
set (pr1: Init A -> A) as proj.
set (h := mor_to_B o proj). (* Lemma 4.2.21 *)
pose proof (proj1_alg_morph A) as pr1_mor.
                    (* Lemma 2.9.6 *)
pose proof (alg_mor_compose (BuildAlgMor proj pr1_mor) mor_to_B) as w1.
change (IsAlgMor h) in w1.
 
refine (BuildContr _ (BuildAlgMor h w1) _).

               (* Uniqueness *)
               (* Although we are using induction on type AlgMor, this is just induction
                  on a sigma in disguise, since records ARE sigmas. *)
induction y as [g w2].
          (* Since records are equivalent to Sigma types, we will prove instead that
             pairs (h;w1), (g;w2) are identifiable. Then, we will use the equivalence
             provided by Lemma algmor_as_sigma to conclude the required identity *) 
  assert ((h;w1) = (g;w2)) as morph_eq.
         (* Lemma 2.8.14 *)
  refine (path_sigma_hprop _ _ _).
         (* We have to do this to help the automatic prover in noticing that what we
            want to prove IS a mere proposition *)
  unfold IsAlgMor.
  exact _.
  simpl. (* Apply function extensionality *) 
  apply path_arrow. (* Lemma 4.2.22 *)
  refine (Init_ind _ _ _).
         (* Here, term "hyp" is Equation (4.12) *)
  intros T Tprop hyp.
  set (fib := fun (w: Init A) (y: T w) => tt).
  set (ts := (functor_sigma idmap fib) :
               {y: Init A & T y} -> {y: Init A & Unit}).
            (* Start Claim 1 *)
  assert ((map H h) o (map H pr1) o (map H ts) ==
         (map H g) o (map H pr1) o (map H ts)) as claim1.
                  (* This is Diagram (4.13) *)
    assert (h o pr1 o ts == g o pr1 o ts) as CD1.
      refine (sig_ind _ _ _ _).
      intros a b.
      simpl. (* By Equation (4.12) *)
      exact (hyp (a;b)).
    intro w. (* Functoriality of H *)
    rewrite <- comp_preser.
    rewrite <- comp_preser.
    rewrite <- comp_preser.
    rewrite <- comp_preser.
    rewrite (path_arrow _ _ CD1).
    reflexivity.
          (* Lemma 2.9.7 *)
  pose proof (id_alg_mor (Init A)) as id_mor.
        (* We have the left square in Diagram 
              (4.14).
           Marked with a big black star.
           We apply Lemma 4.2.14 *)
  pose proof (pin_lemma1 (Init A) (Init A) idmap fib id_mor) as BStar.
        (* We have the middle square in Diagram 
              (4.14).
           Marked with a big black diamond.
           We apply Lemma 4.2.15 *)
  pose proof (pin_lemma2 (Init A)) as BDiamond.
        (* The dashed arrows diagram is represeted by term w1.
           The squiggly arrows diagram is rerpresented by term w2. *) 
  intro w.
  rewrite BStar.
  rewrite BDiamond.
  rewrite w1.
  rewrite claim1.
  rewrite w2.
  reflexivity.

       (* Apply the equivalence between records and sigmas *)
exact (ap (algmor_as_sigma (Init A) B) morph_eq).
Defined.

(* Theorem 4.2.23(ii) 

   The proof is identical as in the previous theorem, we omit the comments this time. *)
Theorem Init_is_init_salg {univ: Univalence} {pres: PropResize} {H: Type -> Type} 
{FH: FunctorStr H} (A: Type) {AA: IsWinSAlg A H} : IsInSAlg (Init A) H.
Proof.
refine (BuildIsInSAlg (Init_is_salg A) _).
intros B BAlg. 
                (* Existence *)
pose proof (winit_alg_pr A B) as mor_to_B.
set (pr1: Init A -> A) as proj.
set (h := mor_to_B o proj).
pose proof (proj1_alg_morph A) as pr1_mor.
pose proof (alg_mor_compose (BuildAlgMor proj pr1_mor) mor_to_B) as w1.
change (IsAlgMor h) in w1.

refine (BuildContr _ (BuildAlgMor h w1) _).

               (* Uniqueness *)
induction y as [g w2]. 
  assert ((h;w1) = (g;w2)) as morph_eq.
  refine (path_sigma_hprop _ _ _).
  unfold IsAlgMor.
  exact _.
  simpl.  
  apply path_arrow.
  refine (Init_ind _ _ _).
  intros T Tprop hyp.
  set (fib := fun (w: Init A) (y: T w) => tt).
  set (ts := (functor_sigma idmap fib) :
               {y: Init A & T y} -> {y: Init A & Unit}).
            (* Start Claim 1 *)
  assert ((map H h) o (map H pr1) o (map H ts) ==
         (map H g) o (map H pr1) o (map H ts)) as claim1.
    assert (h o pr1 o ts == g o pr1 o ts) as CD1.
      refine (sig_ind _ _ _ _).
      intros a b.
      simpl.
      exact (hyp (a;b)).
    intro w.
    rewrite <- comp_preser.
    rewrite <- comp_preser.
    rewrite <- comp_preser.
    rewrite <- comp_preser.
    rewrite (path_arrow _ _ CD1).
    reflexivity.
  pose proof (id_alg_mor (Init A)) as id_mor.
  pose proof (pin_lemma1 (Init A) (Init A) idmap fib id_mor) as BStar.
  pose proof (pin_lemma2 (Init A)) as BDiamond. 
  intro w.
  rewrite BStar.
  rewrite BDiamond.
  rewrite w1.
  rewrite claim1.
  rewrite w2.
  reflexivity.

exact (ap (algmor_as_sigma (Init A) B) morph_eq).
Defined.

(* Corollary 4.2.24 *)
Corollary functor_has_llinit_salg {univ: Univalence} {pres: PropResize} (H: Type -> Type) 
{FH: FunctorStr H} : LLInSAlg H.
Proof. (* It has a LLWinSAlg by Lemma 4.2.9 *)
destruct (functor_has_llwinsalg H) as [W llwinsalg_pr].
       (* By Theorem 4.2.23(i), 
          "Init W" is a LLInSAlg *)
exact (BuildLLInSAlg (Init W) (Init_is_ll_init_salg W)).
Defined.

(*----- Subsection 4.2.3 --------*)

(* Definition 4.2.25 

   We use "Subtype Y" instead of "Y -> hProp", which are equivalent. *)
Definition Pow (Y: Type) := Subtype Y.

(* Lemma 4.2.26 *)
Global Instance Pow_is_functor {univ: Univalence} {pres: PropResize} : FunctorStr Pow. 
Proof.
set (mapPow A B f := fun P: Subtype A => 
                        BuildSubtype (fun w: B => 
                                         GPropR (Trunc -1 (
                                                   exists y: A, (P y) * (f y = w)
                                                )
                                         )
                                     )
    ).
refine (BuildFunctorStr mapPow _ _).

intros A P. (* It is enough to prove that the underlying functions are equal. *)
refine (path_subtype _).
simpl. (* Apply function extensionality *)
apply path_arrow.
intro w. (* Apply univalence *)
refine (path_universe_uncurried _).
         (* Lemma 2.8.8 *)
refine (equiv_iff_hprop _ _).

         (* Lemma 2.8.24 *)
refine (prop_resize_rec _).
         (* By (-1)-truncation recursion *)
refine (Trunc_rec _).
         (* By sigma recursion *)
refine (sig_ind _ _ _ _).
intro y.
refine (prod_ind _ _).
intros q r.
exact (transport P r q).

intro q. (* Lemma 2.8.23 *)
refine (equiv_propresize _ _).
exact (tr (w ; (q , idpath))).

intros A B C g h P. (* It is enough to prove that the underlying functions are equal. *)
refine (path_subtype _).
simpl. (* Apply function extensionality *)
apply path_arrow.
intro w. (* Apply univalence *)
refine (path_universe_uncurried _).
         (* Lemma 2.8.8 *)
refine (equiv_iff_hprop _ _).

         (* Lemma 2.8.24 *)
refine (prop_resize_rec _).
         (* By (-1)-truncation recursion *)
refine (Trunc_rec _).
         (* By sigma recursion *)
refine (sig_ind _ _ _ _).
intro y.
refine (prod_ind _ _).
intros q r.
         (* Lemma 2.8.23 *)
refine (equiv_propresize _ _).
refine (tr (g y ; (_ , r))).
         (* Lemma 2.8.23 *)
refine (equiv_propresize _ _).
exact (tr (y ; (q , idpath))).

         (* Lemma 2.8.24 *)
refine (prop_resize_rec _).
         (* By (-1)-truncation recursion *)
refine (Trunc_rec _).
         (* By sigma recursion *)
refine (sig_ind _ _ _ _).
intro z.
refine (prod_ind _ _).
         (* Lemma 2.8.24 *)
refine (prop_resize_rec _).
         (* By (-1)-truncation recursion *)
refine (Trunc_rec _).
         (* By sigma recursion *)
refine (sig_ind _ _ _ _).
intro t.
refine (prod_ind _ _).
intros s u r.
         (* Lemma 2.8.23 *)
refine (equiv_propresize _ _).
exact (tr (t ; (s , (ap h u) @ r))).
Defined.

(* That Pow preserves sets is part of Lemma 4.2.26

   Also, that Pow preserves levels will be automatically managed by Coq. *)
Global Instance Pow_preservesSets {univ: Univalence} {pres: PropResize} : 
 PreservesSets Pow.
Proof.
intros X Xset. (* Coq automatically proves that "Subtype X" is a set. *)
exact _.
Qed.

(* Theorem 4.2.27 *)
Theorem pow_without_init_salg {univ: Univalence} {pres: PropResize} : ~(InSAlg Pow).
Proof.
intro A. (* Lemma 4.2.12 *)
pose proof (lambek_init_alg A) as fixp.
         (* Lemma 2.8.20 *)
exact (cantor A fixp).
Qed.

(* Corollary 4.2.28 *)
Corollary pow_without_winit_salg {univ: Univalence} {pres: PropResize} : ~(WinSAlg Pow).
Proof.
intro A. (* Theorem 4.2.23(ii) *)
pose proof (Init_is_init_salg A) as Ainit.
         (*  Theorem 4.2.27 *)
exact (pow_without_init_salg (BuildInSAlg (Init A) Ainit)).
Qed.

(* Corollary 4.2.29 *)
Corollary llinit_salg_not_fixpoint {univ: Univalence} {pres: PropResize} (A: Type) 
{Allinit: IsLLInSAlg A Pow} : ~(Pow A <~> A).
Proof. (* Lemma 2.8.20 *)
exact (cantor A).
Qed.

(*----- Subsection 4.2.4 --------*)

Section Example_nat.

(* We will assume univalence and propresize on this section *)
Context {univ: Univalence}
        {propres: PropResize}.

(* Definition 4.2.30 *)
Definition NatF (Y: Type) := Unit + Y.

(* Lemma 4.2.31 *)
Local Instance NatF_is_functor : FunctorStr NatF.
Proof.
transparent assert (mapNatF: (forall A B: Type, (A -> B) -> NatF A -> NatF B)).
 intros A B f. (* Define map by recursion on sum types *)
 refine (sum_ind _ _ _).
 exact (fun l => inl l).
 exact (fun r => inr (f r)).

refine (BuildFunctorStr mapNatF _ _).
        (* Identity mapping case *)
intro A. (* By induction on sum types *)
refine (sum_ind _ _ _).
intro l. (* By computation *)
reflexivity.
intro r. (* By computation *)
reflexivity.
          (* Function composition mapping case *)
intros A B C g h. (* By induction on sum types *)
refine (sum_ind _ _ _).
intro l. (* By computation *)
reflexivity.
intro r. (* By computation *)
reflexivity.
Defined.

(* This is the set preservation part of 
   Lemma 4.2.31

   We do not need to prove that NatF preserves levels, as it is handled 
   automatically by Coq. *)
Local Instance NatF_preserves_sets : PreservesSets NatF.
Proof.
intros X setX. (* Coq automatically proves it *)
exact _.
Defined.

(* Definition 4.2.32

   We obtain it from Corollary 4.2.24 *)
Definition Nat := functor_has_llinit_salg NatF.

(* We extract the In function from Nat because Coq behaves a bit dumb 
   if we attempt to use the expression "In Nat" inside more complex 
   expressions. So, we have to help Coq a bit. *)
Definition In_Nat := In Nat.

(* Definition 4.2.33 *)
Definition zero_Nat : Nat := In_Nat (inl tt).

(* Definition 4.2.33 *)
Definition succ_Nat (n: Nat) : Nat := In_Nat (inr n).

(* Theorem 4.2.34 *)
Theorem Nat_ind (P: Nat -> Type) {HP: forall x: Nat, IsHProp (P x)} :
 P zero_Nat -> (forall n: Nat, P n -> P (succ_Nat n)) -> 
   forall n: Nat, P n.
Proof.
intros base Ind.
refine (Init_ind _ _ _).
intros T HT HInd. (* By induction on sum types *)
refine (sum_ind _ _ _). 
                  (* By induction on unit type *)
refine (Unit_ind _). (* This simplifies to zero_Nat *)
change (P zero_Nat).
exact (base).

intro r. (* This simplifies to P (succ_Nat r.1) *)
change (P (succ_Nat r.1)).
exact (Ind r.1 (HInd r)).
Qed.

(* Theorem 4.2.35 *)
Theorem Nat_iter {D: Type} {SD: IsHSet D} (base: D) (step: D -> D) : 
 Contr (exists f: Nat -> D, (f zero_Nat = base) * 
                            (forall n: Nat, f (succ_Nat n) = step (f n))
       ).
Proof.
set (InD := fun z: Unit + D => match z with
                               | inl _ => base
                               | inr t => step t
                               end). (* So, D is a SAlg for functor NatF *)
set (DSAlg := (BuildIsSAlg InD _): IsSAlg D NatF).
destruct (llinit_alg_pr Nat D) as [u h_unique].
destruct u as [h h_mor]. (* So, h: Nat -> D is a unique morphism.
        Here, "h_mor" is Diagram (4.16) 
        And "h_unique" is the proof that h is unique. *)

                (* Existence *)
assert ((h zero_Nat = base) * (forall n : Nat, h (succ_Nat n) = step (h n))) as w1.
  split.  (* By computation and the fact that h is morphism *)
  exact (h_mor (inl tt)).
  intro n.
  exact (h_mor (inr n)).

refine (BuildContr _ (h ; w1) _).

                (* Uniqueness *)
refine (sig_ind _ _ _ _).
intros g w2. (* Lemma 2.8.14 *)
refine (path_sigma_hprop _ _ _).
simpl.
assert (IsAlgMor g) as q2. (* By induction on sum types *)
 refine (sum_ind _ _ _). (* By induction on the unit type *)
 refine (Unit_ind _). (* By hypotheses on g *)
 exact (fst w2).
 intro r.
 exact (snd w2 r). (* So, by uniqueness of h, we must have h = g *)
 exact (ap alg_mor_fun (h_unique (BuildAlgMor g q2))).
Qed.

(* Theorem 4.2.36 
   
   Here, nat are the naturals as defined in the HoTT library. *)
Theorem Nat_equiv_to_nat : Nat <~> nat.
Proof. (* By the iteration principle for Nat, we have a function
          that translates every "Nat" into a "nat".
          Notice that Coq proves automatically that "nat" is a set.  *)
destruct (@center _ (Nat_iter 0 (fun prev: nat => prev.+1))) as [f fpr].
        (* We also got a function that translates backwards. 
           We use a transparent assert because we want Coq to remember 
           the definition. *)
transparent assert (g: (nat -> Nat)).
refine (nat_ind _ _ _). 
       (* Case 0. *)
exact zero_Nat. (* recursive step. *)
intros n prev.
exact (succ_Nat prev).

         (* Now, we proceed to prove the equivalence. 
            We use Lemma 2.6.17 *)
refine (equiv_adjointify f g _ _).

         (* By induction on "nat" *)
refine (nat_ind _ _ _).
simpl. (* But this is an hypothesis about "f". *)
exact (fst fpr).

intros n IHn.
simpl. (* Rewrite the second hypothesis about "f". *)
rewrite (snd fpr). (* This is the inductive hypothesis applied on the successor. *)
exact (ap S IHn).

         (* By induction on "Nat" *)
refine (Nat_ind _ _ _). (* But "f zero_Nat = 0". *)
rewrite (fst fpr).
reflexivity.

intros n IHn. (* Rewrite hypothesis on f. *)
rewrite (snd fpr).
simpl. (* This is the inductive hypothesis applied on the successor. *)
exact (ap succ_Nat IHn).
Qed.

End Example_nat.

(*----- Section 4.3 ----------*)

(*---- Subsection 4.3.1 ------*)

(* Property part of Definition 4.3.1 *)
Class IsCocone (C: Type) {M: Type} (F: M -> Type) :=
 cocone_diag : forall i: M, F i -> C.

(* Make some arguments implicit *)
Arguments cocone_diag _ {_} {_} {_} _ _.

(* Definition 4.3.1 *)
Record Cocone {M: Type} (F: M -> Type) := BuildCocone {
 cocone_obj           : Type ;
 cocone_obj_is_cocone : IsCocone cocone_obj F
}.

(* Make some arguments implicit *)
Arguments BuildCocone {_} {_} _ _.

(* Make automatically available the proof that it is a cocone *)
Global Existing Instance cocone_obj_is_cocone.

(* Treat a cocone as a type when necessary *)
Coercion cocone_obj : Cocone >-> Sortclass.

(* Definition 4.3.2 *)
Record WColimit {M: Type} (F: M -> Type) := BuildWColimit {
 wcolimit_obj           : Type ;
 wcolimit_obj_is_cocone : IsCocone wcolimit_obj F ;
 wcolimit_diag          : forall Y: Cocone F, exists h: wcolimit_obj -> Y,
                            forall (i: M) (w: F i), 
                               cocone_diag Y i w = h (cocone_diag wcolimit_obj i w)
}.

(* Make some arguments implicit *)
Arguments BuildWColimit {_} {_} _ _ _.
Arguments wcolimit_diag {_} {_} _ _.

(* Make automatically available the proof that a weak colimit is a cocone *)
Global Existing Instance wcolimit_obj_is_cocone.

(* Treat a weak colimit as a type, when necessary *)
Coercion wcolimit_obj : WColimit >-> Sortclass.

(* Lemma 4.3.3  *)
Lemma family_has_wcolimit {M: Type} (F: M -> Type) : WColimit F.
Proof.
set (C := exists i: M, F i).
set (f := fun (i: M) (j: F i) => (i ; j)).
refine (BuildWColimit C f _).

intro Y.

transparent assert (h: (C -> Y)).
  refine (sig_ind _ _ _ _).
  exact (fun (i: M) (j: F i) => cocone_diag Y i j).

exists h.
intros i w.
reflexivity.
Defined.

(* Property part of Definition 4.3.4(i)  
 
   Again we use "let enforce_lt" to enforce the lower level restriction. *)
Class IsLLWfinCoAlg (W: Type@{k}) (H: Type -> Type) {FH: FunctorStr H} := 
BuildIsLLWfinCoAlg { 
 llwfin_is_coalg  : IsCoAlg W H ;
 llwfin_coalg_pr  : let enforce_lt := Type@{l} : Type@{k} in
                       forall (B: Type@{l}) (WBS: IsCoAlg B H), CoAlgMor B W
}.

(* Make some arguments implicit *)
Arguments BuildIsLLWfinCoAlg {_} {_} {_} _ _.
Arguments llwfin_coalg_pr _ {_} {_} {_} _ {_}.

(* Make automatically available the proof that a llWfinCoAlg is a coalgebra *)
Global Existing Instance llwfin_is_coalg.

(* Definition 4.3.4(i)  *)
Record LLWfinCoAlg (H: Type -> Type) {FH: FunctorStr H} := BuildLLWfinCoAlg {
 llwfin_obj              : Type ;
 llwfin_obj_is_wfincoalg : IsLLWfinCoAlg llwfin_obj H
}.

(* Make some arguments implicit *)
Arguments BuildLLWfinCoAlg {_} {_} _ _.

(* Make automatically available its component proofs *)
Global Existing Instance llwfin_obj_is_wfincoalg.

(* Coerce a LLWfinCoAlg into a type when necessary *)
Coercion llwfin_obj : LLWfinCoAlg >-> Sortclass.

(* Property part of Definition 4.3.4(ii)  

   Notice again that the universe levels of W and B must be the same. *)
Class IsWfinCoAlg (W: Type@{k}) (H: Type -> Type) {FH: FunctorStr H} := BuildIsWfinCoAlg { 
 wfin_is_coalg : IsCoAlg W H ;
 wfin_coalg_pr : forall (B: Type@{k}) (WBS: IsCoAlg B H), CoAlgMor B W
}.

(* Make some arguments implicit *)
Arguments BuildIsWfinCoAlg {_} {_} {_} _ _.
Arguments wfin_coalg_pr _ {_} {_} {_} _ {_}.

(* Make automatically available the proof that a WfinCoAlg is a coalgebra *)
Global Existing Instance wfin_is_coalg.

(* Definition 4.3.4(ii)   *)
Record WfinCoAlg (H: Type -> Type) {FH: FunctorStr H} := BuildWfinCoAlg {
 wfin_obj             : Type ;
 wfin_obj_is_wfincoalg : IsWfinCoAlg wfin_obj H
}.

(* Make some arguments implicit *)
Arguments BuildWfinCoAlg {_} {_} _ _.

(* Make automatically available its component proofs *)
Global Existing Instance wfin_obj_is_wfincoalg.

(* Coerce a WfinCoAlg into a type when necessary *)
Coercion wfin_obj : WfinCoAlg >-> Sortclass.

(* Lemma 4.3.6 *)
Lemma functor_has_llwfincoalg {fext: Funext} (H: Type -> Type) {FH: FunctorStr H} : 
 LLWfinCoAlg H.
Proof.  (* Since we are using records, instead of using the first projection 
           function to represent the family "pr1: CoAlg -> Type",
           we will use the record accessor function: "coalg_obj: CoAlg -> Type"             
        *)
        (* First, we invoke Lemma 4.3.3, 
           so that the family coalg_obj has a weak colimit. *)
set (W := family_has_wcolimit coalg_obj).

        (* Now, we prove that H W is a cocone for the family.
           We use a transparent assert because we want Coq to remember the
           constructed term.  *)
transparent assert (HWCocone_pr: (IsCocone (H W) coalg_obj)).
 intro A.  (* Here, "cocone_diag W A: A -> W" is playing the role of function 
             "f (A,Out A): A -> W" in Claim 1 on the report. *) 
 exact ((map H (cocone_diag W A)) o (Out A)).

           (* Since W is a weak colimit for the family, we have a 
              "OUTW: W -> H W" function and a proof that OUTW is a function for the
              colimit, i.e. Equation (4.17) in the
              report.
              
              Equation (4.17) is read as follows
              (just rename bound variables: "i" to "(A, In A)", and "w" to "y"):
              -- "OUTW (cocone_diag W i w)" is playing the role of "Out_W (f (A,Out A) y)" 
                  in the report. 
              -- "cocone_diag
                  {| cocone_obj := H W; cocone_obj_is_cocone := HWCocone_pr |} i w"
                 is playing the role of "map H (f (A,Out A)) (Out_A y)" in the report, 
                 which in this script is read as "map H (cone_diag W A) (Out A y)", because
                 that is precisely how "HWCocone_pr" was defined in the transparent assert
                 above.
           *) 
destruct (wcolimit_diag W (BuildCocone (H W) HWCocone_pr)) as [OUTW OUTW_pr].
change (W -> H W) in OUTW.

refine (BuildLLWfinCoAlg W _).
refine (BuildIsLLWfinCoAlg OUTW _).

       (* Finally, we need to prove that "CoAlgMor B W" is inhabited, for any coalgebra
          B. *)
intros restriction B BCoAlg.
       (* First, "cocone_diag W (BuildCoAlg B BAlg)" will play the role of function 
          "f (B,Out_B)" in the report. We name it fB. 

          It is this step the one that fails if we attempt to repeat this proof
          for a WfinCoAlg instead of a LLWfinCoAlg.*)
set (fB := cocone_diag W (BuildCoAlg B BCoAlg)).

refine (BuildCoAlgMor fB _).
intro y.
        (* But this is exactly Equation (4.17)
           instantiated with CoAlg "(B,Out_B)" and "y: B" if we unfold and compute with
           all definitions. *)
exact (OUTW_pr (BuildCoAlg B BCoAlg) y).
Qed.

(*----- Subsection 4.3.2 --------*)

(* Property part of Definition 4.3.7(i)   

   Again, "let enforce_lt" to enforce the lower level restriction. *)
Class IsLLFinCoAlg (W: Type@{k}) (H: Type -> Type) {FH: FunctorStr H} := 
BuildIsLLFinCoAlg { 
 llfin_is_coalg : IsCoAlg W H ;
 llfin_coalg_pr : let enforce_lt := Type@{l} : Type@{k} in
                    forall (B: Type@{l}) (BS: IsCoAlg B H), Contr (CoAlgMor B W)
}.

(* Make some arguments implicit *)
Arguments BuildIsLLFinCoAlg {_} {_} {_} _ _.
Arguments llfin_coalg_pr _ {_} {_} {_} _ {_}.

(* Make automatically available the proof that a llFinCoAlg is a coalgebra *)
Global Existing Instance llfin_is_coalg.

(* Definition 4.3.7(i)   *)
Record LLFinCoAlg (H: Type -> Type) {FH: FunctorStr H} := BuildLLFinCoAlg {
 llfin_obj              : Type ;
 llfin_obj_is_fincoalg  : IsLLFinCoAlg llfin_obj H
}.

(* Make some arguments implicit *)
Arguments BuildLLFinCoAlg {_} {_} _ _.

(* Make automatically available its component proofs *)
Global Existing Instance llfin_obj_is_fincoalg.

(* Treat a LLFinCoAlg as a type, when necessary *)
Coercion llfin_obj : LLFinCoAlg >-> Sortclass.

(* Property part of Definition 4.3.7(ii)   

   Notice again that the universe levels of W and B must be the same.  *)
Class IsFinCoAlg (W: Type@{k}) (H: Type -> Type) {FH: FunctorStr H} := BuildIsFinCoAlg { 
 fin_is_coalg     : IsCoAlg W H ;
 fin_coalg_pr     : forall (B: Type@{k}) (BS: IsCoAlg B H), Contr (CoAlgMor B W)
}.

(* Make some arguments implicit *)
Arguments BuildIsFinCoAlg {_} {_} {_} _ _.
Arguments fin_coalg_pr _ {_} {_} {_} _ {_}.

(* Make automatically available the proof that a final coalgebra is a coalgebra *)
Global Existing Instance fin_is_coalg.

(* Definition 4.3.7(ii)   *)
Record FinCoAlg (H: Type -> Type) {FH: FunctorStr H} := BuildFinCoAlg {
 fin_obj              : Type ;
 fin_obj_is_fincoalg  : IsFinCoAlg fin_obj H
}.

(* Make some arguments implicit *)
Arguments BuildFinCoAlg {_} {_} _ _.

(* Make automatically available its component proofs *)
Global Existing Instance fin_obj_is_fincoalg.

(* Treat a FinCoAlg as a type, when necessary *)
Coercion fin_obj : FinCoAlg >-> Sortclass.

(* Lemma 4.3.9 *)
Lemma lambek_fin_coalg {H: Type -> Type} {FH: FunctorStr H} (A: Type) 
{FA: IsFinCoAlg A H} : H A <~> A.
Proof.   (* H A becomes a CoAlg with the "map H (Out A) : H A -> H (H A)" function. *)
set (HACoAlg := (map H (Out A)) : IsCoAlg (H A) H). 
              (* Here, the accessor function "fin_coalg_pr" acts as term "mc"
                 in the report. *) 
destruct (@center _ (fin_coalg_pr A (H A))) as [u u_mor].

              (* We prove this early so that it will be available when
                 we prove the other equality *)
assert (u o (Out A) = idmap) as T1.
 assert (IsCoAlgMor (u o (Out A))) as w1.
  intro w. (* Functoriality of H *)
  rewrite comp_preser. (* u is morphism *)
  rewrite <- u_mor.
  refine (ap (map H u) _). (* By computation *)
  reflexivity.
     (* Lemma 2.10.4 *)
 pose proof (id_coalg_mor A) as w2.
        (* We have a unique morphism "gm" going out from A to A *)
 destruct (fin_coalg_pr A A) as [gm gm_unique].
 pose proof (gm_unique (BuildCoAlgMor (u o (Out A)) w1)) as p1.
 pose proof (gm_unique (BuildCoAlgMor idmap w2)) as p2.
       (* And so, "u o (Out A)" and "idmap" must be identifiable. 
          Here, instead of using projection "pr1" on both sides of the identity,
          we use the accessor function "coalg_mor_fun". *)
 exact (ap coalg_mor_fun (p1^ @ p2)).

         (* Lemma 2.6.17 
            The first equality is "happly T1" *)
refine (equiv_adjointify u (Out A) (happly T1) _).
intro w.
rewrite <- u_mor. (* unfold the definition of "Out (H A)" *)
change (map H u (map H (Out A) w) = w). (* Functoriality of H *)
rewrite <- comp_preser.
rewrite T1.
rewrite id_preser.
reflexivity.
Qed.

(* 4.3.10 *)
Lemma coalg_pushout {fext: Funext} {H: Type -> Type} {FH: FunctorStr H} {A B C: Type} 
{Acalg: IsCoAlg A H} {Bcalg: IsCoAlg B H} {Ccalg: IsCoAlg C H}
 (h: A -> B) (g: A -> C) :
     (IsCoAlgMor h) -> (IsCoAlgMor g) -> (IsSurjection h) -> (IsSurjection g) ->
          exists (T: Type) (Tcalg: IsCoAlg T H) (pl: B -> T) (pr: C -> T),
             (IsCoAlgMor pl) * (IsCoAlgMor pr) * (IsSurjection pl) * (IsSurjection pr) *
             (pl o h == pr o g).
Proof.
intros morh morg surh surg.
set (T := pushout h g).
set (h1 := (map H (pushleft h g)) o (Out B)).
set (h2 := (map H (pushright h g)) o (Out C)).
exists T.

transparent assert (Tcalg: (IsCoAlg T H)).
              (* Lemma 2.11.22 *)
  refine (pushout_rec' h1 h2 _).
  intro a.
  unfold h1.
  unfold h2. (* h is a morphism *)
  rewrite <- morh. (* Functoriality of H *)
  rewrite <- comp_preser. (* By higher constructor for pushouts and 
                           function extensionality *)
  rewrite (path_forall _ _ (pushiden h g)).
  rewrite comp_preser. (* g is a morphism *)
  rewrite morg.
  reflexivity.

exists Tcalg.    
exists (pushleft h g).
exists (pushright h g).
split.
split.
split.
split.

intro b. (* By computation *)
reflexivity.

intro c. (* By computation *)
reflexivity.
        
         (* Lemma 2.11.23 *)
exact (pushleft_surjective h g surg).
exact (pushright_surjective h g surh).

intro a. (* By the higher constructor for pushouts *)
exact (pushiden h g a).
Qed.

(* Lemma 4.3.11 *)
Lemma coalg_coequalizer {fext: Funext} {H: Type -> Type} {FH: FunctorStr H} {A B: Type} 
{Acalg: IsCoAlg A H} {Bcalg: IsCoAlg B H} (f: A -> B) (g: A -> B) :
     (IsCoAlgMor f) -> (IsCoAlgMor g) ->
        exists (T: Type) (Tcalg: IsCoAlg T H) (p: B -> T),
               (IsCoAlgMor p) * (IsSurjection p) * (p o f == p o g).
Proof.
intros morf morg.
set (T := Coeq f g).
set (h := (map H (@coeq _ _ f g)) o (Out B)).
exists T.

transparent assert (Tcalg: (IsCoAlg T H)).
          (* Lemma 2.11.18 *)
  refine (Coeq_rec _ h _).
  intro a.
  unfold h. (* f is a morphism *)
  rewrite <- morf. (* Functoriality of H *)
  rewrite <- comp_preser. (* By higher constructor for coequalizers and 
                           function extensionality *)
  rewrite (path_forall _ _ cp).
  rewrite comp_preser. (* g is a morphism *)
  rewrite morg.
  reflexivity.

exists Tcalg.
exists coeq.
split.
split.

intro b. (* By computation *)
reflexivity.
     
         (* Lemma 2.11.19 *)
exact (coeq_constructor_surjective f g).

intro a. (* By the higher constructor for coequalizers *)
exact (cp a).
Qed.

(* Definition 4.3.14 *)
Definition PurelyBehEquiv {H: Type -> Type} {FH: FunctorStr H} {A: Type} 
{Acalg: IsCoAlg A H} (w y: A) := 
  exists (T: Type) (Tcalg: IsCoAlg T H) (f g: A -> T),
    (IsCoAlgMor f) * (IsCoAlgMor g) * (IsSurjection f) * (IsSurjection g) *
    (f w = g y).

(* Definition 4.3.18 

   Notice that Coq uses two different projection functions:
   - For non-dependent pairs it uses "fst" and "snd".
   - For dependent pairs it uses "pr1" and "pr2".
*) 
Definition IsBisimu {H: Type -> Type} {FH: FunctorStr H} {A: Type} {Acalg: IsCoAlg A H} 
(R: A * A -> Type) :=
 forall a b: A, R (a,b) ->  
       exists t: H {z: A * A & R z},
           (Out A a = map H (fst o pr1) t) * 
           (Out A b = map H (snd o pr1) t).

(* Definition 4.3.19 *)
Definition Bisim {H: Type -> Type} {FH: FunctorStr H} {A: Type} {Acalg: IsCoAlg A H} 
(w y: A) := exists R: A * A -> Type, (R (w,y)) * (IsBisimu R).

(* Lemma 4.3.20 *)
Lemma bisim_implies_beh_equiv {fext: Funext} {H: Type -> Type} {FH: FunctorStr H} 
{A: Type} {Acalg: IsCoAlg A H} (w y: A) : Bisim w y -> PurelyBehEquiv w y.
Proof.
refine (sig_ind _ _ _ _).
intro R.
refine (prod_ind _ _).
intros h1 h2. (* Notice we have to use "fst" and "snd" instead of "pr1" and "pr2"
                 because we are projecting over a non-dependent pair. *)
set (T := {z: A * A & R z} + {z: A * A & fst z = snd z}).

transparent assert (f1: ({z: A * A & R z} -> H T)).
refine ((map H inl) o _). (* We define now function f1' in the report by induction 
                           on sigmas.
                           Since Coq represents non-dependent pairs separately from
                           sigmas, we have to use induction on products as well.
                           But this is just a technicality. *)
refine (sig_ind _ _ _ _).
refine (prod_ind _ _).
intros a b p.
exact (pr1 (h2 a b p)).

set (f2' := (fun a: A => inr ((a,a) ; idpath)):A -> T).
set (f2 := ((map H f2') o (Out A) o fst o pr1):{z: A * A & fst z = snd z} -> H T).

transparent assert (Tcalg: (IsCoAlg T H)).
exact (sum_ind _ f1 f2).

transparent assert (m1: (T -> A)).
refine (sum_ind _ _ _).
exact (fst o pr1).
exact (fst o pr1).

transparent assert (m2: (T -> A)).
refine (sum_ind _ _ _).
exact (snd o pr1).
exact (snd o pr1).

assert (IsCoAlgMor m1) as m1mor.
  refine (sum_ind _ _ _).

  refine (sig_ind _ _ _ _).
  refine (prod_ind _ _).
  intros a b p. (* Simplify a bit by computation *)
  change (map H m1 (map H inl (h2 a b p).1) = Out A a). (* Functoriality of H *)
  rewrite <- comp_preser. (* Simplify again *)
  change (map H (fst o pr1) (h2 a b p).1 = Out A a).
  exact (fst (h2 a b p).2)^.

  refine (sig_ind _ _ _ _).
  refine (prod_ind _ _).
  intros a b p. (* Simplify a bit by computation *)
  change (map H m1 (map H f2' (Out A a)) = Out A a). (* Functoriality of H *)
  rewrite <- comp_preser. (* Simplify again *)
  change (map H idmap (Out A a) = Out A a).
  rewrite id_preser.
  reflexivity.

assert (IsCoAlgMor m2) as m2mor.
  refine (sum_ind _ _ _).

  refine (sig_ind _ _ _ _).
  refine (prod_ind _ _).
  intros a b p. (* Simplify a bit by computation *)
  change (map H m2 (map H inl (h2 a b p).1) = Out A b). (* Functoriality of H *)
  rewrite <- comp_preser. (* Simplify again *)
  change (map H (snd o pr1) (h2 a b p).1 = Out A b).
  exact (snd (h2 a b p).2)^.

  refine (sig_ind _ _ _ _).
  refine (prod_ind _ _).
  intros a b p. (* Simplify a bit by computation *)
  change (map H m2 (map H f2' (Out A a)) = Out A b). (* Functoriality of H *)
  rewrite <- comp_preser. (* Simplify again *)
  change (map H idmap (Out A a) = Out A b).
  rewrite id_preser. (* But a = b by hypothesis *)
  exact (ap (Out A) p).

assert (IsSurjection m1) as m1sur.
  intro a.
  set (p1 := (inr ((a,a) ; idpath)): T).
  refine (tr (p1 ; idpath)).

assert (IsSurjection m2) as m2sur.
  intro a.
  set (p1 := (inr ((a,a) ; idpath)): T).
  refine (tr (p1 ; idpath)).

            (* Lemma 4.3.10 *)
destruct (coalg_pushout m1 m2 m1mor m2mor m1sur m2sur) as [Q t1].
destruct t1 as [Qcalg t2].
destruct t2 as [pl t3].
destruct t3 as [pr t4].
destruct t4 as [t5 D1]. 
                (* Term "D1" represents Diagram (4.19) *)
destruct t5 as [t7 prsur].
destruct t7 as [t8 plsur].
destruct t8 as [plmor prmor].

exists Q.
exists Qcalg.
exists pl.
exists pr.
split.
split.
split.
split.
exact plmor.
exact prmor.
exact plsur.
exact prsur. (* By diagram (4.19) 
             and computation *)
exact (D1 (inl ((w,y) ; h1))).
Qed.

(* Lemma 4.3.21 *)
Lemma behavior_equiv_one_morph {fext: Funext} {H: Type -> Type} {FH: FunctorStr H} 
{A: Type} {Acalg: IsCoAlg A H} (w y: A) : 
                             PurelyBehEquiv w y ->  
                                  exists (T: Type) (Tcalg: IsCoAlg T H) (p: A -> T),
                                    (IsCoAlgMor p) * (IsSurjection p) * (p w = p y).
Proof.
refine (sig_ind _ _ _ _).
intro T.
refine (sig_ind _ _ _ _).
intro Tcalg.
refine (sig_ind _ _ _ _).
intro h.
refine (sig_ind _ _ _ _).
intro g.
refine (prod_ind _ _).
refine (prod_ind _ _).
refine (prod_ind _ _).
refine (prod_ind _ _).
intros hmor gmor hsur gsur h1.

destruct (coalg_coequalizer h g hmor gmor) as [Q t1].
destruct t1 as [Qcalg t2].
destruct t2 as [p t3].
destruct t3 as [t4 D1]. 
             (* Term "D1" is Diagram (4.20) *)
destruct t4 as [pmor psur].

exists Q.
exists Qcalg.
set (q := p o h).
exists q.
split.
split.
           (* Lemma 2.10.3 *)
exact (coalg_mor_compose (BuildCoAlgMor h hmor) (BuildCoAlgMor p pmor)).

           (* Lemma 2.11.11 *)
exact (surjections_compose hsur psur).

unfold q.
rewrite h1. (* By Diagram (4.20) *)
exact (D1 y)^.
Qed.

(* Definition 4.3.22 *)
Definition BehEquiv {pres: PropResize} {H: Type -> Type} {FH: FunctorStr H} {A: Type} 
{Acalg: IsCoAlg A H} (w y: A) := GPropR (Trunc -1 (PurelyBehEquiv w y)).

(* Definition 4.3.23
 
   In the report, this is written as A_F. In this script it will be written as
   "Fin A" *)
Definition Fin {pres: PropResize} {H: Type -> Type} {FH: FunctorStr H} (A: Type) 
{Acalg: IsCoAlg A H} := quotient BehEquiv.

(* Lemma 4.3.24 *)
Lemma class_of_factor {fext: Funext} {pres: PropResize} {H: Type -> Type} 
{FH: FunctorStr H} {A: Type} {Acalg: IsCoAlg A H} {B: Type} {Bcalg: IsCoAlg B H} 
(h: A -> B) : (IsCoAlgMor h) -> (IsSurjection h) ->
                                     exists g: B -> Fin A, class_of BehEquiv == g o h.
Proof.
intros hmor hsur.
set (P w := exists y: Fin A, Trunc -1 (
                               exists c: A, (class_of _ c = y) * (h c = w)
                             )
    ).
assert (forall w: B, IsHProp (P w)) as t1.
  intro w.
  apply (equiv_hprop_allpath (P w))^-1.
  refine (sig_ind _ _ _ _).
  intros y1 p1.
  refine (sig_ind _ _ _ _).
  intros y2 p2. (* Lemma 2.8.14 *)
  refine (path_sigma_hprop _ _ _).
  simpl.
  refine (Trunc_ind _ _ p1).
  refine (sig_ind _ _ _ _).
  intro c1.
  refine (prod_ind _ _).
  intros E1 E2.
  refine (Trunc_ind _ _ p2).
  refine (sig_ind _ _ _ _).
  intro c2.
  refine (prod_ind _ _).
  intros E3 E4. (* Here, E1, E2, E3, and E4 are equations
                   (4.22) *)
  rewrite <- E1.
  rewrite <- E3. (* By higher constructor for quotients. *)
  refine (related_classes_eq BehEquiv _).
                 (* Lemma 2.8.23 *)
  refine (equiv_propresize _ _). 
  refine (tr _).
  exists B.
  exists Bcalg.
  exists h.  
  exists h.
  split.
  split.
  split.
  split.
  exact hmor.
  exact hmor.
  exact hsur.
  exact hsur.
  rewrite E2.
  exact E4^.

assert (forall w: B, Trunc -1 (P w)) as t2.
  intro w.
  cut (Trunc -1 (exists c: A, h c = w)).
  refine (Trunc_rec _).
  refine (sig_ind _ _ _ _).
  intros c cp.
  exact (tr (class_of _ c ; tr (c ; (idpath , cp)))).  
  exact (hsur w).

          (* Lemma 2.11.8 *)
pose proof (uni_choice _ t1 t2) as t3.
          (* Theorem 2.11.6 *)
destruct (choice_thm _ t3) as [g t].
exists g.
intro z.
cut (Trunc -1 (exists c: A, (class_of _ c = g (h z)) * (h c = h z))).
refine (Trunc_rec _).
refine (sig_ind _ _ _ _).
intro c.
refine (prod_ind _ _).
intros E1 E2. (* Here, E1 and E2 are equations 
                 (4.23) *)

assert (BehEquiv c z) as t4.
              (* Lemma 2.8.23 *)
  refine (equiv_propresize _ _). 
  refine (tr _).
  exists B.
  exists Bcalg.
  exists h.  
  exists h.
  split.
  split.
  split.
  split.
  exact hmor.
  exact hmor.
  exact hsur.
  exact hsur.
  exact E2.

         (* By higher constructor for quotients *)
pose proof (related_classes_eq BehEquiv t4) as t5.
rewrite <- t5.
exact E1.

exact (t (h z)).
Qed.

(* Lemma 4.3.25 *)
Global Instance Fin_is_coalg {fext: Funext} {pres: PropResize} {H: Type -> Type} 
{FH: FunctorStr H} {sets: PreservesSets H} (A: Type) {Acalg: IsCoAlg A H} : 
  IsCoAlg (Fin A) H.
Proof. (* Recursion principle for quotients
          Lemma 2.11.26 *)
set (h := (map H (class_of BehEquiv)) o (Out A)).
refine (quotient_rec BehEquiv h _).

intros a b. (* Lemma 2.8.24 *)
refine (prop_resize_rec _). 
refine (Trunc_rec _).
intro h1.
       (* Lemma 4.3.21 *)
destruct (behavior_equiv_one_morph _ _ h1) as [Q t1].
destruct t1 as [Qcalg t2].
destruct t2 as [q t3].
destruct t3 as [t4 t5].
destruct t4 as [qmor qsur].
       (* Lemma 4.3.24 *)
destruct (class_of_factor q qmor qsur) as [g E1].
pose proof (path_arrow _ _ E1) as E2.

unfold h.
rewrite E2.
rewrite comp_preser.
rewrite qmor.
rewrite t5.
rewrite <- qmor.
rewrite <- comp_preser.
reflexivity.
Defined.

(* Corollary 4.3.26 *)
Corollary class_of_coalg_morph {fext: Funext} {pres: PropResize} {H: Type -> Type} 
{FH: FunctorStr H} {sets: PreservesSets H} (A: Type) {Acalg: IsCoAlg A H} : 
       IsCoAlgMor (class_of BehEquiv).
Proof.
intro w. (* By computation *)
reflexivity.
Qed.

(* Lemma 4.3.27 *)
Lemma Fin_coind_beh_equiv {fext: Funext} {pres: PropResize} {H: Type -> Type} 
{FH: FunctorStr H} {sets: PreservesSets H} (A: Type) {Acalg: IsCoAlg A H} : 
 forall w y: Fin A, PurelyBehEquiv w y -> w = y.
Proof. 
     (* Apply quotient induction twice *)
refine (quotient_ind_prop BehEquiv _ _). 
intro w.
refine (quotient_ind_prop BehEquiv _ _).
intro y.
refine (sig_ind _ _ _ _).
intro T.
refine (sig_ind _ _ _ _).
intro Tcalg.
refine (sig_ind _ _ _ _).
intro h.
refine (sig_ind _ _ _ _).
intro g.
refine (prod_ind _ _).
refine (prod_ind _ _).
refine (prod_ind _ _).
refine (prod_ind _ _).
intros hmor gmor hsur gsur p1.
      (* By higher constructor for quotients *)
refine (related_classes_eq BehEquiv _). 
      (* Lemma 2.8.23 *)
refine (equiv_propresize _ _).
refine (tr _).
exists T.
exists Tcalg.
exists (h o (class_of BehEquiv)).
exists (g o (class_of BehEquiv)).

      (* Corollary 4.3.26 *)
pose proof (class_of_coalg_morph A) as clmor.
 
      (* Lemma 2.11.27 
         We need to tell Coq that we want the []: A -> A_F map,
         NOT the []: T -> T_F map, since this is what Coq will pick if we just write
         
         "pose proof (class_of_surjective BehEquiv)" 
      *)
pose proof (class_of_surjective (@BehEquiv _ _ _ A _)) as clsur.

split. 
split.
split.
split.

      (* Lemma 2.10.3 *)
exact (coalg_mor_compose (BuildCoAlgMor (class_of BehEquiv) clmor) 
                         (BuildCoAlgMor h hmor)
      ).

      (* Lemma 2.10.3 *)
exact (coalg_mor_compose (BuildCoAlgMor (class_of BehEquiv) clmor) 
                         (BuildCoAlgMor g gmor)
      ).

           (* Lemma 2.11.11 *)
exact (surjections_compose clsur hsur).

           (* Lemma 2.11.11 *)
exact (surjections_compose clsur gsur).

exact p1.
Qed.

(* Corollary 4.3.28 *)
Corollary Fin_coind_bisim {fext: Funext} {pres: PropResize} {H: Type -> Type} 
{FH: FunctorStr H} {sets: PreservesSets H} (A: Type) {Acalg: IsCoAlg A H} : 
 forall w y: Fin A, Bisim w y -> w = y.
Proof.
intros w y h1.
    (* Lemma 4.3.20 *)
pose proof (bisim_implies_beh_equiv w y h1) as p1.
    (* Lemma 4.3.27 *)
exact (Fin_coind_beh_equiv A w y p1).
Qed.

(* Theorem 4.3.29(i) *)
Theorem Fin_is_ll_fin_coalg {fext: Funext} {pres: PropResize} {H: Type -> Type} 
{FH: FunctorStr H} {sets: PreservesSets H} (A: Type) {WA: IsLLWfinCoAlg A H} : 
 IsLLFinCoAlg (Fin A) H.
Proof. (* By Lemma 4.3.25 we know "Fin A" is a CoAlg *)
refine (BuildIsLLFinCoAlg (Fin_is_coalg A) _).
intros restriction B BCoAlg. 

                (* Existence *)
                (* There is a morphism from B to A, since A is a LLWfinCoAlg.
                  Notice the accessor function "llwfin_coalg_pr" is playing the role
                  of term "m" in the report *)
pose proof (llwfin_coalg_pr A B) as mor_from_B.
set (h := (class_of BehEquiv) o mor_from_B). (* Lemma 4.3.26 *)
pose proof (class_of_coalg_morph A) as cl_mor.
                    (* Lemma 2.10.3 *)
pose proof (coalg_mor_compose mor_from_B (BuildCoAlgMor (class_of BehEquiv) cl_mor)) as w1.
change (IsCoAlgMor h) in w1.

refine (BuildContr _ (BuildCoAlgMor h w1) _).

               (* Uniqueness *)
               (* Although we are using induction on type CoAlgMor, this is just induction
                  on a sigma in disguise, since records ARE sigmas. *)
induction y as [g w2].
          (* Since records are equivalent to Sigma types, we will prove instead that
             pairs (h;w1), (g;w2) are identifiable. Then, we will use the equivalence
             provided by Lemma coalgmor_as_sigma to conclude the required identity *) 
  assert ((h;w1) = (g;w2)) as morph_eq.
         (* Lemma 2.8.14 *)
  refine (path_sigma_hprop _ _ _).
         (* We have to do this to help the automatic prover in noticing that what we
            want to prove IS a mere proposition *)
  unfold IsCoAlgMor.
  exact _.
  simpl. (* Apply function extensionality *) 
  apply path_arrow.
  intro w. (* Corollary 4.3.28 *)
  refine (Fin_coind_bisim _ _ _ _).
  
  transparent assert (R: ((Fin A) * (Fin A) -> Type)).
    refine (prod_ind _ _).
    exact (fun a b => exists c: B, (a = h c) * (b = g c)).

  exists R.
  split.
  exact (w ; (idpath, idpath)).
  intros m n.
  refine (sig_ind _ _ _ _).
  intro c.
  refine (prod_ind _ _).
  intros p1 p2. (* Here, p1 and p2 represent Equations (4.27) 
                   in the report *)
  set (k r := ( (h r, g r) ; (r ; (idpath, idpath))) : {z: (Fin A) * (Fin A) & R z}).
  set (t := map H k (Out B c)).
  exists t.
  split.

  unfold t. (* Functoriality of H *)
  rewrite <- comp_preser. (* By definition of k and computation *)
  change (Out (Fin A) m = map H h (Out B c)). (* By Diagram (4.25) *)
  rewrite w1. (* By Equations (4.27) *)
  rewrite <- p1. (* By Definition of "Fin A" *)
  reflexivity.

  unfold t. (* Functoriality of H *)
  rewrite <- comp_preser. (* By definition of k and computation *)
  change (Out (Fin A) n = map H g (Out B c)). (* By Diagram (4.26) *)
  rewrite w2. (* By Equations (4.27) *)
  rewrite <- p2.
  reflexivity.

       (* Apply the equivalence between records and sigmas *)
exact (ap (coalgmor_as_sigma B (Fin A)) morph_eq).
Defined.

(* Theorem 4.3.29(ii) 

This is identical to the previous theorem. We omit comments. *)
Theorem Fin_is_fin_coalg {fext: Funext} {pres: PropResize} {H: Type -> Type} 
{FH: FunctorStr H} {sets: PreservesSets H} (A: Type) {WA: IsWfinCoAlg A H} : 
 IsFinCoAlg (Fin A) H.
Proof.
refine (BuildIsFinCoAlg (Fin_is_coalg A) _).
intros B BCoAlg. 
                (* Existence *)
pose proof (wfin_coalg_pr A B) as mor_from_B.
set (h := (class_of BehEquiv) o mor_from_B).
pose proof (class_of_coalg_morph A) as cl_mor.
pose proof (coalg_mor_compose mor_from_B (BuildCoAlgMor (class_of BehEquiv) cl_mor)) as w1.
change (IsCoAlgMor h) in w1.

refine (BuildContr _ (BuildCoAlgMor h w1) _).

               (* Uniqueness *)
induction y as [g w2].
  assert ((h;w1) = (g;w2)) as morph_eq.
  refine (path_sigma_hprop _ _ _).
  unfold IsCoAlgMor.
  exact _.
  simpl. 
  apply path_arrow.
  intro w.
  refine (Fin_coind_bisim _ _ _ _).
  
  transparent assert (R: ((Fin A) * (Fin A) -> Type)).
    refine (prod_ind _ _).
    exact (fun a b => exists c: B, (a = h c) * (b = g c)).

  exists R.
  split.
  exact (w ; (idpath, idpath)).
  intros m n.
  refine (sig_ind _ _ _ _).
  intro c.
  refine (prod_ind _ _).
  intros p1 p2.
  set (k r := ( (h r, g r) ; (r ; (idpath, idpath))) : {z: (Fin A) * (Fin A) & R z}).
  set (t := map H k (Out B c)).
  exists t.
  split.

  unfold t.
  rewrite <- comp_preser.
  change (Out (Fin A) m = map H h (Out B c)).
  rewrite w1. 
  rewrite <- p1.
  reflexivity.

  unfold t. 
  rewrite <- comp_preser. 
  change (Out (Fin A) n = map H g (Out B c)).
  rewrite w2.
  rewrite <- p2.
  reflexivity.

exact (ap (coalgmor_as_sigma B (Fin A)) morph_eq).
Defined.

(* Corollary 4.3.30 *)
Corollary functor_has_llfin_coalg {fext: Funext} {pres: PropResize} (H: Type -> Type) 
{FH: FunctorStr H} {sets: PreservesSets H} : LLFinCoAlg H.
Proof. (* It has a LLWfinCoAlg by Lemma 4.3.6 *)
destruct (functor_has_llwfincoalg H) as [W llwfincoalg_pr].
       (* By Theorem 4.3.29(i), 
          "Fin W" is a LLFinCoAlg *)
exact (BuildLLFinCoAlg (Fin W) (Fin_is_ll_fin_coalg W)).
Defined.

(*----- Subsection 4.3.3 --------*)

(* Theorem 4.3.31 *)
Theorem pow_without_fin_coalg {univ: Univalence} {pres: PropResize} : ~(FinCoAlg Pow).
Proof.
intro A. (* Lemma 4.3.9 *)
pose proof (lambek_fin_coalg A) as fixp.
         (* Lemma 2.8.20 *)
exact (cantor A fixp).
Qed.

(* Corollary 4.3.32 *)
Corollary pow_without_wfin_coalg {univ: Univalence} {pres: PropResize} : ~(WfinCoAlg Pow).
Proof.
intro A. (* Theorem 4.3.29(ii) *)
pose proof (Fin_is_fin_coalg A) as Afin.
         (*  Theorem 4.3.31 *)
exact (pow_without_fin_coalg (BuildFinCoAlg (Fin A) Afin)).
Qed.

(* Corollary 4.3.33 *)
Corollary llfin_coalg_not_fixpoint {univ: Univalence} {pres: PropResize} (A: Type) 
{Allfin: IsLLFinCoAlg A Pow} : ~(Pow A <~> A).
Proof. (* Lemma 2.8.20 *)
exact (cantor A).
Qed.

(*----- Subsection 4.3.4 --------*)

Section Example_stream.

(* We will assume function extensionality and propresize on this section *)
Context {fext: Funext}
        {propres: PropResize}.

(* Definition 4.3.34 *)
Definition StreamF (A: Type) (Y: Type) := A * Y.

(* Lemma 4.3.35 *)
Local Instance StreamF_is_functor (A: Type) : FunctorStr (StreamF A).
Proof.
transparent assert (
     mapStreamF: (forall C D: Type, (C -> D) -> StreamF A C -> StreamF A D)
).
  intros C D f. (* Define map by recursion on product types *)
  refine (prod_ind _ _).
  exact (fun (o': A) (s: C) => (o', f s)).

refine (BuildFunctorStr mapStreamF _ _).

       (* Identity mapping case *)
intro C. (* By induction on product types *)
refine (prod_ind _ _).
intros a c. (* By computation *)
reflexivity.
          (* Function composition mapping case *)
intros B C D g h. (* By induction on product types *)
refine (prod_ind _ _).
intros a b. (* By computation *)
reflexivity.
Defined.

(* This is the set preservation part of 
   Lemma 4.3.35

   We do not need to prove that StreamF preserves levels, as it is handled 
   automatically by Coq. *)
Local Instance StreamF_preserves_sets (A: Type) {setA: IsHSet A} : 
 PreservesSets (StreamF A).
Proof.
intros X setX. (* Coq automatically proves it *)
exact _.
Defined.

(* Definition 4.3.36

   We obtain it from Corollary 4.3.30 *)
Definition Stream (A: Type) {setA: IsHSet A} := functor_has_llfin_coalg (StreamF A).


(* We extract the Out function from Stream A because Coq behaves a bit dumb 
   if we attempt to use the expression "Out (Stream A)" inside more complex 
   expressions. So, we have to help Coq a bit. *)
Definition Out_Stream (A: Type) {setA: IsHSet A} := Out (Stream A).

(* Definition 4.3.37 *)
Definition head_Stream {A: Type} {setA: IsHSet A} (s: Stream A) : A := 
  fst (Out_Stream A s).

(* Definition 4.3.37 *)
Definition tail_Stream {A: Type} {setA: IsHSet A} (s: Stream A) : Stream A :=
 snd (Out_Stream A s).

(* Theorem 4.3.38 *)
Theorem Stream_coind {A: Type} {setA: IsHSet A} (w y: Stream A) : 
 (exists R: Stream A -> Stream A -> Type, 
       (R w y) * 
       (forall m n: Stream A, R m n -> 
                (head_Stream m = head_Stream n) * 
                (R (tail_Stream m) (tail_Stream n))
       )
 ) -> w = y.
Proof.
refine (sig_ind _ _ _ _).
intro R.
refine (prod_ind _ _).
intros h1 h2. (* Corollary 4.3.28 *)
apply Fin_coind_bisim.
set (S p := R (fst p) (snd p)).
exists S.
split.
exact h1.
intros m n p1.
pose proof (fst (h2 m n p1)) as p2.
pose proof (snd (h2 m n p1)) as p3.
set (t := (head_Stream m, ( (tail_Stream m, tail_Stream n) ; p3)) : 
               A * {z: (Stream A) * (Stream A) & S z}).
exists t.
split.
        (* Make the expression more readable by folding definitions *)
change (Out_Stream A m = map (StreamF A) (fst o pr1) t).
        (* By definition of "t", "map (StreamF A)" and projections *)
change (Out_Stream A m = (head_Stream m , tail_Stream m)).
unfold head_Stream.
unfold tail_Stream. (* Lemma 2.6.1 *)
rewrite eta_prod.
reflexivity.

        (* Make the expression more readable by folding definitions *)
change (Out_Stream A n = map (StreamF A) (snd o pr1) t).
        (* By definition of "t", "map (StreamF A)" and projections *)
change (Out_Stream A n = (head_Stream m , tail_Stream n)).
rewrite p2.
unfold head_Stream.
unfold tail_Stream. (* Lemma 2.6.1 *)
rewrite eta_prod.
reflexivity.
Qed.

(* Theorem 4.3.39 *)
Theorem Stream_coiter {A D: Type} {setA: IsHSet A} (h: D -> A) (t: D -> D) : 
 Contr (exists f: D -> Stream A, 
    forall w: D, (head_Stream (f w) = h w) * (tail_Stream (f w) = f (t w))
 ).
Proof.
set (DCoAlg := (fun d: D => (h d, t d)): IsCoAlg D (StreamF A)).
destruct (llfin_coalg_pr (Stream A) D) as [mor u_unique].
destruct mor as [u u_mor]. (* So, u: D -> Stream A is a unique morphism.
        Here, "u_mor" is Diagram (4.29) 
        And "u_unique" is the proof that u is unique. *)
                
             (* Existence *)
assert (forall w : D, (head_Stream (u w) = h w) * (tail_Stream (u w) = u (t w))) as w1.
  intro w.
  assert (Out_Stream A (u w) = (h w , u (t w))) as p1.
        (* By definition of "Out D" and "map (StreamF A)". *)
    change (Out_Stream A (u w) = map (StreamF A) u (Out D w)).
        (* u is morphism *)
    exact (u_mor w)^.
  split.  (* Apply fst to both sides of p1 and by definition of head_Stream  *)
  exact (ap fst p1).
        (* Apply snd to both sides of p1 and by definition of tail_Stream  *)
  exact (ap snd p1).

refine (BuildContr _ (u ; w1) _).

             (* Uniqueness *)
refine (sig_ind _ _ _ _).
intros g w2. (* Here, "w2" is acting as Equations 
                (4.30) *)
             (* Lemma 2.8.14 *)
refine (path_sigma_hprop _ _ _).
simpl.
assert (IsCoAlgMor g) as q2. 
  intro w. (* Corollary 2.6.25 *)
  apply path_prod. (* Simplify by computation *)
  change (h w = head_Stream (g w)).
             (* By Equations (4.30) *)
  exact (fst (w2 w))^.

             (* Simplify by computation *)
  change (g (t w) = tail_Stream (g w)).
             (* By Equations (4.30) *)
  exact (snd (w2 w))^.
         
        (* So, by uniqueness of u, we must have u = g *)
exact (ap coalg_mor_fun (u_unique (BuildCoAlgMor g q2))).
Qed.

(* Theorem 4.3.40 
   
   Here, nat are the naturals as defined in HoTT library. *)
Theorem Stream_equiv_to_nat_indexed_functions (A: Type) {setA: IsHSet A} : 
  (Stream A) <~> (nat -> A).
Proof. 
transparent assert (iter: (forall C: Type, (C -> C) -> nat -> C -> C)).
  intros C f.
  refine (nat_ind _ _ _).  
  exact idmap. (* This is the 0 case. "iter f 0 := idmap" *)
  intros n prev.
  exact (prev o f). (* This is the "successor" case. 
                       "iter f (succ n) := (iter f n) o f" *)

set (f1 := fun (s: Stream A) (n: nat) => head_Stream (iter _ tail_Stream n s)).
        (* The backward function is defined using coiteration for Stream A. *)
destruct (@center _ (Stream_coiter (fun g: nat -> A => g 0)
                                   (fun g: nat -> A => g o S)
                    )
         ) as [f2 f2pr].

         (* Now, we proceed to prove the equivalence. 
            We use Lemma 2.6.17 *)
refine (equiv_adjointify f1 f2 _ _).

intro g. (* By function extensionality *)
apply path_arrow.
cut (forall (n: nat) (t: nat -> A), f1 (f2 t) n = t n).
intros p1 n.
exact (p1 n g). (* By induction on nat *)
refine (nat_ind _ _ _).
 intro t. (* Simplify by computation *)
 change (head_Stream (f2 t) = t 0). (* By definition of f2 *)
 exact (fst (f2pr t)).
 
 intros n ind r. (* Simplify by computation *)
 change (f1 (tail_Stream (f2 r)) n = r (S n)). (* By definition of f2 *)
 rewrite (snd (f2pr r)). (* Apply the inductive hypothesis *)
 rewrite ind.
 reflexivity.

intro s. (* By coinduction on "Stream A" *)
apply Stream_coind.
set (R a b := exists w: Stream A, (a = f2 (f1 w)) * (b = w)).
exists R.
split.
exact (s ; (idpath, idpath)).
intros m n.
refine (sig_ind _ _ _ _).
intro w.
refine (prod_ind _ _).
intros q1 q2. (* Here, "q1" and "q2" are Equations 
                 (4.34) *)
split.

rewrite q1. (* By definition of f2 *)
rewrite (fst (f2pr (f1 w))). (* Simplify *)
change (head_Stream w = head_Stream n).
exact (ap head_Stream q2^).

assert (tail_Stream m = f2 (f1 (tail_Stream n))) as p1.
  rewrite q1. (* By definition of f2 *)
  rewrite (snd (f2pr (f1 w))). (* Simplify *)
  change (f2 (f1 (tail_Stream w)) = f2 (f1 (tail_Stream n))).
  rewrite <- q2.
  reflexivity.
exact (tail_Stream n ; (p1 , idpath)).
Qed.

End Example_stream.


(* ---------------------------------------------------------------------------
 inf201_Dupre_Jaunatre_Raspail_projet.ml : Projet d'INF201

 Alexandre Dupré <alexandre.dupre@etu.univ-grenoble-alpes.fr> \
 Maxime Jaunatre <maxime.jaunatre@etu.univ-grenoble-alpes.fr>  > Groupe D
 Clément Raspail <clement.raspail@etu.univ-grenoble-alpes.fr> /

 -----------------------------------------------------------------------------
*)

(* -------------- Partie 2 : Ensemble --------------*)

(* Définition des types *)

type 'a ensemble = Ve | Ce of 'a * 'a ensemble ;;

(* Cardinalité
|SPÉCIFICATION 
| - Profil cardinal ∶ 'a ensemble -> int
| - Sémantique : cardinal(ens) renvois le nombre d'éléments dans l'ensemble ens.
| - Exemple :
|   (1) cardinal (Ce(1,Ve)) = 1
|   (2) caridnal Ve = 0
|   (3) cardinal (Ce (1, Ce (2, Ve))) = 2
|REALISATION
| - Implémentation :
*)
let rec cardinal (ens:'a ensemble) : int =
    match ens with
    | Ve -> 0
    | Ce(x, sens) -> 1 + cardinal (sens)
;;

assert(cardinal(Ve) = 0);; (* - : unit = () *)
assert(cardinal(Ce(1,Ve)) = 1);; (* - : unit = () *)
assert(cardinal(Ce (1, Ce (2, Ve))) = 2);; (* - : unit = () *)
assert(cardinal(Ce (1.5, Ce (3.14, Ve))) = 2);; (* - : unit = () *)
assert(cardinal(Ce ("hello", Ce ("world", Ve))) = 2);; (* - : unit = () *)

(*Appartenance*)
(*
|SPÉCIFICATION
| - Profil appartient ∶ 'a -> 'a ensemble -> bool
| - Sémantique : appartient(elt ens) indique si l'élément elt appartient à l'ensemble ens
| - Exemple :
|   (1) appartient 1 (Ce (1, Ce (2, Ve))) = true
|   (2) appartient 3. (Ce (1., Ce (2., Ce (4., Ve)))) = false
|   (3) appartient false (Ce (true, Ce (true, Ce (false, Ve)))) = true
|REALISATION
| - Implémentation :
*)
let rec appartient (elt: 'a) (ens: 'a ensemble) : bool =
    match ens with
    | Ve -> false
    | Ce(x,y) when x = elt -> true
    | Ce(x,y) -> false || appartient elt y 
  ;;

  assert(appartient 1 (Ce (1, Ce (2, Ve))));; (* - : unit = () *)
  assert(not (appartient 3. (Ce (1., Ce (2., Ce (4., Ve))))));; (* - : unit = () *)
  assert(appartient false (Ce (true, Ce (false, Ve))));; (* - : unit = () *)
  assert(not(appartient "ahel" (Ce ("hello", Ce ("world", Ve)))));; (* - : unit = () *)

  
(* Inclusion *)
(* 
|SPÉCIFICATION
| - Profil inclus ∶ 'a ensemble -> 'a ensemble -> bool
| - Sémantique : (inclus ens1 ens2) est vrai si et seulement si ens1 inclus dans ens2
| - Exemple :
|   (1) inclus (Ce(1,Ve)) (Ce(1,Ce(2,Ve))) = true
|   (2) inclus (Ce(1,Ve)) (Ce(2,Ce(3,Ve))) = false
|   (3) inclus Ve Ve = true
|REALISATION
| - Implémentation :
*)
let rec inclus (e1:'a ensemble) (e2:'a ensemble): bool =
  match e1 with
  | Ce(x,y) -> appartient x e2 && inclus y e2
  | Ve -> true
;;

assert(inclus (Ce(1,Ve)) (Ce(1,Ce(2,Ve))));; (* - : unit = () *)
assert(not (inclus (Ce(1,Ve)) (Ce(2,Ce(3,Ve)))));; (* - : unit = () *)
assert(inclus (Ce(1,Ve)) (Ce(1,Ce(2,Ve))));; (* - : unit = () *)
assert(not (inclus (Ce("Never",Ce ("Gonna",Ce("Give",Ve)))) (Ce("You",Ce("Up",Ve)))));; (* - : unit = () *)


(* Ajout
|SPÉCIFICATION
| - Profil ajoute ∶ 'a -> 'a ensemble -> 'a ensemble 
| - Sémantique : ajoute(a ens) Ajoute un élément a à un ensemble ens respectant la contrainte de non répétition des éléments
|                Dépend de inclusion
| - Exemple 
|   (1) ajoute (3 (Ce(1,Ve))) = Ce(3,Ce(1,Ve))
|   (2) ajoute ("hello" (Ce("world",Ve))) = Ce("hello",Ce("world",Ve))
|   (3) ajoute (3 Ve) = Ce(3,Ve)
|   (4) ajoute ("Immortal" (Ce("Immortal",Ve))) = Ce("Immortal",Ve)
|REALISATION
| - Implémentation :
*)
let ajoute (elt: 'a) (ens: 'a ensemble) : 'a ensemble =
    if appartient elt ens then
        ens
    else 
        Ce(elt, ens)
;;

assert(ajoute 3 (Ce(1,Ve)) = (Ce(3, Ce(1, Ve))));; (* - : unit = () *)
assert(ajoute 3 Ve = (Ce(3, Ve)) );; (* - : unit = () *)
assert(ajoute "Immortal" (Ce("Immortal",Ve)) = (Ce("Immortal",Ve)));; (* - : unit = () *)


(* Suppression
|SPÉCIFICATION
| - Profil supprime ∶ 'a -> 'a ensemble -> 'a ensemble 
| - Sémantique : supprime(a ens) enlève l'élément a de l'ensemble ens
| - Exemple 
|   (1) supprime 3 (Ce(1,Ce(3,Ve))) = Ce(1,Ve)
|   (2) supprime "hello" (Ce("world",Ce("hello",Ve))) = Ce("world",Ve)
|   (3) supprime false (Ce(true,Ce(false,Ve))) = Ce(true,Ve)
|REALISATION
| - Implémentation :
*)
let rec supprime (elt:'a) (ens:'a ensemble) : 'a ensemble =
  if not(appartient elt ens) then ens else
    match ens with
    | Ve -> Ve
    | Ce(x,Ve) when x = elt -> Ve
    | Ce(x,Ve) -> Ce(x,Ve)
    | Ce(x, Ce(y,z)) when y = elt -> Ce(x,z)
    | Ce(x, Ce(y,z)) when x = elt -> Ce(y,z)
    | Ce(x, Ce(y,z)) -> Ce(x,supprime elt (Ce(y,z)))
  ;;

  assert(supprime 3 (Ce(1,Ce(3,Ve))) = Ce(1,Ve));; (* - : unit = () *)
  assert(supprime "hello" (Ce("world",Ce("hello",Ve))) = Ce("world",Ve));; (* - : unit = () *)
  assert(supprime false (Ce(true,Ce(false,Ve))) = Ce(true,Ve));; (* - : unit = () *)
  assert(supprime "pas" (Ce ("Je", (Ce ("suis", Ce ("pas", (Ce ("fort", Ce ("en", Ce ("ocaml", Ve))))))))) = (Ce ("Je", (Ce ("suis", (Ce ("fort", Ce ("en", Ce ("ocaml", Ve)))))))));; (* - : unit = () *)

  
(* Egalité
|SPÉCIFICATION
| - Profil egaux ∶ 'a ensemble -> 'a ensemble -> bool
| - Sémantique : (egaux ens1 ens2) est vrai si et seulement si ens1 et ens1 ont les mêmes éléments.
| - Exemple 
|   (1) egaux (Ce(1, Ce(2, Ve))) (Ce(2, Ce(1, Ve))) = true
|   (2) egaux Ve Ve = true
|   (3) egaux (Ce("Hello",Ve)) (Ce("Hello",Ce("World",Ve))) = false
|REALISATION
| - Implémentation :
*)
let rec egaux (ens1:'a ensemble) (ens2:'a ensemble):bool =
  if (cardinal ens1) <> (cardinal ens2) then false
  else
    match ens1 with
    | Ce(x,y) -> (appartient x ens2) && (egaux y (supprime x ens2))
    | Ve -> true
;;
  
assert(egaux Ve Ve);; (* - : unit = () *)
assert(egaux (Ce(1, Ce(2, Ve))) (Ce(2, Ce(1, Ve))));; (* - : unit = () *)
assert(not (egaux (Ce("Hello",Ve)) (Ce("Hello",Ce("World",Ve)))));; (* - : unit = () *)
assert(not (egaux (Ce(1, Ce(2,Ce(3,Ve)))) (Ce(2, Ce(1, Ve)))));; (* - : unit = () *)


(* Intersection
|SPÉCIFICATION
| - Profil intersection ∶ 'a ensemble -> 'a ensemble -> 'a ensemble 
| - Sémantique : intersection (ens1 ens2) renvois l'ensemble avec seulement les éléments compris dans les deux ensembles précisés
| - Exemple 
|   (1) intersection (Ce(1, Ce(2, Ve))) (Ce(2, Ce(1, Ve))) = (Ce(2, Ce(1, Ve)))
|   (2) intersection Ve Ve = Ve
|   (3) intersection (Ce("Hello",Ve)) (Ce("Hello",Ce("World",Ve))) = (Ce("Hello",Ve))
|REALISATION
| - Implémentation :
*)
let rec intersection (ens1 : 'a ensemble) (ens2 : 'a ensemble) : 'a ensemble =
    if egaux ens1 ens2 then ens1
    else
        match ens1 with
        | Ce(x,y) -> if not (appartient x ens2) then intersection y ens2 else Ce(x,intersection y ens2)
        | Ve -> Ve   
;;

assert( intersection (Ce(1, Ce(2, Ve))) (Ce(2, Ce(1, Ve))) = (Ce(1, Ce(2, Ve))) );; (* - : unit = () *)
assert( intersection Ve Ve = Ve );; (* - : unit = () *)
assert(  intersection (Ce("Hello",Ve)) (Ce("Hello",Ce("World",Ve))) = (Ce("Hello",Ve)) );; (* - : unit = () *)
    

(* Union
|SPÉCIFICATION
| - Profil union ∶ 'a ensemble -> 'a ensemble -> 'a ensemble
| - Sémantique : (union ens1 ens2) est l’ensemble ens1 ∪ ens2, c’est-à-dire l’ensemble des éléments appartenant à ens1 ou à ens2.
| - Exemple 
|   (1) union (Ce(1, Ce(2, Ve))) (Ce(2, Ce(1, Ve))) = (Ce(2, Ce(1, Ve)))
|   (2) union (Ce(1, Ce(2, Ve))) (Ce(3, Ce(4, Ve))) = (Ce(1, Ce(2, Ce(3, Ce(4, Ve)))))
|   (3) union (Ce("Hello",Ve)) (Ce("Hello",Ce("World",Ve))) = (Ce("Hello",Ce("World",Ve)))
|REALISATION
| - Implémentation :
*)
let rec union (ens1:'a ensemble) (ens2:'a ensemble):'a ensemble =
  match ens1 with
  | Ce(x,y) -> union y (ajoute x ens2)
  | Ve -> ens2
;;

assert(union (Ce(1, Ce(2, Ve))) (Ce(2, Ce(1, Ve))) = (Ce(2, Ce(1, Ve))));; (* - : unit = () *)
assert(union (Ce(3, Ce(4, Ve))) (Ce(2, Ce(1, Ve))) = (Ce(4, Ce(3, Ce(2, Ce(1, Ve))))));; (* - : unit = () *)
assert(union (Ce("Hello",Ve)) (Ce("Hello",Ce("World",Ve))) = (Ce("Hello",Ce("World",Ve))));; (* - : unit = () *)

  
(* Différence
|SPÉCIFICATION
| - Profil dif ∶ 'a ensemble -> 'a ensemble -> 'a ensemble
| - Sémantique : (dif ens1 ens2) est l’ensemble ens1 privé de ens2, c’est-à-dire l’ensemble des éléments appartenant à ens1 mais pas ens2.
| - Exemple 
|   (1) dif (Ce(2, Ve)) (Ce(2, Ce(1, Ve))) = Ve
|   (2) dif (Ce(1., Ce(2., Ve))) (Ce(3., Ce(4., Ve))) = (Ce(1., Ce(2., Ve)))
|   (3) dif (Ce("Hello",Ce("IamAI",Ve))) (Ce("Hello",Ce("World",Ve))) = Ce("IamAI",Ve)
|REALISATION
| - Implémentation :
*)
let rec dif (ens1 : 'a ensemble) (ens2 : 'a ensemble) : 'a ensemble =
  if egaux ens1 ens2 then Ve else
  match ens1 with
  | Ve -> Ve
  | Ce(x,y) when (appartient x ens2) -> dif y ens2
  | Ce(x,y) -> Ce(x, dif y ens2)
;;

assert(dif (Ce(2, Ve)) (Ce(2, Ce(1, Ve))) = Ve);; (* - : unit = () *)
assert(dif (Ce(1., Ce(2., Ve))) (Ce(3., Ce(4., Ve))) = (Ce(1., Ce(2., Ve))));; (* - : unit = () *)
assert(dif (Ce("Hello",Ce("IamAI",Ve))) (Ce("Hello",Ce("World",Ve))) = Ce("IamAI",Ve));; (* - : unit = () *)
  
  
(* Différence symétrique
|SPÉCIFICATION
| - Profil difsym ∶ 'a ensemble -> 'a ensemble -> 'a ensemble
| - Sémantique : (difsym ens1 ens2) est l’union ens1 ens2 privé de l'intersection ens1 ens2, c’est-à-dire l’ensemble des éléments appartenant à ens1 et ens2 mais pas aux deux.
| - Exemple 
|   (1) difsym (Ce(2, Ve)) (Ce(2, Ce(1, Ve))) = (Ce(1, Ve))
|   (2) difsym (Ce(2., Ce(1., Ve))) (Ce(3., Ce(4., Ve))) = (Ce(1., Ce(2., Ce( 3. , Ce( 4., Ve )))))
|   (3) difsym (Ce("Hello", Ce("John", Ve))) (Ce("Hello",Ce("World",Ve))) = (Ce("John", Ce("World", Ve)))
|REALISATION
| - Implémentation :
*)
let difsym (ens1 : 'a ensemble) (ens2 : 'a ensemble) : 'a ensemble =
    dif (union ens1 ens2) (intersection ens1 ens2)
;;

assert( difsym (Ce(2, Ve)) (Ce(2, Ce(1, Ve))) = (Ce(1, Ve)) );;
assert( difsym (Ce(2., Ce(1., Ve))) (Ce(3., Ce(4., Ve))) = (Ce(1., Ce(2., Ce( 3. , Ce( 4., Ve ))))) );;
assert( difsym (Ce("Hello", Ce("John", Ve))) (Ce("Hello",Ce("World",Ve))) = (Ce("John", Ce("World", Ve))) );;


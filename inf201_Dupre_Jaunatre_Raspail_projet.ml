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

(* TODO !
Suppression A
Egalite
Intersection
Union
Difference
Difference symetrique
*)


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

assert(cardinal(Ve) = 0);; (*- : unit = ()*)
assert(cardinal(Ce(1,Ve)) = 1);; (*- : unit = ()*)
assert(cardinal(Ce (1, Ce (2, Ve))) = 2);; (*- : unit = ()*)
assert(cardinal(Ce (1.5, Ce (3.14, Ve))) = 2);; (*- : unit = ()*)
assert(cardinal(Ce ("hello", Ce ("world", Ve))) = 2);; (*- : unit = ()*)

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

  assert(appartient 1 (Ce (1, Ce (2, Ve))));; (*- : unit = ()*)
  assert(not (appartient 3. (Ce (1., Ce (2., Ce (4., Ve))))));; (*- : unit = ()*)
  assert(appartient false (Ce (true, Ce (false, Ve))));; (*- : unit = ()*)
  assert(not(appartient "hel" (Ce ("hello", Ce ("world", Ve)))));; (*- : unit = ()*)

  
(* Inclusion *)
(* 
|SPÉCIFICATION
| - Profil inclus ∶ 'a ensemble -> 'a ensemble -> bool
| - Sémantique : (inclus 𝑒𝑛𝑠1 𝑒𝑛𝑠2) est vrai si et seulement si 𝑒𝑛𝑠1 ⊂ 𝑒𝑛𝑠2
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

assert(inclus (Ce(1,Ve)) (Ce(1,Ce(2,Ve))));; (* - : unit = ()*)
assert(not (inclus (Ce(1,Ve)) (Ce(2,Ce(3,Ve)))));; (* - : unit = ()*)
assert(inclus (Ce(1,Ve)) (Ce(1,Ce(2,Ve))));; (* - : unit = ()*)
assert(not (inclus (Ce("Never",Ce ("Gonna",Ce("Give",Ve)))) (Ce("You",Ce("Up",Ve)))));; (* - : unit = ()*)


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

assert(ajoute 3 (Ce(1,Ve)) = (Ce(3, Ce(1, Ve))));; (* - : unit = ()*)
assert(ajoute 3 Ve = (Ce(3, Ve)) );; (* - : unit = ()*)
assert(ajoute "Immortal" (Ce("Immortal",Ve)) = (Ce("Immortal",Ve)));; (* - : unit = ()*)


(* Suppression
|SPÉCIFICATION
| - Profil supprime ∶ 'a -> 'a ensemble -> 'a ensemble 
| - Sémantique : supprime(a ens) enlève l'élément a de l'ensemble ens
| - Exemple 
|   (1) supprime (3 Ce(1,Ce(3,Ve))) = Ce(1,Ve)
|   (2) supprime ("hello" Ce("world",Ce("hello",Ve)) = Ce("world",Ve)
|   (3) supprime (false Ce(true,Ce(false,Ve))) = Ce(true,Ve)
|REALISATION
| - Implémentation :
*)
let rec supprime (elt:'a) (ens:'a ensemble) : 'a ensemble =
  if not(appartient elt ens) then ens else
    match ens with
    | Ve -> Ve
    | Ce(x, Ce(y,z)) when y = elt -> Ce(x,z)
    | Ce(x, Ce(y,z)) -> Ce(x,supprime elt Ce(y,z))
  ;;
    


(* Egalité
|SPÉCIFICATION
| - Profil egaux ∶ 'a -> 'a ensemble -> 'a ensemble 
| - Sémantique : (𝑒𝑔𝑎𝑢𝑥 𝑒𝑛𝑠1 𝑒𝑛𝑠2) est vrai si et seulement si 𝑒𝑛𝑠1 et 𝑒𝑛𝑠2 ont les mêmes éléments.
| - Exemple 
|   (1) egaux (Ce(1, Ce(2, Ve))) (Ce(2, Ce(1, Ve))) = vrai
|   (2) egaux Ve Ve = vrai
|   (3) ajoute (Ce("Hello",Vide)) (Ce("Hello",Ce("World",Ve))) = false
|REALISATION
| - Implémentation :
*)
(*let rec egaux (elt:'a) (ens:'a ensemble):'a ensemble =*)
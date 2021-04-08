(* ---------------------------------------------------------------------------
 inf201_Dupre_Jaunatre_Raspail_projet_partie2.ml : Projet d'INF201

 Alexandre Dupré <alexandre.dupre@etu.univ-grenoble-alpes.fr> \
 Maxime Jaunatre <maxime.jaunatre@etu.univ-grenoble-alpes.fr>  > Groupe D
 Clément Raspail <clement.raspail@etu.univ-grenoble-alpes.fr> /

 -----------------------------------------------------------------------------
*)

(* ---------- Partie 4 : Multi-ensembles  ----------*)

(* Q4. Définir en OCaml les types multielement 𝛼 et multiensemble 𝛼 *)

(* Définition des types *)

type 'a mutlielement = 'a list ;;
type 'a multiensemble = 'a list ;;



(* Q5. Réalisation des fonctions *)

(* Cardinalité
|SPÉCIFICATION 
| - Profil cardinal ∶ 'a ensemble -> int
| - Sémantique : cardinal(ens) renvois le nombre d'éléments dans l'ensemble ens.
| - Exemple :
|   (1) cardinal [1] = 1
|   (2) caridnal [] = 0
|   (3) cardinal [1;2] = 2 
|REALISATION
| - Implémentation :
*)
let rec cardinal (ens:'a ensemble) : int =
    match ens with
    | [] -> 0
    | x::fin -> 1 + (cardinal fin)
;;

assert(cardinal [] = 0);; (* - : unit = () *)
assert(cardinal [1] = 1);; (* - : unit = () *)
assert(cardinal [1;2] = 2);; (* - : unit = () *)
assert(cardinal [1,5;3,14] = 2);; (* - : unit = () *)
assert(cardinal ["hello";"world"] = 2);; (* - : unit = () *)


(* Occurence
|Spécification
|REALISATION
| - Implémentation :
*)

(*Appartenance*)
(*
|SPÉCIFICATION
| - Profil appartient ∶ 'a -> 'a ensemble -> bool
| - Sémantique : appartient(elt ens) indique si l'élément elt appartient à l'ensemble ens
| - Exemple :
|   (1) appartient 1 [1;2] = true
|   (2) appartient 3. [1.;2.;4.] = false
|   (3) appartient false [true;false] = true
|REALISATION
| - Implémentation :
*)
let rec appartient (elt: 'a) (ens: 'a ensemble) : bool =
  match ens with
  | [] -> false
  | x::y when x = elt -> true
  | x::y -> false || appartient elt y 
;;

  assert(appartient 1 [1;2]);; (* - : unit = () *)
  assert(not (appartient 3. [1.;2.;4.]));; (* - : unit = () *)
  assert(appartient false [true;false]);; (* - : unit = () *)
  assert(not(appartient "ahel" ["hello";"world"]));; (* - : unit = () *)


(* Inclusion *)
(* 
|SPÉCIFICATION
| - Profil inclus ∶ 'a ensemble -> 'a ensemble -> bool
| - Sémantique : (inclus ens1 ens2) est vrai si et seulement si ens1 inclus dans ens2
| - Exemple :
|   (1) inclus [1] [1;2] = true
|   (2) inclus [1] [2;3] = false
|   (3) inclus [] [] = true
|REALISATION
| - Implémentation :
*)
let rec inclus (e1:'a ensemble) (e2:'a ensemble): bool =
  match e1 with
  | x::y -> appartient x e2 && inclus y e2
  | [] -> true
;;

assert(inclus [1] [1;2]);; (* - : unit = () *)
assert(not (inclus [1] [2;3]));; (* - : unit = () *)
assert(not (inclus ["Never";"Gonna";"Give"] ["You";"Up"]));; (* - : unit = () *)


(* Ajout
|SPÉCIFICATION
| - Profil ajoute ∶ 'a -> 'a ensemble -> 'a ensemble 
| - Sémantique : ajoute(a ens) Ajoute un élément a à un ensemble ens respectant la contrainte de non répétition des éléments
|                Dépend de inclusion
| - Exemple 
|   (1) ajoute 3 [1] = [3;1]
|   (2) ajoute "hello" ["world"] = ["hello";"world"]
|   (3) ajoute 3 [] = [3]
|   (4) ajoute "Immortal" ["Immortal"] = ["Immortal"]
|REALISATION
| - Implémentation :
*)
let ajoute (elt: 'a) (ens: 'a ensemble) : 'a ensemble =
    if appartient elt ens then
        ens
    else 
        elt::ens
;;

assert(ajoute 3 [1] = [3;1]);; (* - : unit = () *)
assert(ajoute 3 [] = [3]);; (* - : unit = () *)
assert(ajoute "Immortal" ["Immortal"] = ["Immortal"]);; (* - : unit = () *)


(* Suppression
|SPÉCIFICATION
| - Profil supprime ∶ 'a -> 'a ensemble -> 'a ensemble 
| - Sémantique : supprime(a ens) enlève l'élément a de l'ensemble ens
| - Exemple 
|   (1) supprime 3 [1;3] = [1]
|   (2) supprime "hello" ["world";"hello"] = ["world"]
|   (3) supprime false [true;false] = [true]
|REALISATION
| - Implémentation :
*)
let rec supprime (elt:'a) (ens:'a ensemble) : 'a ensemble =
  if not(appartient elt ens) then ens else
    match ens with
    | [] -> []
    | x::[] when x = elt -> []
    | x::[] -> [x]
    | x::y::z when y = elt -> [x]@z
    | x::y::z when x = elt -> [y]@z
    | x::y-> [x]@(supprime elt y)
;;

assert(supprime 3 [1;3] = [1]);; (* - : unit = () *)
assert(supprime "hello" ["world";"hello"] = ["world"]);; (* - : unit = () *)
assert(supprime false [true;false] = [true]);; (* - : unit = () *)
assert(supprime "pas" ["Je";"suis";"pas";"fort";"en";"ocaml"] = ["Je";"suis";"fort";"en";"ocaml"]);; (* - : unit = () *)

  
(* Egalité
|SPÉCIFICATION
| - Profil egaux ∶ 'a ensemble -> 'a ensemble -> bool
| - Sémantique : (egaux ens1 ens2) est vrai si et seulement si ens1 et ens1 ont les mêmes éléments.
| - Exemple 
|   (1) egaux [1;2] [2;1] = true
|   (2) egaux [] [] = true
|   (3) egaux ["Hello"] ["Hello","World"] = false
|REALISATION
| - Implémentation :
*)
let rec egaux (ens1:'a ensemble) (ens2:'a ensemble):bool =
  if (cardinal ens1) <> (cardinal ens2) then false
  else
    match ens1 with
    | x::y -> (appartient x ens2) && (egaux y (supprime x ens2))
    | [] -> true
;;
  
assert(egaux [] []);; (* - : unit = () *)
assert(egaux [1;2] [2;1]);; (* - : unit = () *)
assert(not (egaux ["Hello"] ["Hello";"World"]));; (* - : unit = () *)
assert(not (egaux [1;2;3] [2;1]));; (* - : unit = () *)


(* Intersection
|SPÉCIFICATION
| - Profil intersection ∶ 'a ensemble -> 'a ensemble -> 'a ensemble 
| - Sémantique : intersection (ens1 ens2) renvois l'ensemble avec seulement les éléments compris dans les deux ensembles précisés
| - Exemple 
|   (1) intersection [1;2] [2;1] = [1;2]
|   (2) intersection [] [] = []
|   (3) intersection ["Hello"] ["Hello";"World"] = ["Hello"]
|REALISATION
| - Implémentation :
*)
let rec intersection (ens1 : 'a ensemble) (ens2 : 'a ensemble) : 'a ensemble =
    if egaux ens1 ens2 then ens1
    else
        match ens1 with
        | x::y -> if not (appartient x ens2) then intersection y ens2 else x::intersection y ens2
        | [] -> []   
;;

assert(intersection [1;2] [2;1] = [1;2]);; (* - : unit = () *)
assert(intersection [] [] = [] );; (* - : unit = () *)
assert(intersection ["Hello"] ["Hello";"World"] = ["Hello"]);; (* - : unit = () *)
    

(* Union
|SPÉCIFICATION
| - Profil union ∶ 'a ensemble -> 'a ensemble -> 'a ensemble
| - Sémantique : (union ens1 ens2) est l’ensemble ens1 ∪ ens2, c’est-à-dire l’ensemble des éléments appartenant à ens1 ou à ens2.
| - Exemple 
|   (1) union [1;2] [2;1] = [2;1]
|   (2) union [2;1] [3;4] = [1;2;3;4]
|   (3) union ["Hello"] ["Hello";"World"] = ["Hello";"World"]
|REALISATION
| - Implémentation :
*)
let rec union (ens1:'a ensemble) (ens2:'a ensemble):'a ensemble =
  match ens1 with
  | x::y -> union y (ajoute x ens2)
  | [] -> ens2
;;

assert(union [1;2] [2;1] = [2;1]);; (* - : unit = () *)
assert(union [2;1] [3;4] = [1;2;3;4]);; (* - : unit = () *)
assert(union ["Hello"] ["Hello";"World"] = ["Hello";"World"]);; (* - : unit = () *)

  
(* Différence
|SPÉCIFICATION
| - Profil dif ∶ 'a ensemble -> 'a ensemble -> 'a ensemble
| - Sémantique : (dif ens1 ens2) est l’ensemble ens1 privé de ens2, c’est-à-dire l’ensemble des éléments appartenant à ens1 mais pas ens2.
| - Exemple 
|   (1) dif [2] [2;1] = []
|   (2) dif [1;2] [3;4] = [1;2]
|   (3) dif ["Hello";"IamAI"] ["Hello";"World"] = ["IamAI"]
|REALISATION
| - Implémentation :
*)
let rec dif (ens1 : 'a ensemble) (ens2 : 'a ensemble) : 'a ensemble =
  if egaux ens1 ens2 then [] else
  match ens1 with
  | [] -> []
  | x::y when (appartient x ens2) -> dif y ens2
  | x::y -> [x]@dif y ens2
;;

assert(dif [2] [2;1] = []);; (* - : unit = () *)
assert(dif [1;2] [3;4] = [1;2]);; (* - : unit = () *)
assert(dif ["Hello";"IamAI"] ["Hello";"World"] = ["IamAI"]);; (* - : unit = () *)
  

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

assert(difsym [2] [2;1] = [1] );; (* - : unit = () *)
assert(difsym [2;1] [3;4] = [1;2;3;4]);; (* - : unit = () *)
assert(difsym ["Hello";"John"] ["Hello";"World"] = ["John";"World"]);; (* - : unit = () *)


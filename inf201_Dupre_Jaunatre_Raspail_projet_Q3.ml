(* ---------------------------------------------------------------------------
 inf201_Dupre_Jaunatre_Raspail_projet_Q3.ml : Projet d'INF201

 Alexandre Dupré <alexandre.dupre@etu.univ-grenoble-alpes.fr> \
 Maxime Jaunatre <maxime.jaunatre@etu.univ-grenoble-alpes.fr>  > Groupe D
 Clément Raspail <clement.raspail@etu.univ-grenoble-alpes.fr> /

 -----------------------------------------------------------------------------
*)

(* ---------- Partie 3 : Q3 Réusinage : listes OCaml et ordre supérieur  ----------*)

(* Définition des types *)

type 'a ensemble = 'a list ;;

(* Cardinalité
|SPÉCIFICATION 
| - Profil cardinale ∶ 'a ensemble -> int
| - Sémantique : cardinale(ens) renvois le nombre d'éléments dans l'ensemble ens.
| - Exemple :
|   (1) cardinale [1] = 1
|   (2) caridnale [] = 0
|   (3) cardinale [1;2] = 2 
|REALISATION
| - Implémentation :
*)
let cardinale (ens:'a ensemble) : int =
  List.fold_left (fun x _ -> x + 1) 0 ens
;;

assert(cardinale [] = 0);; (* - : unit = () *)
assert(cardinale [1] = 1);; (* - : unit = () *)
assert(cardinale [1;2] = 2);; (* - : unit = () *)
assert(cardinale [1,5;3,14] = 2);; (* - : unit = () *)
assert(cardinale ["hello";"world"] = 2);; (* - : unit = () *)

(*Appartenance*)
(*
|SPÉCIFICATION
| - Profil appartiente ∶ 'a -> 'a ensemble -> bool
| - Sémantique : appartiente(elt ens) indique si l'élément elt appartient à l'ensemble ens.
| - Exemple :
|   (1) appartiente 1 [1;2] = true
|   (2) appartiente 3. [1.;2.;4.] = false
|   (3) appartiente false [true;false] = true
|REALISATION
| - Implémentation :
*)
let appartiente (elt: 'a) (ens: 'a ensemble) : bool =
  let p = (fun x -> x=elt) in
  List.exists p ens
;;

assert(appartiente [] [[]]);; (* - : unit = () *)
assert(appartiente 1 [1;2]);; (* - : unit = () *)
assert(not (appartiente 3. [1.;2.;4.]));; (* - : unit = () *)
assert(appartiente false [true;false]);; (* - : unit = () *)
assert(not(appartiente "ahel" ["hello";"world"]));; (* - : unit = () *)
assert(appartiente "66" ["Order";"66"]);;


(* Inclusion *)
(* 
|SPÉCIFICATION
| - Profil incluse ∶ 'a ensemble -> 'a ensemble -> bool
| - Sémantique : (inclus ens1 ens2) est vrai si et seulement si ens1 inclus dans ens2.
| - Exemple :
|   (1) incluse [1] [1;2] = true
|   (2) incluse [1] [2;3] = false
|   (3) incluse [] [] = true
|REALISATION
| - Implémentation :
*)
let incluse (e1:'a ensemble) (e2:'a ensemble): bool =
  List.fold_right (fun x y -> (List.exists (fun elt -> elt=x) e2) && y) e1 true
;;

assert(incluse [] []);; (* - : unit = () *)
assert(incluse [1] [1;2]);; (* - : unit = () *)
assert(not (incluse [1] [2;3]));; (* - : unit = () *)
assert(not (incluse ["Never";"Gonna";"Give"] ["You";"Up"]));; (* - : unit = () *)


(* Suppression
|SPÉCIFICATION
| - Profil supprimee ∶ 'a -> 'a ensemble -> 'a ensemble 
| - Sémantique : supprimee(a ens) enlève l'élément a de l'ensemble ens
| - Exemple 
|   (1) supprimee 3 [1;3] = [1]
|   (2) supprimee "hello" ["world";"hello"] = ["world"]
|   (3) supprimee false [true;false] = [true]
|REALISATION
| - Implémentation :
*)
let supprimee (elt:'a) (ens:'a ensemble) : 'a ensemble =
  if not(appartiente elt ens) then ens else  
  let p = (fun x -> (x<>elt)) in
  List.filter p ens
;;

assert(supprimee [] [[]] = []);; (* - : unit = () *)
assert(supprimee 3 [1;3] = [1]);; (* - : unit = () *)
assert(supprimee "hello" ["world";"hello"] = ["world"]);; (* - : unit = () *)
assert(supprimee false [true;false] = [true]);; (* - : unit = () *)
assert(supprimee "pas" ["Je";"suis";"pas";"fort";"en";"ocaml"] = ["Je";"suis";"fort";"en";"ocaml"]);; (* - : unit = () *)

  
(* Intersectione
|SPÉCIFICATION
| - Profil intersectione ∶ 'a ensemble -> 'a ensemble -> 'a ensemble 
| - Sémantique : intersectione (ens1 ens2) renvois l'ensemble avec seulement les éléments compris dans les deux ensembles précisés
| - Exemple 
|   (1) intersectione [1;2] [2;1] = [1;2]
|   (2) intersectione [] [] = []
|   (3) intersectione ["Hello"] ["Hello";"World"] = ["Hello"]
|REALISATION
| - Implémentation :
*)
let intersectione (ens1 : 'a ensemble) (ens2 : 'a ensemble) : 'a ensemble =
  List.filter (fun x -> appartiente x ens2 ) ens1
;;

assert(intersectione [1;2] [2;1] = [1;2]);; (* - : unit = () *)
assert(intersectione [] [] = [] );; (* - : unit = () *)
assert(intersectione ["Hello"] ["Hello";"World"] = ["Hello"]);; (* - : unit = () *)
    

(* Union
|SPÉCIFICATION
| - Profil unione ∶ 'a ensemble -> 'a ensemble -> 'a ensemble
| - Sémantique : (union ens1 ens2) est l’ensemble ens1 ∪ ens2, c’est-à-dire l’ensemble des éléments appartenant à ens1 ou à ens2.
| - Exemple 
|   (1) unione [1;2] [2;1] = [2;1]
|   (2) unione [2;1] [3;4] = [1;2;3;4]
|   (3) unione ["Hello"] ["Hello";"World"] = ["Hello";"World"]
|REALISATION
| - Implémentation :
*)
let unione (ens1:'a ensemble) (ens2:'a ensemble):'a ensemble =
  List.filter (fun x -> not (appartiente x (intersectione ens1 ens2 ))) ens1@ens2
;;

assert(unione [] [] = []);; (* - : unit = () *) 
assert(unione [1;2] [2;1] = [2;1]);; (* - : unit = () *)
assert(unione [1;2] [3;4] = [1;2;3;4]);; (* - : unit = () *)
assert(unione ["Hello"] ["Hello";"World"] = ["Hello";"World"]);; (* - : unit = () *)


(* Différence
|SPÉCIFICATION
| - Profil dife ∶ 'a ensemble -> 'a ensemble -> 'a ensemble
| - Sémantique : (dife ens1 ens2) est l’ensemble ens1 privé de ens2, c’est-à-dire l’ensemble des éléments appartenant à ens1 mais pas ens2.
| - Exemple 
|   (1) dife [2] [2;1] = []
|   (2) dife [1;2] [3;4] = [1;2]
|   (3) dife ["Hello";"IamAI"] ["Hello";"World"] = ["IamAI"]
|REALISATION
| - Implémentation :
*)
let dife (ens1 : 'a ensemble) (ens2 : 'a ensemble) : 'a ensemble =
  List.filter (fun x -> not (appartiente x ens2) ) ens1
;;

assert(dife [] [] = []);; (* - : unit = () *)
assert(dife [2] [2;1] = []);; (* - : unit = () *)
assert(dife [1;2] [3;4] = [1;2]);; (* - : unit = () *)
assert(dife ["Hello";"IamAI"] ["Hello";"World"] = ["IamAI"]);; (* - : unit = () *)
  
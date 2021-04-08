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

type 'a multielement = 'a * int ;;
type 'a multiensemble = 'a multielement list ;;


(* Q5. Réalisation des fonctions *)

(* Cardinalité
|SPÉCIFICATION 
| - Profil cardinalm ∶ 'a multiensemble -> int
| - Sémantique : cardinalm(mens) renvois le nombre d'éléments dans le multi-ensemble mens ainsi que le nombre total d'occurence des éléments.
| - Exemple :
|   (1) cardinalm [(1,1)] = (1,1)
|   (2) caridnalm [] = (0, 0)
|   (3) cardinalm [(1,1);(2,2)] = (2,3) 
|REALISATION
| - Implémentation :
*)
let rec cardinalm (mens:'a multiensemble) : int * int =
    match mens with
    | [] -> 0, 0
    | (x, n)::fin -> let(a,b) = (cardinalm fin) in 1+a, n+b
;;

assert(cardinalm [] = (0,0));; (* - : unit = () *)
assert(cardinalm [(1,1)] = (1,1));; (* - : unit = () *)
assert(cardinalm [(1,1);(2,2)] = (2,3));; (* - : unit = () *)
assert(cardinalm [(1, 2);(5,2);(3,2);(14, 2)] = (4, 8));; (* - : unit = () *)
assert(cardinalm [("hello",20);("world", 22)] = (2, 42));; (* - : unit = () *)


(* Occurence
|Spécification
| - Profil occurrence ∶ 'a -> 'a multiensemble -> int
| - Sémantique : (occurrence x mens) est le nombre d’occurrences du support x dans mens.
| - Exemple :
|   (1) occurrence 'm' [('u', 2);('m', 5)] = 5
|   (2) occurrence 2 [(2, 2);(1, 3)] = 2
|   (3) occurrence true [(true, 1);(false, 5)] = 1
|REALISATION
| - Implémentation :
*)
let rec occurrence (x:'a) (mens:'a multiensemble): int=
  match mens with
  | [] -> 0
  | (elt,nb)::fin when elt=x -> nb
  | (elt,nb)::fin -> occurence x fin
;;

assert(occurrence 'm' [('u', 2);('m', 5)] = 5);; (* - : unit = () *)
assert(occurrence 2 [(2, 2);(1, 3)] = 2);; (* - : unit = () *)
assert(occurrence true [(true, 1);(false, 5)] = 1);; (* - : unit = () *)


(* Appartenance *)
(*
|SPÉCIFICATION
| - Profil appartientm ∶ 'a multielement -> 'a multiensemble -> bool
| - Sémantique : (appartientm melt mens) est vrai si et seulement si la multiplicité de melt est
inférieure ou égale au nombre d’occurences de son support dans mens
| - Exemple :
|   (1) appartientm ('m',4) [('u', 2);('m', 5)] = true
|   (2) appartientm (3,1) [(2, 2);(1, 3)] = false
|   (3) appartientm (true,2) [(true, 1);(false, 5)] = false
|REALISATION
| - Implémentation :
*)
let appartientm (melt: 'a multielement) (mens: 'a multiensemble) : bool =
  let (s,m) = melt in m <= (occurrence s mens)
;;

  assert(appartientm ('m',4) [('u', 2);('m', 5)]);; (* - : unit = () *)
  assert(not (appartientm (3,1) [(2, 2);(1, 3)]));; (* - : unit = () *)
  assert(not(appartientm (true,2) [(true, 1);(false, 5)]));; (* - : unit = () *)


(* Inclusion *)
(* 
|SPÉCIFICATION
| - Profil inclusm ∶ 'a multiensemble -> 'a multiensemble -> bool
| - Sémantique : (inclusm mens1 mens2) est vrai si et seulement si tout élément de mens2 appartient à mens2.
| - Exemple :
|   (1) inclusm [('u',1)] [('u',1);('m',2)] = true
|   (2) inclusm [('u',1)] [('u',5);('m',2)] = true
|   (3) inclusm [('u',5)] [('u',1);('m',2)] = false
|REALISATION
| - Implémentation :
*)
let rec inclusm (mens1:'a multiensemble) (mens2:'a multiensemble): bool =
  match mens1 with
  | melt::fin -> appartientm melt mens2 && inclusm fin mens2
  | [] -> true
;;

assert(not (inclusm [(2,1)] [(3,1);(4,2)]));; (* - : unit = () *)
assert(inclusm [('u',1)] [('u',1);('m',2)]);; (* - : unit = () *)
assert(inclusm [('u',1)] [('u',5);('m',2)]);; (* - : unit = () *)
assert(not (inclusm [('u',5)] [('u',1);('m',2)]));; (* - : unit = () *)


(* Ajout
|SPÉCIFICATION
| - Profil ajoutem ∶ 'a multielement -> 'a multiensemble -> 'a multiensemble 
| - Sémantique : ajoutem(a ens) Ajoute un élément a à un ensemble ens respectant la contrainte de non répétition des éléments
|                Dépend de inclusion
| - Exemple 
|   (1) ajoutem (3,1) [(1,2)] = [(3,1);(1,2)]
|   (2) ajoutem ("hello",1) [("world", 1)] = [("hello", 1);("world",1)]
|   (3) ajoutem (3,1) [] = [(3,1)]
|   (4) ajoutem ("Immortal", 1) [("Immortal", 1)] = [("Immortal", 2)]
|REALISATION
| - Implémentation :
*)
let rec ajoutem (melt: 'a multielement) (mens: 'a multiensemble) : 'a multiensemble =
  let (s,o)= melt in 
    match mens with
    | [] when o > 0 -> melt::mens
    | (elt,nb)::fin when elt = s -> (elt,o+nb)::fin
    | (elt, nb)::fin -> ajoutem melt fin
    | [] -> []
;;

assert(ajoutem (3,1) [(1,2)] = [(3,1);(1,2)]);; (* - : unit = () *)
assert(ajoutem (3,1) [] = [(3,1)]);; (* - : unit = () *)
assert(ajoutem ("Immortal", 1) [("Immortal", 1)] = [("Immortal", 2)]);; (* - : unit = () *)


(* Suppression
|SPÉCIFICATION
| - Profil supprimem ∶ 'a -> 'a ensemble -> 'a ensemble 
| - Sémantique :  (supprimem (x, n) mens) supprime n occurrences du support x du multi-ensemble
| mens. Si n est supérieur ou égal au nombre d’occurrences de x dans mens, alors x
| disparaît complètement de mens. Selon le besoin, il pourra être pratique d’implémenter en plus la fonctionalité suivante : si 𝑛 = 0, toutes les occurrences de x sont
| supprimées ().
| - Exemple 
|   (1) supprimem 3 [1;3] = [1]
|   (2) supprimem "hello" ["world";"hello"] = ["world"]
|   (3) supprimem false [true;false] = [true]
|REALISATION
| - Implémentation :
*)
let rec supprimem (melt:'a multielement) (mens:'a multiensemble) : 'a multiensemble =
  if not(appartient melt mens) then mens else
    match mens with
    | [] -> []
    | (x,n)
;;

assert(supprime 3 [1;3] = [1]);; (* - : unit = () *)
assert(supprime "hello" ["world";"hello"] = ["world"]);; (* - : unit = () *)
assert(supprime false [true;false] = [true]);; (* - : unit = () *)
assert(supprime "pas" ["Je";"suis";"pas";"fort";"en";"ocaml"] = ["Je";"suis";"fort";"en";"ocaml"]);; (* - : unit = () *)

  
(* Egalité
|SPÉCIFICATION
| - Profil egauxm ∶ 'a multiensemble -> 'a multiensemble -> bool
| - Sémantique : (egaux mens1 mens2) est vrai si et seulement si mens1 et mens2 ont les mêmes multi-éléments.
| - Exemple 
|   (1) egauxm [(1,1);(2,3)] [(2,3);(1,1)] = true
|   (2) egauxm [] [] = true
|   (3) egauxm [("Hello",1)] [("Hello",1),("World",2)] = false
|   (3) egauxm [('c',2),('a',1)] [('c',2),('a',2)] = false
|REALISATION
| - Implémentation :
*)
let rec egaux (mens1:'a multiensemble) (mens2:'a multiensemble):bool =
  if (cardinalm mens1) <> (cardinalm mens2) then false
  else
    match mens1 with
    | melt::fin -> (appartient melt mens2) && (egaux fin (supprime x ens2))
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


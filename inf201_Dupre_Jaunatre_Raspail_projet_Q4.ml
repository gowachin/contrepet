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
    | (elt,nb)::fin when elt = s -> [(elt,o+nb)]@fin
    | melt2::fin -> (ajoutem melt fin)@[melt2]
    | [] -> []
;;

assert(ajoutem (3,1) [(1,2)] = [(3,1);(1,2)]);; (* - : unit = () *)
assert(ajoutem (3,1) [] = [(3,1)]);; (* - : unit = () *)
assert(ajoutem ("Immortal", 1) [("Immortal", 1)] = [("Immortal", 2)]);; (* - : unit = () *)

(* Suppression
|SPÉCIFICATION
| - Profil supprimem ∶ 'a multielement -> 'a multiensemble -> 'a multiensemble 
| - Sémantique :  (supprimem (x, n) mens) supprime n occurrences du support x du multi-ensemble
| mens. Si n est supérieur ou égal au nombre d’occurrences de x dans mens, alors x
| disparaît complètement de mens. Selon le besoin, il pourra être pratique d’implémenter en plus la fonctionalité suivante : si 𝑛 = 0, toutes les occurrences de x sont
| supprimées ().
| - Exemple 
|   (1) supprimem ('m' ,2) [('m',3);('n',1);('a',23)] = [('m',1);('n',1);('a',23)]
|   (2) supprimem (3,3) [(3,1);(1,2)] = [(1,2)]
|   (3) supprimem (false,0) [(true,1);(false,1)] = [(true,1)]
|REALISATION
| - Implémentation :
*)
let rec supprimem (melt:'a multielement) (mens:'a multiensemble) : 'a multiensemble =
    let x,n = melt in 
    match mens with
    | [] -> []
    | (x1,n1)::fin when x=x1 -> if (n>=n1)||(n=0) then supprimem melt fin else [(x1,n1-n)]@fin
    | melt2::fin -> [melt2]@(supprimem melt fin)
;;
  
assert(supprimem (3,1) [(1,2);(3,1)] = [(1,2)]);; (* - : unit = () *)
assert(supprimem ('m' ,2) [('m',3);('n',1);('a',23)] = [('m',1);('n',1);('a',23)]);; (* - : unit = () *)
assert(supprimem (false,0) [(true,1);(false,1)] = [(true,1)]);; (* - : unit = () *)
assert(supprimem ("pas",1) [("Je",1);("suis",1);("pas",1);("fort",1);("en",1);("ocaml",1)] = [("Je",1);("suis",1);("fort",1);("en",1);("ocaml",1)]);; (* - : unit = () *)

  
(* Egalité
|SPÉCIFICATION
| - Profil egauxm ∶ 'a multiensemble -> 'a multiensemble -> bool
| - Sémantique : (egaux mens1 mens2) est vrai si et seulement si mens1 et mens2 ont les mêmes multi-éléments.
| - Exemple 
|   (1) egauxm [(1,1);(2,3)] [(2,3);(1,1)] = true
|   (2) egauxm [] [] = true
|   (3) egauxm [("Hello",1)] [("Hello",1);("World",2)] = false
|   (3) egauxm [('c',2);('a',1)] [('c',2);('a',2)] = false
|REALISATION
| - Implémentation :
*)
let rec egauxm (mens1:'a multiensemble) (mens2:'a multiensemble):bool =
  if (cardinalm mens1) <> (cardinalm mens2) then false
  else
    match mens1 with
    | (elt,nb)::fin -> if (occurrence elt mens2)=nb then (egauxm fin (supprimem (elt,nb) mens2)) else false
    | [] -> true
;; 
  
assert(egauxm [] []);; (* - : unit = () *)
assert(egauxm [(1,1);(2,3)] [(2,3);(1,1)]);;(* - : unit = () *)
assert(not (egauxm [("Hello",1)] [("Hello",1);("World",2)]));;(* - : unit = () *)
assert(not (egauxm [('c',2);('a',1)] [('c',2);('a',2)]));;(* - : unit = () *)


(* Intersection
|SPÉCIFICATION
| - Profil intersectionm ∶ 'a multiensemble -> 'a multiensemble -> 'a mutiensemble 
| - Sémantique : (intersectionm mens1 mens2) est le multi-ensemble des éléments appartenant à la fois à mens1 et à mens2.
| - Exemple 
|   (1) intersectionm [('m', 3) ; ('u', 1)] [('m', 1) ; ('a', 1)] = [('m', 1)]
|   (2) intersectionm [] [] = []
|   (3) intersectionm [("Bonjour",2)] [("Hello",3);("World",1)] = []
|REALISATION
| - Implémentation :
*)
let rec intersectionm (mens1 : 'a multiensemble) (mens2 : 'a multiensemble) : 'a multiensemble =
    if egauxm mens1 mens2 then mens1
    else
        match mens1 with
        | [] -> []
        | (elt,nb)::fin -> if (occurrence elt mens2)=0
          then intersectionm fin mens2
          else [(elt,min nb (occurrence elt mens2))]@(intersectionm fin mens2)
;;

assert(intersectionm [('m', 3) ; ('u', 1)] [('m', 1) ; ('a', 1)] = [('m', 1)]);; (* - : unit = () *)
assert(intersectionm [] [] = [] );; (* - : unit = () *)
assert(intersectionm [("Bonjour",2)] [("Hello",3);("World",1)] = []);; (* - : unit = () *)

(* Union
|SPÉCIFICATION
| - Profil unionm ∶ 'a multiensemble -> 'a multiensemble -> 'a multiensemble
| - Sémantique : (unionm mens1 ens2) est l’ensemble mens1 ∪ mens2, c’est-à-dire l’ensemble des éléments appartenant à mens1 ou à mens2.
| - Exemple 
|   (1) unionm [(1,1);(2,2)] [(2,2);(1,1)] = [(2,2);(1,1)]
|   (2) unionm [(2,1);(1,1)] [(3,3);(4,4)] = [(1,1);(2,2);(3,3);(4,4)]
|   (3) unionm [("Hello", 1)] [("Hello",1);("World",1)] = [("Hello",1);("World",1)]
|   (4) unionm [("Hello", 2)] [("Hello",1);("World",1)] = [("Hello",2);("World",1)]
|REALISATION
| - Implémentation :
*)
let rec unionm (mens1:'a multiensemble) (mens2:'a multiensemble):'a multiensemble =
  if egauxm mens1 mens2 then mens1
  else
    match mens1 with
    | [] -> mens2
    | (elt,nb)::fin -> if (occurrence elt mens2)=0
      then [(elt,nb)]@(unionm fin mens2)
      else unionm [(elt,max nb (occurrence elt mens2))] (unionm fin (supprimem (elt,(occurrence elt mens2)) mens2)  ) 
;;

assert(unionm [(1,1);(2,2)] [(2,2);(1,1)] = [(1,1); (2,2)]);; (* - : unit = () *)
assert(unionm [(2,2);(1,1)] [(3,3);(4,4)] = [(2,2);(1,1);(3,3);(4,4)]);; (* - : unit = () *)
assert(unionm [("Hello", 1)] [("Hello",1);("World",1)] = [("Hello",1);("World",1)]);; (* - : unit = () *)
assert(unionm [("Hello", 2)] [("Hello",1);("World",1)] = [("Hello",2);("World",1)]);; (* - : unit = () *)
assert(unionm [("Hello",3);("John",1)] [("Hello",2);("World",1)] = [("Hello", 3); ("John", 1); ("World", 1)]);; (* - : unit = () *)

  
(* Différence
|SPÉCIFICATION
| - Profil difm ∶ 'a multiensemble -> 'a multiensemble -> 'a ensemble
| - Sémantique : (difm mens1 mens2) est le multi-ensemble obtenu en supprimant les multiéléments appartenant à mens2 de mens1
| - Exemple 
|   (1) difm [(2,3);(3,1);(4,1)] [(2,2);(3,1);(6,1)] = [(2,3);(4,1)]
|   (2) difm [(2,1);(3,1);(4,1)] [(2,2);(3,1);(6,1)] = [(4,1)]
|   (3) difm [("Hello",1);("IamAI",2)] [("Hello",3);("World",1)] = [("IamAI",2)]
|REALISATION
| - Implémentation :
*)
let rec difm (mens1 : 'a multiensemble) (mens2 : 'a multiensemble) : 'a multiensemble =
  if egauxm mens1 mens2 then [] else
  match mens1 with
  | [] -> []
  | melt1::melt2 when (appartientm melt1 mens2) -> difm melt2 mens2
  | melt1::melt2 -> [melt1]@difm melt2 mens2
;;

assert(difm [(2,3);(3,1);(4,1)] [(2,2);(3,1);(6,1)] = [(2,3);(4,1)]);; (* - : unit = () *)
assert(difm [(2,1);(3,1);(4,1)] [(2,2);(3,1);(6,1)] = [(4,1)]);; (* - : unit = () *)
assert(difm [("Hello",1);("IamAI",2)] [("Hello",3);("World",1)] = [("IamAI",2)]);; (* - : unit = () *)
  

(* Différence symétrique
|SPÉCIFICATION
| - Profil difsymm ∶ 'a multiensemble -> 'a multiensemble -> 'a multiensemble
| - Sémantique : (difsymm mens1 mens2) est le multi-ensemble des multi-éléments qui appartiennent soit à mens1, soit à mens2, mais pas au deux à la fois.
| - Exemple 
|   (1) difsymm [(2,1)] [(2,2);(1,3)] = [(2, 2); (1, 3)]
|   (2) difsymm [(2,1);(1,1)] [(3,2);(4,5)] = [(2, 1); (1, 1); (3, 2); (4, 5)]
|   (3) difsymm [("Hello",3);("John",1)] [("Hello",2);("World",1)] = [("Hello", 3); ("John", 1); ("World", 1)]
|REALISATION
| - Implémentation :
*)
let difsymm (mens1 : 'a multiensemble) (mens2 : 'a multiensemble) : 'a multiensemble =
  difm (unionm mens1 mens2) (intersectionm mens1 mens2)
;;

assert(difsymm [(2,1)] [(2,2);(1,3)] = [(2, 2); (1, 3)] );; (* - : unit = () *)
assert(difsymm [(2,1);(1,1)] [(3,2);(4,5)] = [(2, 1); (1, 1); (3, 2); (4, 5)]);; (* - : unit = () *)
assert(difsymm [("Hello",3);("John",1)] [("Hello",2);("World",1)] = [("Hello", 3); ("John", 1); ("World", 1)]);; (* - : unit = () *)

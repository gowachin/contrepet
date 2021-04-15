(* ---------------------------------------------------------------------------
 inf201_Dupre_Jaunatre_Raspail_projet_Q4-Q5.ml : Projet d'INF201

 Alexandre Dupré <alexandre.dupre@etu.univ-grenoble-alpes.fr> \
 Maxime Jaunatre <maxime.jaunatre@etu.univ-grenoble-alpes.fr>  > Groupe D
 Clément Raspail <clement.raspail@etu.univ-grenoble-alpes.fr> /

 -----------------------------------------------------------------------------
*)

(* ---------- Partie 5 : Contrepet  ----------*)

(* Q6. Définir en OCaml les types mot et phrase *)

type mot = char list;; (* 'a', … , 'z' *)
type phrase = mot list ;;

(*  Ne marche pas car sur turing version 4.05
(* Conversion de chaînes de mots
|SPÉCIFICATION
| - Profil chaineVmot, cVm ∶ string -> mot
| - Sémantique : chaineVmot (s) est le mot correspondant à la chaîne s.
|                cVm est un synonyme de chaineVmot.
| - Exemple :
|   (1) (cVm ”algorithme”) = [’a’ ;’l’ ;’g’ ;’o’ ;’r’ ;’i’ ;’t’ ;’h’ ;’m’ ;’e’]
|REALISATION
| - Implémentation :
*)
let chaineVmot (ch:string) : char list =
  List.of_seq (String.to_seq ch) 
;;

let cVm : string -> char list =
  chaineVmot 
;;
*)

(* Q7 *)
(*let quelle = chaineVmot "quelle";;
let ministre = chaineVmot "ministre";;
let seche = chaineVmot "seche";;*)
let quelle = ['q';'u';'e';'l';'l';'e'];;
let ministre = ['m';'i';'n';'i';'s';'t';'r';'e'];;
let seche = ['s';'e';'c';'h';'e'];;

(*
let sinistre = chaineVmot "sinistre";;
let meche = chaineVmot "meche";; *)
let sinistre = ['s';'i';'n';'i';'s';'t';'r';'e'];;
let meche = ['m';'e';'c';'h';'e'];;

let cstQMS = [quelle; ministre; seche];;
let cstQSM = [quelle; sinistre; meche];;

(* Ne marche pas car sur turing version 4.05
(* Conversion de chaînes de mots
|SPÉCIFICATION
| - Profil phraseVseqstring, pVs ∶ phrase -> séq (string)
| - Sémantique : phraseVseqstring(ph) est la séquence de chaînes correspondant à ph.
| - Exemple :
|   (1) (phraseVseqstring cstQMS) = [”quelle” ; ”ministre” ; ”seche”]
|REALISATION
| - Implémentation :
*)
let phraseVseqstring : phrase -> string list =
  List.map (fun m -> String.of_seq (List.to-seq m))
;;

let pVs : phrase -> string list =
  phraseVseqstring
;;*)


(* Q8 *)
type dictionnaire = mot ensemble;;

(* Q9 *)
let cst_DICO = [quelle; sinistre; ministre; seche; meche] ;;

(* Q10 *)
cst_DICO@[['m';'o';'u';'c';'h';'e'];['d';'o';'u';'c';'h';'e'];['t';'o';'u';'c';'h';'e'];
    ['l';'o';'u';'c';'h';'e'];['s';'o';'u';'c';'h';'e'];['b';'o';'u';'c';'h';'e'];
    ['l';'a'];['s';'e'];['p';'o';'u';'l';'e'];['m';'o';'u';'l';'e'];['e';'l';'l';'e'];
    ['e';'s';'t'];['f';'o';'l';'l';'e'];['d';'e'];['m';'e';'s';'s';'e'];['m';'o';'l';'l';'e'];
    ['f';'e';'s';'s';'e']]
;;

(* https://fr.wikibooks.org/wiki/Livre_d%27humour/Contrep%C3%A8teries *)


(* Q11 *)

(* 
|SPÉCIFICATION
| - Profil supprimePrefixeCommun ∶ mot -> mot -> mot * mot
| - Sémantique : Étant donnés deux mots m1 et m2 , posons (m′1 , m′2 ) = (supprimePrefixeCommun
|                m1 m2 ). m′1 (resp. m′2 ) est le mot obtenu en supprimant de m1 (resp. m2 ) 
|                le préfixe commun à m 1 et m 2 .
| - Exemple :
|   (1) (phraseVseqstring cstQMS) = [”quelle” ; ”ministre” ; ”seche”]
|REALISATION
| - Implémentation :
*)
let rec supprimePrefixeCommun (m1:mot) (m2:mot) : mot * mot = 
    match m1,m2 with
    | elt1::fin1 , elt2::fin2 when elt1=elt2 -> supprimePrefixeCommun fin1 fin2
    | elt1::fin1 , elt2::fin2 -> [elt1]@fin1,[elt2]@fin2
    | _,_ -> [],[]
;;


(*
crache ['c';'r';'a';'c';'h';'e']
croche ['c';'r';'o';'c';'h';'e']
supprimePrefixeCommun ['c';'r';'o';'c';'h';'e'] ['c';'r';'a';'c';'h';'e'];;
*)




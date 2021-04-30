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
let rec chaineVmot (ch:string) : char list =
  match ch with
  | "" -> []
  | _ -> (String.get ch 0) :: (chaineVmot (String.sub ch 1 ((String.length ch)-1)))
;;

let cVm : string -> char list =
  chaineVmot 
;;


(* Q7 *)
let quelle = chaineVmot "quelle";;
let ministre = chaineVmot "ministre";;
let seche = chaineVmot "seche";;
let sinistre = chaineVmot "sinistre";;
let meche = chaineVmot "meche";; 

let cstQMS = [quelle; ministre; seche];;
let cstQSM = [quelle; sinistre; meche];;


(* Conversion de chaînes de mots
|SPÉCIFICATION
| - Profil phraseVseqstring, pVs ∶ phrase -> séq (string)
| - Sémantique : phraseVseqstring(ph) est la séquence de chaînes correspondant à ph.
| - Exemple :
|   (1) (phraseVseqstring cstQMS) = [”quelle” ; ”ministre” ; ”seche”]
|REALISATION
| - Implémentation :
*)
let rec motVchaine (m:char list) : string =
  match m with
  | [] -> ""
  | c::fin -> (String.make 1 c) ^ (motVchaine fin)
;;

let phraseVseqstring : phrase -> string list =
  List.map motVchaine
;;

let pVs : phrase -> string list =
  phraseVseqstring
;;


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
|   (1) supprimePrefixeCommun ['m';'o';'u';'c';'h';'e'] ['b';'o';'u';'c';'h';'e'] = (['m';'o';'u';'c';'h';'e'],['b';'o';'u';'c';'h';'e'])
|   (2) supprimePrefixeCommun ['d';'u'] ['d';'e'] = (['u'],['e'])
|   (3) supprimePrefixeCommun ['c';'r';'o';'c';'h';'e'] ['c';'r';'a';'c';'h';'e'] = (['o'; 'c'; 'h'; 'e'],['a'; 'c'; 'h'; 'e'])
|REALISATION
| - Implémentation :
*)
let rec supprimePrefixeCommun (m1:mot) (m2:mot) : mot * mot = 
    match m1,m2 with
    | elt1::fin1 , elt2::fin2 when elt1=elt2 -> supprimePrefixeCommun fin1 fin2
    | elt1::fin1 , elt2::fin2 -> [elt1]@fin1,[elt2]@fin2
    | _,_ -> [],[]
;;
assert(supprimePrefixeCommun ['d';'e'] ['d';'e'] = ([],[]));;
assert(supprimePrefixeCommun ['d';'u'] ['d';'e'] = (['u'],['e']));;
assert(supprimePrefixeCommun ['c';'r';'o';'c';'h';'e'] ['c';'r';'a';'c';'h';'e'] = (['o'; 'c'; 'h'; 'e'],['a'; 'c'; 'h'; 'e']));;
assert(supprimePrefixeCommun ['m';'o';'u';'c';'h';'e'] ['b';'o';'u';'c';'h';'e'] = (['m';'o';'u';'c';'h';'e'],['b';'o';'u';'c';'h';'e']));;

(* 
|SPÉCIFICATION
| - Profil suffixeEgaux ∶ mot -> mot -> bool
| - Sémantique : (suffixeEgaux m1 m2 ) est vrai si et seulement si m1 et m2 ne diffèrent que par leur
|                première lettre.
| - Exemple :
|   (1) suffixeEgaux ['m';'e'] ['d';'e'] = true
|REALISATION
| - Implémentation :
*)
let suffixeEgaux (m1:mot) (m2:mot) : bool =
  match m1,m2 with
  | x::mot1,y::mot2 when mot1=mot2 -> true
  | _ -> false
;;

assert(suffixeEgaux ['m';'e'] ['d';'e']);;
assert(suffixeEgaux ['m';'o';'u';'c';'h';'e'] ['b';'o';'u';'c';'h';'e']);;
assert(not (suffixeEgaux ['c';'r';'o';'c';'h';'e'] ['c';'r';'a';'c';'h';'e']));;


(* Q12 *)
(* 
|SPÉCIFICATION
| - Profil motsSontContrepet ∶ mot*mot -> mot*mot -> bool
| - Sémantique : (motSontContrepet ) est vrai si et seulement si m1 et m2 ne diffèrent que par leur
|                première lettre.
| - Exemple :
|   (1) motsSontContrepet ( ['m';'i';'n'], ['s';'e';'c';'h';'e'] ) (['s';'i';'n'], ['m';'e';'c';'h';'e'] )
|REALISATION
| - Implémentation :
*)
let motsSontContrepet ((mot1_1,mot1_2): mot * mot) ((mot2_1,mot2_2): mot * mot): bool =
  if (mot1_1=mot2_2) && (mot1_2 = mot2_1)
  then true (* On utilise l'opérateur = car l'ordre des éléments est important ici par rapport a la fonction egaux de Q2 *)
  else
    if (mot1_1=mot2_2) || (mot1_2 = mot2_1)
    then false
     else
      let (pref1_1,pref2_2)=(supprimePrefixeCommun mot1_1 mot2_2) in
      let (pref1_2,pref2_1)=(supprimePrefixeCommun mot1_2 mot2_1) in
      let (deb1_1::suff1_1,deb2_1::suff2_1)=(pref1_1,pref2_1) in
      let (deb1_2::suff1_2,deb2_2::suff2_2)=(pref1_2,pref2_2) in
      (deb1_1=deb2_1) && (deb1_2=deb2_2) && (suffixeEgaux suff1_1 suff2_1) && (suffixeEgaux suff1_2 suff2_2)
;;

assert(motsSontContrepet ( ['m';'i';'n'], ['s';'i';'n'] ) (['s';'i';'n'], ['m';'i';'n']));; (* Contrepetrie avec les meme mots *)
assert(not (motsSontContrepet ( ['m';'i';'n'], ['m';'i';'n'] ) (['s';'i';'n'], ['s';'i';'n']) ));; (* Meme mot en comparaison *)
assert(not (motsSontContrepet ( ['m';'i';'n'], ['s';'i';'n'] ) (['s';'o';'n'], ['m';'i';'n']) ));; (* 1 seul meme mot pour la contrepetrie *)
assert(motsSontContrepet ( ['m';'i';'n'], ['s';'e';'c';'h';'e'] ) (['s';'i';'n'], ['m';'e';'c';'h';'e'] ) );; (* Contrepetrie normal *)
assert(not (motsSontContrepet ( ['m';'i';'n'], ['s';'e';'c';'h';'e'] ) (['s';'o';'n'], ['m';'e';'c';'h';'e'] )) );; (* Pas de contrepetrie *)


(* 
(* Q13 
|SPÉCIFICATION
| - Profil motsSontContrepet ∶ phrase -> phrase -> bool
| - Sémantique : (phrasesSontContrepet phr1 phr2 ) est vrai si et seulement si phr1 et phr2 sont contre-
|                pèterie l’une de l’autre.
| - Exemple :
|   (1) 
|REALISATION
| - Implémentation :
*)
let rec phrasesSontContrepet (p1:phrase) (p2:phrase): bool =
  match p1,p2 with
  | [],_ | _,[] -> false
  | deb1::mid1::fin1,deb2,mid2,fin2 -> (motsSontContrepet (deb1,mid1) (deb2,mid2)) && phrasesSontContrepet fin1 fin2
;;
*)(*
phrasesSontContrepet [ ['q'; 'u'; 'e'; 'l'; 'l'; 'e'] ; ['m';'i';'n']; ['s';'e';'c';'h';'e'] ] [['q'; 'u'; 'e'; 'l'; 'l'; 'e'] ; ['s';'i';'n']; ['m';'e';'c';'h';'e']]
*)
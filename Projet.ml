(* ---------------------------------------------------------------------------
 inf201_Dupre_Jaunatre_Raspail_projet.ml : Projet d'INF201

 Alexandre Dupré <alexandre.dupre@etu.univ-grenoble-alpes.fr> \
 Maxime Jaunatre <maxime.jaunatre@etu.univ-grenoble-alpes.fr>  > Groupe D
 Clément Raspail <clement.raspail@etu.univ-grenoble-alpes.fr> /

 -----------------------------------------------------------------------------
*)

(* 4.1 TP6 flux de circulation sur une voie routière*)

(* Q1 *)
type seq_int = Nil | N of int*seq_int;;
type releve = seq_int;;


(* 4.1 TP6 flux de circulation sur une voie routière*)

(* Q2 *)
(*
|SPÉCIFICATION
| - Profil nbj_sans ∶ releve -> int
| - Sémantique : nbj_sans(releve) donne le nombre de jours sans vehicules
| - Exemple :
|   (1) nbj_sans (N(0,Nil)) = 1
|   (2) nbj_sans Nil = 0
|   (3) nbj_sans (N(5,N(0,N(0,N(1,Nil))))) = 2
*)

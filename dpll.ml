(* MP1 2023/2024 - dpll.ml *)

open List

(* fonctions utilitaires *)
(* ----------------------------------------------------------- *)
(* filter_map : ('a -> 'b option) -> 'a list -> 'b list
   disponible depuis la version 4.08.0 de OCaml dans le module List :
   pour chaque élément de `list', appliquer `filter' :
   - si le résultat est `Some e', ajouter `e' au résultat ;
   - si le résultat est `None', ne rien ajouter au résultat.
   Attention, cette implémentation inverse l'ordre de la liste *)
let filter_map filter list =
  let rec aux list ret =
    match list with
    | [] -> ret   (* Si on arrive à la fin de la liste, on renvoie l'accumulateur "ret" *)
    | h::t ->
      match (filter h) with   (* Sinon, on match la fonction filter avec l'élément de la liste *)
      | None -> aux t ret     (* Si filter renvoie None, on continue avec la suite *)
      | Some e -> aux t (e::ret)  (* S'il y a un resultat, on continue en stockant le resultat dans l'accumulateur *)
  in aux list []  (* Fait appel à "aux" avec list et une liste accumulateur vide *)

(* print_modele : int list option -> unit
   affichage du résultat *)
let print_modele: int list option -> unit = function
  | None   -> print_string "UNSAT\n"
  | Some modele -> print_string "SAT\n";
     let modele2 = sort (fun i j -> (abs i) - (abs j)) modele in
     List.iter (fun i -> print_int i; print_string " ") modele2;
     print_string "0\n"

(* ensembles de clauses de test *)
let exemple_3_12 = [[1;2;-3];[2;3];[-1;-2;3];[-1;-3];[1;-2]]
let exemple_7_2 = [[1;-1;-3];[-2;3];[-2]]
let exemple_7_4 = [[1;2;3];[-1;2;3];[3];[1;-2;-3];[-1;-2;-3];[-3]]
let exemple_7_8 = [[1;-2;3];[1;-3];[2;3];[1;-2]]
let systeme = [[-1;2];[1;-2];[1;-3];[1;2;3];[-1;-2]]
let coloriage = [
  [1;2;3];[4;5;6];[7;8;9];[10;11;12];[13;14;15];[16;17;18];
  [19;20;21];[-1;-2];[-1;-3];[-2;-3];[-4;-5];[-4;-6];[-5;-6];
  [-7;-8];[-7;-9];[-8;-9];[-10;-11];[-10;-12];[-11;-12];[-13;-14];
  [-13;-15];[-14;-15];[-16;-17];[-16;-18];[-17;-18];[-19;-20];
  [-19;-21];[-20;-21];[-1;-4];[-2;-5];[-3;-6];[-1;-7];[-2;-8];
  [-3;-9];[-4;-7];[-5;-8];[-6;-9];[-4;-10];[-5;-11];[-6;-12];
  [-7;-10];[-8;-11];[-9;-12];[-7;-13];[-8;-14];[-9;-15];[-7;-16];
  [-8;-17];[-9;-18];[-10;-13];[-11;-14];[-12;-15];[-13;-16];
  [-14;-17];[-15;-18]]

(* ----------------------------------------------------------- *)

(* simplifie : int -> int list list -> int list list 
   applique la simplification de l'ensemble des clauses en mettant
   le littéral l à vrai.
   *)
let simplifie (l : int) (clauses : int list list) : int list list =
  let filter_clause (c:int list) =     (* On va simplifier chaque clause de notre formule *)
    if List.mem (l:int) (c:int list) then None  (* Si le littéral l apparaît dans clause, il faut supprimer la clause de la formule, on renvoie None -> la clause ne sera donc pas stockée dans la liste retournée par filter_map *)
    else 
      Some(
        let verif x =  (* On gère le cas où il faut seulement supprimer not(l) de la clause, ici "x" va représenter chaque littéral de la clause "c" *)
        if x <> (-l)    (* On vérifie la valeur de "x" *)
          then Some(x)  (* Si x différent de not(l), aucun soucis, on garde x dans notre clause *)
          else None     (* Si x = not(l), il faut le retirer de notre clause, on renvoie donc None pour que filter_map ne stock pas "x" dans sa liste retournée *)
        in (filter_map verif c)   (* Appel à filter_map *)
        ) 
  in filter_map filter_clause (clauses)    (* On fait appel à filter_map avec notre fonction auxiliaire filter_clause ainsi que notre formule *)

(* solveur_split : int list list -> int list -> int list option
   exemple d'utilisation de `simplifie' *)
(* cette fonction ne doit pas être modifiée, sauf si vous changez 
   le type de la fonction simplifie *)
let rec solveur_split clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
  (* la clause vide n'est jamais satisfiable *)
  if mem [] clauses then None else
  (* branchement *) 
  let l = hd (hd clauses) in
  let branche = solveur_split (simplifie l clauses) (l::interpretation) in
  match branche with
  | None -> solveur_split (simplifie (-l) clauses) ((-l)::interpretation)
  | _    -> branche

(* tests *)
(* let () = print_modele (solveur_split systeme []) *)
(* let () = print_modele (solveur_split coloriage []) *)

(* solveur dpll récursif *)
(* ----------------------------------------------------------- *)

(* pur : int list list -> int option
    - si `clauses' contient au moins un littéral pur, retourne "Some" de ce littéral ;
    - sinon, None *)
let pur (clauses : int list list) : int option =
  let rec trouve allLiteral doublons =   (* On va chercher si un littéral apparait purement dans la formule (allLiteral) en faisant attention aux doublons *)
    match allLiteral with 
    | [] -> None          (* On est arrivé à la fin -> pas d'éléments pur *)
    | x::x1 ->      (* On va vérifier si x est pur *)
    if List.mem(abs(x)) doublons then trouve x1 doublons  (* Si x ou -x appartient à doublons, pas besoin de chercher, on passe à la suite (sans rajouter x à doublons vu qu'il y est déjà) *)
    else
      if List.mem(-x) x1 then trouve x1 (abs(x)::doublons)   (* Si x ou -x n'appartient pas à doublons, mais que -x apparait par la suite, x n'est donc pas pur, on continue en ajoutant x à doublons *)
      else Some x   (* Sinon, x est pur, on le renvoie *)
  in trouve (List.flatten(clauses)) []        (* On fait appel à la fonction auxiliaire *)

(*
Pourquoi verifier si abs(x) apparait dans doublons et pas autrement ?

Notre liste "doublons" va contenir les litteraux non-pur qu'on aura verifiés auparavant.
Sauf que si x n'est pas pur, alors not(x) n'est pas pur également. Donc au lieu de ralonger la taille de la liste "doublons",
en ajoutant x et not(x) à chaque fois, autant rajouter seulement l'un des deux (le premier qui a été vérifier),
et faire appel à abs(x) pour converger les deux cas en un seul cas.

On aurait donc très bien pu, à chaque fois rajouter x et not(x) dans la liste "doublons" et vérifier si List.mem(x) (sans abs()).
Mais la taille de "doublons" aura doublée, donc + de recherche.
*)
                
(* unitaire : int list list -> int option
    - si `clauses' contient au moins une clause unitaire, retourne
      "Some" du littéral de cette clause unitaire ;
    - sinon, None *)
let unitaire (clauses : int list list) : int option =
    try Some (List.hd (List.find (fun c -> List.length c = 1) clauses)) with  (* On cherche la première clause de longueur 1 pour renvoyer le littéral à l'intérieur *)
    | _ -> None   (* S'il y en a pas, on renvoie None *)


(* solveur_dpll_rec : int list list -> int list -> int list option *)
let rec solveur_dpll_rec (clauses : int list list) (interpretation : int list) : int list option =
  if clauses = [] then Some interpretation else     (* La formule est un ensemble vide -> satisfaisable *)
  if List.mem [] clauses then None else      (* Il existe au moins une clause vide -> non-satisfaisable *)
    match unitaire clauses with     (* On verifie s'il y a une clause unitaire *)
    | Some u -> solveur_dpll_rec (simplifie u clauses) (u :: interpretation)  (* Si oui, on continue le DPLL avec une formule simplifiée par le littéral dans la clause unitaire *)
    | None ->   (* Sinon, on continue avec les autres cas *)
      match pur clauses with      (* On verifie s'il y a un littéral pur *)
      | Some p -> solveur_dpll_rec (simplifie p clauses) (p :: interpretation)  (* Si oui, on continue le DPLL avec une formule simplifiée par le littéral pur *)
      | None ->   (* Sinon, on continue avec un branchage *)
        let l = List.hd (List.hd clauses) in  (* Choix du littéral sur lequel on branche *)
        let branche = solveur_dpll_rec (simplifie l clauses) (l :: interpretation) in   (* On branche sur ce littéral *)
        match branche with
        | None -> solveur_dpll_rec (simplifie (-l) clauses) ((-l) :: interpretation)  (* Si la première branche n'a rien donnée, on branche avec not(litteral) *)
        | _ -> branche    (* Sinon, on renvoie la première branche *)

(* 
Question : Pourquoi ne pas vérifier "pur" avant "unitaire" ? 

On sait bien que la fonction unitaire est plus efficace/rapide que la fonction pur.
Et lors du DPLL, on peut très bien arriver à un cas où le premier littéral pur est dans une clause unitaire.
Donc autant faire disparaitre ce litteral avec la fonction unitaire qui sera bien plus rapide que la fonction pur.

(PS : intervertir l'ordre d'appel entre "pur" et "unitaire" ne change rien au résultat final)
*)


(* tests *)
(* ----------------------------------------------------------- *)
(* let () = print_modele (solveur_dpll_rec systeme []) *)
(* let () = print_modele (solveur_dpll_rec coloriage []) *)


let () =
  let clauses = Dimacs.parse Sys.argv.(1) in
  print_modele (solveur_split clauses [])

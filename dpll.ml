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
    | []   -> ret
    | h::t -> match (filter h) with
      | None   -> aux t ret
      | Some e -> aux t (e::ret)
  in aux list []

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

(*Cette fonction supprime tous les elt de la liste list*)
let remove list elt = 
  let rec aux l e acc =
    match l with 
    |[] -> acc
    |x::xl -> if x = elt then aux xl e acc else aux xl e acc@[x]
  in aux list elt []

(* simplifie : int -> int list list -> int list list 
   applique la simplification de l'ensemble des clauses en mettant
   le littéral l à vrai.

   Explication :
   Si le littéral l est vrai et qu'elle se trouve dans une clause de l'ensemble alors on supprime la clause
   car celle-ci sera égale à a, si ca -l se trouve dans une clause de l'ensemble alors on supprime le littéral de la clause 
   sinon on ne fait rien. On répéte cette action pour l'ensemble des clause *)
let simplifie (l:int) (clauses:int list list) : int list list =
  let rec aux l clauses (acc:int list list) = 
    match clauses with 
    |[] -> acc
    |x::xl -> let negate = -1*l in 
              if List.mem l x
                then aux l xl acc 
                else if List.mem negate x  
                    then aux l xl (acc@[remove x l]) 
                    else aux l xl acc@[x]
    in aux l clauses []

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

(*
(*Cette fonction recupere chaque littéral dans une clause, la liste renvoyé ne contient aucun doublon*)
let recupererLitterauxInClause l = 
  let rec aux (liste:int list) (acc:int list) =
    match liste with 
    |[] -> acc
    |x::xl -> if List.mem x acc then aux xl acc else aux xl acc@[x]
  in aux l []

(*Cette fonction recupere tous les littéraux de l'ensemble de clause, la liste renvoyé ne contient aucun doublon*)
let recupererLitteral clauses =
  let rec aux clauses acc = 
    match clauses with 
    |[] -> acc
    |x::xl -> aux xl acc@recupererLitterauxInClause x
  in aux clauses []

(* Cette fonction renvoie un liste l ,tel que pour chaque e appartenant à l alors -e n'appartient pas à l*)
let recupererLitteralUnitaire clauses =
  let rec recuppererLitterauxNonUnitaire liste acc =
    match liste with
    |[] -> acc 
    |x::xl -> if List.mem x clauses && List.mem (-1*x) clauses
                then recuppererLitterauxNonUnitaire xl acc 
                else recuppererLitterauxNonUnitaire xl acc@[x]
    in recuppererLitterauxNonUnitaire clauses []

  *)

(* pur : int list list -> int
    - si `clauses' contient au moins un littéral pur, retourne "Some" de ce littéral ;
    - sinon, None *)
let pur (clauses : int list list) : int option =
  let rec aux l acc =
    match l with 
    | [] -> None
    | x::x1 -> 
      if not(List.mem(x) acc || List.mem (-x) acc) && not(List.mem(-x) x1)
        then (Some x)
        else aux x1 (x::acc)
  
  in aux (List.flatten(clauses)) [] 
                
(* unitaire : int list list -> int
    - si `clauses' contient au moins une clause unitaire, retourne
      "Some" du littéral de cette clause unitaire ;
    - sinon, None *)
let rec unitaire (clauses : int list list) : int option =
  match clauses with 
  |[] -> None
  |x::xl -> if List.length x = 1 then Some (List.hd x) else unitaire xl

(* solveur_dpll_rec : int list list -> int list -> int list option *)
let rec solveur_dpll_rec (clauses : int list list) (interpretation : int list) : int list option =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
  (* un clause vide est insatisfiable *)
  if mem [] clauses then None else
    match unitaire clauses with
    | Some u -> solveur_dpll_rec (simplifie u clauses) (u :: interpretation)
    | None ->
      match pur clauses with
      | Some p -> solveur_dpll_rec (simplifie p clauses) (p :: interpretation)
      | None -> 
        let l = List.hd (List.hd clauses) in
        let branche = solveur_dpll_rec (simplifie l clauses) (l :: interpretation) in
        match branche with
        | None -> solveur_dpll_rec (simplifie (-l) clauses) ((-l) :: interpretation)
        | _ -> branche


(* tests *)
(* ----------------------------------------------------------- *)
(* let () = print_modele (solveur_dpll_rec systeme []) *)
(* let () = print_modele (solveur_dpll_rec coloriage []) *)

let () =
  let clauses = Dimacs.parse Sys.argv.(1) in
  print_modele (solveur_dpll_rec clauses [])

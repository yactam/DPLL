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

(* simplifie : int -> int list list -> int list list 
   applique la simplification de l'ensemble des clauses en mettant
   le littéral l à vrai *)
let simplifie l clauses =
  filter_map (fun c -> (* pour chaque clause *)
    if mem l c (* si l ∈ c *)                 
    then None (* on supprime la clause *)
    else Some ( (* sinon on supprime juste le litral ¬l dans la clause *)
      filter_map (fun l' -> if l' = -l then None else Some(l')) c)
  ) clauses

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

(* pur : int list list -> int
    - si `clauses' contient au moins un littéral pur, retourne
      ce littéral ;
    - sinon, lève une exception `Failure "pas de littéral pur"' *)
let pur clauses =
  let module SL = Set.Make(Int) in 
  let rec pur_aux cf vus non_purs =
    match cf with
    | []   -> failwith "pas de littéral pur"
    | l::x ->
        (* si l est dans l'ensemble des non purs ou ¬l apparait dans x ou 
           non_vus alors il n'est pas pur *)
        if (SL.mem (abs l) non_purs || SL.mem (-l) vus || mem (-l) x)
        (* on cherche un littéral pur dans le reste des littéraux en ajoutant
         l aux littéraux non_purs et les littéreux déja vus  *)
        then pur_aux x (SL.add l vus) (SL.add (abs l) non_purs)
        (* sinon l est pur *)
        else l 
  in pur_aux (List.flatten clauses) (SL.empty) (SL.empty) 

(* unitaire : int list list -> int
    - si `clauses' contient au moins une clause unitaire, retourne
      le littéral de cette clause unitaire ;
    - sinon, lève une exception `Not_found' *)
let unitaire clauses =
  hd (find (fun c -> length c = 1) clauses) 

let moms clauses =
  if clauses = [] then failwith "Empty formula" 
  (* si l'ensemble des clauses est vide alors on ne peut pas brancher sur un 
     litéral *)
  else
    let moms = Hashtbl.create 10 in 
    (* on créé une table de hashage pour stocker chaque literal et son nombre 
       d'occurrence *)
    let min_len = ref (length (hd clauses)) in 
    (* on initialise la taille minimale des clauses à la taille de la première clause *) 
    let max_lit = ref 0 in 
    (* et le literal qui a le maximum de nombre d'occurrence dans ses clauses 
       minimales à 0 *)

    iter (fun c -> min_len := min !min_len (length c)) clauses; 
    (* on cherche la taille minimale des clauses *)

    iter(fun c-> (* pour chaque clause *)
      if length c = !min_len then  (* si sa taille est minimale *)
        iter (fun l -> (* pour chaque literal dans la clause c *)
          let count = Hashtbl.find_opt moms (abs l) |> Option.value ~default:0 in 
          (* on récupère son nombre d'occurrence (0 si c'est pour la première
             fois) *) 
          Hashtbl.replace moms (abs l) (count+1); 
          (* on mis à jour ce nombre d'occurence *)
          if !max_lit = 0 || (count + 1 > Hashtbl.find moms !max_lit) then 
            (* si ce nombre d'occurrence est plus grand que le maximum 
               déja rencotré *)
            max_lit := (abs l) 
            (* on mis à jour le literal qui apparait avec un maximum de nombre d'occurrence *)
        ) c 
    ) clauses;

    !max_lit

(* solveur_dpll_rec : int list list -> int list -> int list option *)
let rec solveur_dpll_rec clauses interpretation =
  match clauses with
  | [] -> Some(interpretation)
  | _  -> 
      if mem [] clauses 
      then None 
      else 
        try
          let unitaire = unitaire clauses in 
          solveur_dpll_rec (simplifie unitaire clauses) (unitaire::interpretation)
        with
        | Not_found ->
            try
              let pur = pur clauses in 
              solveur_dpll_rec (simplifie pur clauses) (pur::interpretation)
            with
            | Failure _ -> 
                let l = moms clauses in
                let branche = solveur_dpll_rec (simplifie l clauses) (l::interpretation) in
                match branche with
                | None -> solveur_dpll_rec (simplifie (-l) clauses) ((-l)::interpretation)
                | _    -> branche


(* tests *)
(* ----------------------------------------------------------- *)
(* let () = print_modele (solveur_dpll_rec systeme []) *)
(* let () = print_modele (solveur_dpll_rec coloriage []) *)

let () =
  let clauses = Dimacs.parse Sys.argv.(1) in
  print_modele (solveur_dpll_rec clauses [])

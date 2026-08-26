(* Hand-written native OCaml for the executable part of the PCF development.

   This is a readable counterpart of [extraction/pcf.ml], not another verified
   artifact.  It implements the same bidirectional checker, call-by-name
   small-step evaluator, and finite strictness analysis.

   The contrast with [nbe-system-t/reference/nbe_native.ml] is instructive.
   System T's semantic family contains OCaml functions and extraction needs
   [Obj.magic] to recover their erased type indices.  Here the syntax is already
   extrinsic, and the only indexed computational family is

       aval Nat       = a definedness bit
       aval (A -> B)  = a finite table

   Extraction erases it to the ordinary [AN | AF] variant below without any
   casts.  The native version therefore keeps that representation and makes
   its trust boundary explicit: malformed low-level combinations either
   return the bottom value, as the Rocq definition does, or reach an
   [assert false] arm that the erased index used to rule out.

   Run it directly with:

       ocaml reference/pcf_native.ml
*)

(* ===== Syntax and types ===== *)

type ty =
  | Tnat
  | Tarr of ty * ty

type term =
  | Tvar of string
  | Tlam of string * term
  | Tapp of term * term
  | Tnum of int
  | Tsucc of term
  | Tpred of term
  | Tifz of term * term * term
  | Tfix of ty * term
  | Tann of term * ty

type ctx = (string * ty) list

let rec ty_eqb a b =
  match a, b with
  | Tnat, Tnat -> true
  | Tarr (a1, a2), Tarr (b1, b2) -> ty_eqb a1 b1 && ty_eqb a2 b2
  | _ -> false

let rec lookup gamma x =
  match gamma with
  | [] -> None
  | (y, a) :: gamma' -> if x = y then Some a else lookup gamma' x

(* ===== Bidirectional type checking ===== *)

type error =
  | E_Unbound of string
  | E_NoSynth of term
  | E_NotFun of term * ty
  | E_LamNotFun of term * ty
  | E_Mismatch of term * ty * ty

type 'a result =
  | Ok of 'a
  | Err of error

let lookup_ty gamma x =
  match lookup gamma x with
  | Some a -> Ok a
  | None -> Err (E_Unbound x)

let after result a =
  match result with
  | Ok () -> Ok a
  | Err e -> Err e

let switch t expected = function
  | Ok actual when ty_eqb actual expected -> Ok ()
  | Ok actual -> Err (E_Mismatch (t, expected, actual))
  | Err e -> Err e

let apply_to f function_ty check_argument =
  match function_ty with
  | Ok Tnat -> Err (E_NotFun (f, Tnat))
  | Ok (Tarr (domain, codomain)) -> after (check_argument domain) codomain
  | Err e -> Err e

let rec infer gamma t =
  match t with
  | Tvar x -> lookup_ty gamma x
  | Tapp (f, u) -> apply_to f (infer gamma f) (check gamma u)
  | Tnum _ -> Ok Tnat
  | Tsucc u -> after (check gamma u Tnat) Tnat
  | Tpred u -> after (check gamma u Tnat) Tnat
  | Tfix (a, u) -> after (check gamma u (Tarr (a, a))) a
  | Tann (u, a) -> after (check gamma u a) a
  | Tlam _ | Tifz _ -> Err (E_NoSynth t)

and check gamma t expected =
  match t, expected with
  | Tlam (_, _), Tnat -> Err (E_LamNotFun (t, Tnat))
  | Tlam (x, body), Tarr (domain, codomain) ->
      check ((x, domain) :: gamma) body codomain
  | Tifz (condition, if_zero, if_nonzero), _ ->
      (match check gamma condition Tnat with
       | Err e -> Err e
       | Ok () ->
           (match check gamma if_zero expected with
            | Err e -> Err e
            | Ok () -> check gamma if_nonzero expected))
  | _, _ -> switch t expected (infer gamma t)

(* ===== Call-by-name operational semantics ===== *)

(* Substitution is deliberately the source algorithm's simple named
   substitution.  Evaluation is exposed for closed, checked programs, so the
   substituted argument is closed and capture cannot occur. *)
let rec subst x replacement t =
  match t with
  | Tvar y -> if x = y then replacement else t
  | Tlam (y, body) ->
      if x = y then t else Tlam (y, subst x replacement body)
  | Tapp (f, u) -> Tapp (subst x replacement f, subst x replacement u)
  | Tnum n -> Tnum n
  | Tsucc u -> Tsucc (subst x replacement u)
  | Tpred u -> Tpred (subst x replacement u)
  | Tifz (c, a, b) ->
      Tifz (subst x replacement c, subst x replacement a,
            subst x replacement b)
  | Tfix (a, u) -> Tfix (a, subst x replacement u)
  | Tann (u, a) -> Tann (subst x replacement u, a)

type step_result =
  | SNext of term
  | SValue
  | SStuck of term

let rec step t =
  match t with
  | Tvar _ -> SStuck t
  | Tapp (Tlam (x, body), argument) -> SNext (subst x argument body)
  | Tapp (f, u) ->
      (match step f with
       | SNext f' -> SNext (Tapp (f', u))
       | SValue -> SStuck t
       | SStuck stuck -> SStuck stuck)
  | Tsucc (Tnum n) -> SNext (Tnum (n + 1))
  | Tsucc u ->
      (match step u with
       | SNext u' -> SNext (Tsucc u')
       | SValue -> SStuck t
       | SStuck stuck -> SStuck stuck)
  | Tpred (Tnum n) -> SNext (Tnum (if n <= 0 then 0 else n - 1))
  | Tpred u ->
      (match step u with
       | SNext u' -> SNext (Tpred u')
       | SValue -> SStuck t
       | SStuck stuck -> SStuck stuck)
  | Tifz (Tnum n, if_zero, if_nonzero) ->
      SNext (if n <= 0 then if_zero else if_nonzero)
  | Tifz (condition, if_zero, if_nonzero) ->
      (match step condition with
       | SNext condition' ->
           SNext (Tifz (condition', if_zero, if_nonzero))
       | SValue -> SStuck t
       | SStuck stuck -> SStuck stuck)
  | Tfix (a, u) -> SNext (Tapp (u, Tfix (a, u)))
  | Tann (u, _) -> SNext u
  | Tlam _ | Tnum _ -> SValue

type eval_result =
  | Value of term
  | Timeout
  | Stuck of term

let rec evalFuel fuel t =
  if fuel <= 0 then Timeout
  else
    match step t with
    | SNext t' -> evalFuel (fuel - 1) t'
    | SValue -> Value t
    | SStuck stuck -> Stuck stuck

let eval_fuel = evalFuel

(* ===== Finite abstract domain ===== *)

type ('input, 'output) table = ('input * 'output) list

type aval =
  | AN of bool
  | AF of (aval, aval) table

let rec table_eqb
    (equal_input : 'input -> 'input -> bool)
    (equal_output : 'output -> 'output -> bool)
    (ts : ('input, 'output) table)
    (us : ('input, 'output) table) : bool =
  match ts, us with
  | [], [] -> true
  | (a1, b1) :: ts', (a2, b2) :: us' ->
      equal_input a1 a2
      && equal_output b1 b2
      && table_eqb equal_input equal_output ts' us'
  | _ -> false

let rec aval_eqb ty v w =
  match ty, v, w with
  | Tnat, AN a, AN b -> Bool.equal a b
  | Tarr (domain, codomain), AF ts, AF us ->
      table_eqb (aval_eqb domain) (aval_eqb codomain) ts us
  | _ -> assert false

let rec concat_map f = function
  | [] -> []
  | x :: xs -> f x @ concat_map f xs

let rec all_tables
    (inputs : 'input list)
    (outputs : 'output list) : ('input, 'output) table list =
  match inputs with
  | [] -> [ [] ]
  | input :: inputs' ->
      concat_map
        (fun output ->
          List.map
            (fun table -> (input, output) :: table)
            (all_tables inputs' outputs))
        outputs

let rec table_leb
    (less_output : 'output -> 'output -> bool)
    (ts : ('input, 'output) table)
    (us : ('input, 'output) table) : bool =
  match ts, us with
  | [], [] -> true
  | (_, b) :: ts', (_, b') :: us' ->
      less_output b b' && table_leb less_output ts' us'
  | _ -> false

let rec aleb ty v w =
  match ty, v, w with
  | Tnat, AN a, AN b -> (not a) || b
  | Tarr (_, codomain), AF ts, AF us ->
      table_leb (aleb codomain) ts us
  | _ -> assert false

let monotone_tbl domain codomain (table : (aval, aval) table) =
  List.for_all
    (fun (input, output) ->
      List.for_all
        (fun (input', output') ->
          not (aleb domain input input') || aleb codomain output output')
        table)
    table

let rec enum = function
  | Tnat -> [AN false; AN true]
  | Tarr (domain, codomain) ->
      List.map
        (fun table -> AF table)
        (List.filter
           (monotone_tbl domain codomain)
           (all_tables (enum domain) (enum codomain)))

let rec abot = function
  | Tnat -> AN false
  | Tarr (domain, codomain) ->
      AF (List.map (fun input -> input, abot codomain) (enum domain))

let rec int_pow base exponent =
  if exponent <= 0 then 1 else base * int_pow base (exponent - 1)

let rec dsize = function
  | Tnat -> 2
  | Tarr (domain, codomain) -> int_pow (dsize codomain) (dsize domain)

let aapply domain codomain function_value argument =
  match function_value with
  | AN _ -> assert false
  | AF table ->
      (match List.find_opt
               (fun (input, _) -> aval_eqb domain input argument)
               table
       with
       | Some (_, output) -> output
       | None -> abot codomain)

let rec join_tables
    (join_output : 'output -> 'output -> 'output)
    (ts : ('input, 'output) table)
    (us : ('input, 'output) table) : ('input, 'output) table =
  match ts, us with
  | (input, output) :: ts', (_, output') :: us' ->
      (input, join_output output output') :: join_tables join_output ts' us'
  | _ -> ts

let rec ajoin ty v w =
  match ty, v, w with
  | Tnat, AN a, AN b -> AN (a || b)
  | Tarr (_, codomain), AF ts, AF us ->
      AF (join_tables (ajoin codomain) ts us)
  | _ -> assert false

let an_defined = function
  | AN defined -> defined
  | AF _ -> assert false

let rec iter count f x =
  if count <= 0 then x else f (iter (count - 1) f x)

let afix_approx ty function_value count =
  iter count (aapply ty ty function_value) (abot ty)

(* ===== Abstract environments and interpreter ===== *)

type packed_aval = PackAval of ty * aval
type aenv = (string * packed_aval) list

let rec alookup env x =
  match env with
  | [] -> None
  | (y, value) :: env' -> if x = y then Some value else alookup env' x

let unpack_aval expected = function
  | PackAval (actual, value) ->
      if ty_eqb actual expected then value else abot expected

let rec aeval gamma env t expected =
  match t with
  | Tvar x ->
      (match alookup env x with
       | Some value -> unpack_aval expected value
       | None -> abot expected)
  | Tlam (x, body) ->
      (match expected with
       | Tnat -> abot Tnat
       | Tarr (domain, codomain) ->
           AF
             (List.map
                (fun input ->
                  input,
                  aeval
                    ((x, domain) :: gamma)
                    ((x, PackAval (domain, input)) :: env)
                    body codomain)
                (enum domain)))
  | Tapp (f, u) ->
      (match infer gamma f with
       | Ok (Tarr (domain, codomain)) when ty_eqb codomain expected ->
           aapply domain codomain
             (aeval gamma env f (Tarr (domain, codomain)))
             (aeval gamma env u domain)
       | Ok Tnat | Ok (Tarr _) | Err _ -> abot expected)
  | Tnum _ ->
      (match expected with
       | Tnat -> AN true
       | Tarr _ -> abot expected)
  | Tsucc u | Tpred u ->
      (match expected with
       | Tnat -> aeval gamma env u Tnat
       | Tarr _ -> abot expected)
  | Tifz (condition, if_zero, if_nonzero) ->
      if an_defined (aeval gamma env condition Tnat) then
        ajoin expected
          (aeval gamma env if_zero expected)
          (aeval gamma env if_nonzero expected)
      else
        abot expected
  | Tfix (annotated, body) ->
      if ty_eqb annotated expected then
        afix_approx annotated
          (aeval gamma env body (Tarr (annotated, annotated)))
          (dsize annotated)
      else
        abot expected
  | Tann (body, annotated) ->
      if ty_eqb annotated expected then
        aeval gamma env body annotated
      else
        abot expected

let analyse t ty = aeval [] [] t ty

let certified_strict t =
  match check [] t (Tarr (Tnat, Tnat)) with
  | Err _ -> false
  | Ok () ->
      aval_eqb Tnat
        (aapply Tnat Tnat (analyse t (Tarr (Tnat, Tnat))) (AN false))
        (AN false)

(* ===== Example programs from [theories/Examples.v] and [Extract.v] ===== *)

let add_body =
  Tlam ("f",
    Tlam ("m",
      Tlam ("n",
        Tifz (Tvar "m", Tvar "n",
          Tsucc (Tapp (Tapp (Tvar "f", Tpred (Tvar "m")), Tvar "n"))))))

let add = Tfix (Tarr (Tnat, Tarr (Tnat, Tnat)), add_body)

let mul =
  Tfix (Tarr (Tnat, Tarr (Tnat, Tnat)),
    Tlam ("f",
      Tlam ("m",
        Tlam ("n",
          Tifz (Tvar "m", Tnum 0,
            Tapp (Tapp (add, Tvar "n"),
              Tapp (Tapp (Tvar "f", Tpred (Tvar "m")), Tvar "n")))))))

let fact_body =
  Tlam ("f",
    Tlam ("n",
      Tifz (Tvar "n", Tnum 1,
        Tapp (Tapp (mul, Tvar "n"),
          Tapp (Tvar "f", Tpred (Tvar "n"))))))

let fact = Tfix (Tarr (Tnat, Tnat), fact_body)

let omega_at a = Tfix (a, Tlam ("x", Tvar "x"))
let omega = omega_at Tnat
let delta = Tlam ("x", Tapp (Tvar "x", Tvar "x"))
let omega_untyped = Tapp (delta, delta)
let stuck_succ = Tsucc (Tlam ("x", Tvar "x"))
let cbn_flagship = Tapp (Tlam ("x", Tnum 0), omega)

let cbn_flagship_ann =
  Tapp (Tann (Tlam ("x", Tnum 0), Tarr (Tnat, Tnat)), omega)

let loop =
  Tfix (Tarr (Tnat, Tnat),
    Tlam ("g",
      Tlam ("n",
        Tifz (Tvar "n", Tapp (Tvar "g", Tnum 0), Tnum 0))))

let blind = Tlam ("x", Tapp (loop, Tnum 0))

let slow =
  Tfix (Tarr (Tnat, Tnat),
    Tlam ("f",
      Tlam ("n",
        Tifz (Tvar "n", Tnum 0,
          Tapp (Tvar "f", Tpred (Tvar "n"))))))

let strict_succ = Tlam ("x", Tsucc (Tvar "x"))
let const_zero = Tlam ("x", Tnum 0)
let ex_id = Tlam ("x", Tvar "x")
let ex_id_ann = Tann (ex_id, Tarr (Tnat, Tnat))

let ex_apply_to_three =
  Tapp
    (Tann
       (Tlam ("f", Tapp (Tvar "f", Tnum 0)),
        Tarr (Tarr (Tnat, Tnat), Tnat)),
     Tnum 3)

(* ===== Pretty-printers and executable smoke tests ===== *)

let rec pp_ty = function
  | Tnat -> "Nat"
  | Tarr (a, b) -> pp_ty_atom a ^ " -> " ^ pp_ty b

and pp_ty_atom = function
  | Tnat -> "Nat"
  | Tarr _ as a -> "(" ^ pp_ty a ^ ")"

let rec pp_term = function
  | Tvar x -> x
  | Tlam (x, body) -> "fun " ^ x ^ " -> " ^ pp_term body
  | Tapp (f, u) -> "(" ^ pp_term f ^ " " ^ pp_term u ^ ")"
  | Tnum n -> string_of_int n
  | Tsucc u -> "succ (" ^ pp_term u ^ ")"
  | Tpred u -> "pred (" ^ pp_term u ^ ")"
  | Tifz (c, a, b) ->
      "ifz " ^ pp_term c ^ " then " ^ pp_term a ^ " else " ^ pp_term b
  | Tfix (a, u) -> "fix[" ^ pp_ty a ^ "] (" ^ pp_term u ^ ")"
  | Tann (u, a) -> "(" ^ pp_term u ^ " : " ^ pp_ty a ^ ")"

let rec pp_aval = function
  | AN false -> "bottom"
  | AN true -> "defined"
  | AF table ->
      "{" ^
      String.concat ", "
        (List.map
           (fun (input, output) -> pp_aval input ^ " |-> " ^ pp_aval output)
           table)
      ^ "}"

let run_examples () =
  let nn = Tarr (Tnat, Tnat) in
  assert (infer [] fact = Ok nn);
  assert (infer [] omega = Ok Tnat);
  assert (check [] omega_untyped Tnat <> Ok ());
  assert (infer [] ex_id_ann = Ok nn);
  assert (evalFuel 5000 (Tapp (fact, Tnum 3)) = Value (Tnum 6));
  assert (evalFuel 5000 omega = Timeout);
  assert (evalFuel 2 cbn_flagship = Value (Tnum 0));
  assert (evalFuel 10 stuck_succ = Stuck stuck_succ);
  assert (certified_strict strict_succ);
  assert (not (certified_strict const_zero));
  assert (certified_strict fact);
  assert (certified_strict slow);
  assert (certified_strict loop);
  assert (not (certified_strict blind));
  assert (not (certified_strict omega));
  print_endline "Native PCF reference:";
  Printf.printf "  fact 3       ~> %s\n"
    (match evalFuel 5000 (Tapp (fact, Tnum 3)) with
     | Value value -> pp_term value
     | Timeout -> "timeout"
     | Stuck stuck -> "stuck at " ^ pp_term stuck);
  Printf.printf "  (fun x -> 0) omega, fuel 2 ~> %s\n"
    (match evalFuel 2 cbn_flagship with
     | Value value -> pp_term value
     | Timeout -> "timeout"
     | Stuck stuck -> "stuck at " ^ pp_term stuck);
  Printf.printf "  analyse fact ~> %s\n" (pp_aval (analyse fact nn));
  Printf.printf "  strict(fact) ~> %b\n" (certified_strict fact);
  Printf.printf "  strict(fun x -> 0) ~> %b\n" (certified_strict const_zero)

(* As in [nbe_native.ml], loading with [#mod_use] has no side effect. *)
let () =
  if Filename.basename Sys.argv.(0) = "pcf_native.ml" then run_examples ()

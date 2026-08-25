(* A small handwritten front end for the extracted raw PCF syntax.

   This module is intentionally ordinary, unverified OCaml. Its output becomes
   trustworthy only after the extracted checker accepts it. The grammar is:

     type ::= Nat | (type) | type -> type
     term ::= fun x -> term | ifz term then term else term | term : type
            | term term | succ term | pred term | fix[type] term
            | x | n | (term)

   Application associates left, arrows associate right, and an annotation has
   the lowest precedence. Parentheses delimit non-atomic operands. Unicode λ,
   ℕ, and →/⇒ are accepted as conveniences. *)

type position = {
  offset : int;
  line : int;
  column : int;
}

type error = {
  position : position;
  message : string;
}

let string_of_error { position; message } =
  Printf.sprintf "line %d, column %d: %s"
    position.line position.column message

exception Parse_failure of error

let fail position format =
  Printf.ksprintf
    (fun message -> raise (Parse_failure { position; message }))
    format

type token_kind =
  | Ident of string
  | Int of int
  | Lparen
  | Rparen
  | Lbracket
  | Rbracket
  | Colon
  | Dot
  | Lambda
  | Arrow
  | Succ
  | Pred
  | Ifz
  | Then
  | Else
  | Fix
  | Nat
  | Eof

type token = {
  kind : token_kind;
  position : position;
}

let starts_with source offset text =
  let source_length = String.length source in
  let text_length = String.length text in
  offset + text_length <= source_length
  && String.sub source offset text_length = text

let is_ident_start = function
  | 'a' .. 'z' | 'A' .. 'Z' | '_' -> true
  | _ -> false

let is_ident_continue = function
  | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '\'' -> true
  | _ -> false

let keyword_or_ident = function
  | "fun" | "lambda" -> Lambda
  | "succ" -> Succ
  | "pred" -> Pred
  | "ifz" -> Ifz
  | "then" -> Then
  | "else" -> Else
  | "fix" -> Fix
  | "Nat" | "nat" | "N" -> Nat
  | name -> Ident name

let is_digit = function
  | '0' .. '9' -> true
  | _ -> false

let tokenize source =
  let length = String.length source in
  let rec loop offset line column tokens =
    let position = { offset; line; column } in
    if offset = length then
      Array.of_list (List.rev ({ kind = Eof; position } :: tokens))
    else
      match source.[offset] with
      | ' ' | '\t' | '\r' -> loop (offset + 1) line (column + 1) tokens
      | '\n' -> loop (offset + 1) (line + 1) 1 tokens
      | '(' -> emit Lparen 1 1 offset line column tokens
      | ')' -> emit Rparen 1 1 offset line column tokens
      | '[' -> emit Lbracket 1 1 offset line column tokens
      | ']' -> emit Rbracket 1 1 offset line column tokens
      | ':' -> emit Colon 1 1 offset line column tokens
      | '.' -> emit Dot 1 1 offset line column tokens
      | '\\' -> emit Lambda 1 1 offset line column tokens
      | '-' when starts_with source offset "->" ->
          emit Arrow 2 2 offset line column tokens
      | '=' when starts_with source offset "=>" ->
          emit Arrow 2 2 offset line column tokens
      | '0' .. '9' ->
          let rec scan finish =
            if finish < length && is_digit source.[finish] then
              scan (finish + 1)
            else
              finish
          in
          let finish = scan (offset + 1) in
          let spelling = String.sub source offset (finish - offset) in
          let value =
            try int_of_string spelling
            with Failure _ -> fail position "natural-number literal is out of range"
          in
          loop finish line (column + finish - offset)
            ({ kind = Int value; position } :: tokens)
      | character when is_ident_start character ->
          let finish = ref (offset + 1) in
          while !finish < length && is_ident_continue source.[!finish] do
            incr finish
          done;
          let spelling = String.sub source offset (!finish - offset) in
          loop !finish line (column + !finish - offset)
            ({ kind = keyword_or_ident spelling; position } :: tokens)
      | _ when starts_with source offset "λ" ->
          emit Lambda (String.length "λ") 1 offset line column tokens
      | _ when starts_with source offset "ℕ" ->
          emit Nat (String.length "ℕ") 1 offset line column tokens
      | _ when starts_with source offset "→" ->
          emit Arrow (String.length "→") 1 offset line column tokens
      | _ when starts_with source offset "⇒" ->
          emit Arrow (String.length "⇒") 1 offset line column tokens
      | character -> fail position "unexpected character %C" character
  (* [bytes] advances the offset, [cols] the reported column: they differ
     both ways — "->" is one token two columns wide, "λ" is one column three
     bytes wide. *)
  and emit kind bytes cols offset line column tokens =
    let position = { offset; line; column } in
    loop (offset + bytes) line (column + cols) ({ kind; position } :: tokens)
  in
  loop 0 1 1 []

type state = {
  tokens : token array;
  mutable cursor : int;
}

let current state = state.tokens.(state.cursor)

let advance state =
  let token = current state in
  state.cursor <- state.cursor + 1;
  token

let token_name = function
  | Ident name -> Printf.sprintf "identifier %S" name
  | Int value -> string_of_int value
  | Lparen -> "'('"
  | Rparen -> "')'"
  | Lbracket -> "'['"
  | Rbracket -> "']'"
  | Colon -> "':'"
  | Dot -> "'.'"
  | Lambda -> "'fun'"
  | Arrow -> "'->'"
  | Succ -> "'succ'"
  | Pred -> "'pred'"
  | Ifz -> "'ifz'"
  | Then -> "'then'"
  | Else -> "'else'"
  | Fix -> "'fix'"
  | Nat -> "'Nat'"
  | Eof -> "end of input"

let accept state expected =
  if (current state).kind = expected then begin
    ignore (advance state);
    true
  end else
    false

let expect state expected =
  let token = current state in
  if token.kind = expected then
    ignore (advance state)
  else
    fail token.position "expected %s, found %s"
      (token_name expected) (token_name token.kind)

let rec parse_type state =
  let domain = parse_type_atom state in
  if accept state Arrow then
    Pcf.Tarr (domain, parse_type state)
  else
    domain

and parse_type_atom state =
  let token = current state in
  match token.kind with
  | Nat ->
      ignore (advance state);
      Pcf.Tnat
  | Lparen ->
      ignore (advance state);
      let ty = parse_type state in
      expect state Rparen;
      ty
  | _ ->
      fail token.position "expected a type, found %s" (token_name token.kind)

let rec parse_term state = parse_annotation state

and parse_annotation state =
  let term = parse_core state in
  if accept state Colon then
    Pcf.Tann (term, parse_type state)
  else
    term

and parse_core state =
  match (current state).kind with
  | Lambda -> parse_lambda state
  | Ifz -> parse_ifz state
  | _ -> parse_application state

and parse_lambda state =
  ignore (advance state);
  let binder_token = current state in
  let binder =
    match binder_token.kind with
    | Ident name ->
        ignore (advance state);
        name
    | _ ->
        fail binder_token.position "expected a binder name, found %s"
          (token_name binder_token.kind)
  in
  begin match (current state).kind with
  | Arrow | Dot -> ignore (advance state)
  | found ->
      fail (current state).position "expected '->' or '.', found %s"
        (token_name found)
  end;
  Pcf.Tlam (binder, parse_core state)

and parse_ifz state =
  ignore (advance state);
  let condition = parse_term state in
  expect state Then;
  let zero_branch = parse_term state in
  expect state Else;
  let successor_branch = parse_core state in
  Pcf.Tifz (condition, zero_branch, successor_branch)

and parse_application state =
  let function_term = parse_prefix state in
  let rec arguments term =
    if starts_prefix (current state).kind then
      arguments (Pcf.Tapp (term, parse_prefix state))
    else
      term
  in
  arguments function_term

and starts_prefix = function
  | Ident _ | Int _ | Lparen | Succ | Pred | Fix -> true
  | _ -> false

and parse_prefix state =
  match (current state).kind with
  | Succ ->
      ignore (advance state);
      Pcf.Tsucc (parse_prefix state)
  | Pred ->
      ignore (advance state);
      Pcf.Tpred (parse_prefix state)
  | Fix ->
      ignore (advance state);
      expect state Lbracket;
      let ty = parse_type state in
      expect state Rbracket;
      Pcf.Tfix (ty, parse_prefix state)
  | _ -> parse_atom state

and parse_atom state =
  let token = current state in
  match token.kind with
  | Ident name ->
      ignore (advance state);
      Pcf.Tvar name
  | Int value ->
      ignore (advance state);
      Pcf.Tnum value
  | Lparen ->
      ignore (advance state);
      let term = parse_term state in
      expect state Rparen;
      term
  | _ ->
      fail token.position "expected a term, found %s" (token_name token.kind)

let parse source =
  try
    let state = { tokens = tokenize source; cursor = 0 } in
    let term = parse_term state in
    let trailing = current state in
    begin match trailing.kind with
    | Eof -> Result.Ok term
    | _ ->
        fail trailing.position "unexpected %s after the complete term"
          (token_name trailing.kind)
    end
  with Parse_failure error -> Result.Error error

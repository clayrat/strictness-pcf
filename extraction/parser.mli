(** Handwritten, unverified surface parser for the extracted PCF syntax. *)

type position = {
  offset : int;
  line : int;
  column : int;
}

type error = {
  position : position;
  message : string;
}

val string_of_error : error -> string

(** [parse source] translates one complete source term into the raw [Pcf.term]
    datatype. It performs no scope or type checking; use [Pcf.infer] or
    [Pcf.check] on the result when those guarantees are needed. *)
val parse : string -> (Pcf.term, error) Stdlib.result

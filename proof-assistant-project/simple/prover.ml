let () = Printexc.record_backtrace true

open Expr
open Helpers

let _test_parsing () =
  let l =
    [
      "A => B";
      "A ⇒ B";
      "A /\\ B";
      "A ∧ B";
      "T";
      "A \\/ B";
      "A ∨ B";
      "_";
      "not A";
      "¬ A";
      "(A => B) => A => (B)";
    ]
  in
  List.iter
    (fun s ->
      Printf.printf "the parsing of %S is %s\n%!" s
        (string_of_ty (ty_of_string s)))
    l;
  let l =
    [
      "t u v";
      "fun (x : A) -> t";
      "λ (x : A) → t";
      "(t , u)";
      "fst(t)";
      "snd(t)";
      "()";
      "case t of x -> u | y -> v";
      "left(t,B)";
      "right(A,t)";
      "absurd(t,A)";
    ]
  in
  List.iter
    (fun s ->
      Printf.printf "the parsing of %S is %s\n%!" s
        (string_of_tm (tm_of_string s)))
    l

let string_of_ctx ctx =
  String.concat " , "
    (List.map (fun (x, ty) -> x ^ " : " ^ string_of_ty ty) ctx)

type sequent = context * ty

let string_of_seq (ctx, ty) = string_of_ctx ctx ^ " |- " ^ string_of_ty ty

let proof_steps = ref []

let rec prove env a =
  print_endline (string_of_seq (env, a));
  print_string "? ";
  flush_all ();
  let error e =
    if e <> "" then print_endline e;
    (proof_steps := match !proof_steps with [] -> [] | _ :: rem -> rem);
    prove env a
  in
  let cmd, arg =
    let cmd = input_line stdin in
    proof_steps := cmd :: !proof_steps;
    let n = try String.index cmd ' ' with Not_found -> String.length cmd in
    let c = String.sub cmd 0 n in
    let a = String.sub cmd n (String.length cmd - n) in
    let a = String.trim a in
    (c, a)
  in
  try
    match cmd with
    | "intro" -> (
        match a with
        | Imp (a, b) ->
            if arg = "" then error "Please provide an argument for intro."
            else
              let x = arg in
              let t = prove ((x, a) :: env) b in
              Abs (x, a, t)
        | And (a, b) ->
            let pa = prove env a in
            let pb = prove env b in
            Pair (pa, pb)
        | True -> Unit
        | _ -> error "Don't know how to introduce this.")
    | "exact" -> (
        if arg = "" then error "Please provide an argument for exact."
        else
          let t = tm_of_string arg in
          try if infer_type env t <> a then error "Not the right type." else t
          with Type_error -> error "Invalid variable name.")
    | "elim" -> (
        if arg = "" then error "Please provide an argument for elim."
        else
          let t = Var arg in
          match infer_type env t with
          | Imp (x, fx) when fx = a -> App (t, prove env x)
          | Or (x, y) ->
              let env' = List.filter (fun (z, _) -> z <> arg) env in
              let px = prove ((arg, x) :: env') a in
              let py = prove ((arg, y) :: env') a in
              Case (t, arg, px, arg, py)
          | False -> Absurd (t, a)
          | Nat ->
              print_endline (arg ^ " = 0");
              let z = prove env a in
              print_endline (arg ^ " = S(" ^ arg ^ ")");
              let s = prove env (Imp (a, a)) in
              Rec (t, z, Abs (arg, Nat, s))
          | _ -> error "Don't know how to eliminate this.")
    | "cut" ->
        if arg = "" then error "Please provide an argument for cut."
        else
          let _B = ty_of_string arg in
          let f = prove env (Imp (_B, a)) in
          let x = prove env _B in
          App (f, x)
    | "fst" -> (
        if arg = "" then error "Please provide an argument for fst."
        else
          let t = tm_of_string arg in
          try
            match infer_type env t with
            | And (x, _) when x = a -> Fst t
            | And _ -> error "Not the right type."
            | _ -> error "Not a conjunction."
          with Type_error -> error "Invalid variable name.")
    | "snd" -> (
        if arg = "" then error "Please provide an argument for snd."
        else
          let t = tm_of_string arg in
          try
            match infer_type env t with
            | And (_, y) when y = a -> Snd t
            | And _ -> error "Not the right type."
            | _ -> error "Not a conjunction."
          with Type_error -> error "Invalid variable name.")
    | "left" -> (
        match a with
        | Or (x, y) -> Left (prove env x, y)
        | _ -> error "Not a disjunction.")
    | "right" -> (
        match a with
        | Or (x, y) -> Right (x, prove env y)
        | _ -> error "Not a disjunction.")
    | "zero" -> (
        match a with Nat -> Zero | _ -> error "Not a natural number.")
    | "succ" -> (
        match a with
        | Nat -> Succ (prove env Nat)
        | _ -> error "Not a natural number.")
    | cmd -> error (if cmd <> "" then "Unknown command: " ^ cmd else "")
  with Parsing.Parse_error -> error "Invalid formula."

let exit_ceremony target =
  try
    let should_save =
      print_string "Do you want to save the proof? [y/N] ";
      flush_all ();
      let answer = String.lowercase_ascii (input_line stdin) in
      answer = "yes" || answer = "y"
    in
    if should_save then (
      let output_filename =
        print_string "Please enter the output filename: [out.proof] ";
        flush_all ();
        let answer = input_line stdin in
        if answer = "" then "out.proof" else answer
      in
      let oc = open_out (String.trim output_filename) in
      output_string oc (target ^ "\n");
      output_string oc (String.concat "\n" (List.rev !proof_steps) ^ "\n");
      close_out oc;
      print_endline ("Proof saved in " ^ output_filename))
  with End_of_file -> ()

let () =
  print_endline "Please enter the formula to prove:";
  let target = input_line stdin in
  try
    let a = ty_of_string target in
    print_endline "Let's prove it.";
    let t = prove [] a in
    print_endline "done.";
    print_endline "Proof term is";
    print_endline (string_of_tm t);
    print_string "Typechecking... ";
    flush_all ();
    assert (infer_type [] t = a);
    print_endline "ok.";
    exit_ceremony target
  with Parsing.Parse_error -> print_endline "Invalid formula."

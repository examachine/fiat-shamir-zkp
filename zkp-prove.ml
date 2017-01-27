open Printf
open Scanf
open Arg
open UnixLabels
open Nat
open Cryptokit
open Config

let id = ref ""

let init = ref false

let host = ref ""

let port = ref 0

let speclist = 	  
  [ ("--init", Bool (fun x -> init := x), "generate keys");
    ("--id", String (fun x -> id := x), "authentication ID");
    ("--host", String (fun x -> host := x), "authentication host");
    ("--port", Arg.String (fun x -> port := (int_of_string x)),
     "authentication port") ]

let usage_msg = 
"Usage:
  zkp-prove --init true
  zkp-prove --id <auth-id> --host <hostname> ---port <port #>"


let risqrmodn ri n = Bn.mod_ (Bn.mult ri ri) n

let alice input output n v s =
  let rng = Random.pseudo_rng (Random.string Random.secure_rng 20) in

    (* 0. Alice sends user id in plain text *)
    fprintf output "ZKP%S\n%!" !id;

    (* 1. Alice chooses k random numbers r_1,r_2,...,r_k. For each
       r_i, she sends r_i^2 mod n to Bob *)
    let r = Array.init Config.num_challenges
	      (fun x -> Lowlife.random_prime ~rng:rng 768) in
      Array.iter
	(fun ri ->
	   fprintf output "%s\n%!"(string_of_nat (risqrmodn ri n));
	   printf "wrote: %s \n" (string_of_nat (risqrmodn ri n))
	) r;
      printf "%s Phase 1: Sent %d ri^2 mod n for\n%!"
	!id Config.num_challenges;

      (* 2. Bob chooses a random subset of the r_i^2 and tells Alice
	 which subset he has selected to be known as subset 1. The
	 others will be known as subset 2 *)
      let subset1 = Array.make Config.num_challenges false in
	for i = 0 to (Array.length subset1)-1 do
	  let s = input_line input in
	  let buf1 = Scanning.from_string s in
	    bscanf buf1 "%b" (fun b -> subset1.(i) <- b);
	    (*printf "read subset[%d]=%b for phase 2\n" i subset1.(i);*)
	done;
	printf "Phase 2: sent subset info\n%!";


	(* 3. Alice sends sr_i mod n for each r_i^2 of subset 1, and
	   sends r_i mod n for each r_i^2 of subset 2 *)
	for i = 0 to (Array.length r)-1 do
	  let val2send = 
	    if subset1.(i) then
	      Bn.mod_ (Bn.mult s r.(i)) n
	    else
	      Bn.mod_ r.(i) n in
	    fprintf output "%s\n" (string_of_nat val2send);
	    printf "%s\n" (string_of_nat val2send)
	done;
	flush output;


	(* 4. Bob squares Alice's replies mod n. For those r_i^2 in
	   subset 1 he checks that the square of the reply is vr_i^2
	   mod n. For those r_i^2 in subset 2, he checks that the
	   square of the reply is r_i^2 mod n. *)

	printf "Proved identity for %s\n%!" !id

let main () =
  printf "Fiat-Shamir Zero Knowledge Proof system, authentication agent\n%!";
  Arg.parse speclist (fun x -> ()) usage_msg;
  if !init then (
    printf "Generating public keys\n";
    Config.init_keys ();
  )
  else (
    if !id = "" then (
      printf "No authentication ID given\n";
      Arg.usage speclist usage_msg;
      exit 2;
    );
    if !host = "" then (
      printf "No authentication host given\n";
      Arg.usage speclist usage_msg;
      exit 2;
    );
    if !port = 0 then (
      printf "No authentication port given";
      Arg.usage speclist usage_msg;
      exit 2;
    );
    printf "Proving identity for %s\n" !id;
    Config.read_config ();
    if Config.KeyDict.mem !id !Config.public_keys then
      printf "Public key found for %s\n" !id
    else (
      printf "No public key found for %s\n" !id;
      exit 2;
    );
    if Config.KeyDict.mem !id !Config.secret_keys then
      printf "Secret key found for %s\n" !id
    else (
      printf "No secret key found for %s\n" !id;
      exit 2;
    )
    printf "Opening connection to server %s:%d %!" !host !port;
    print_newline ();
    let hostaddr = handle_unix_error inet_addr_of_string !host in
    let (input, output) =
      open_connection (ADDR_INET (hostaddr, !port)) in
      printf "Connection established \n";
      let public_key = Config.KeyDict.find !id !Config.public_keys
      and secret_key = Config.KeyDict.find !id !Config.secret_keys in
	alice input output public_key.n public_key.v secret_key;
	shutdown_connection input ;
  )
;;
    

main ();

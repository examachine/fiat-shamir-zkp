open Printf
open Scanf
open UnixLabels
open Nat
open Config

let print_sockaddr sa =
  match sa with
      ADDR_UNIX str -> printf "%s" str
    | ADDR_INET (host, port) -> printf "%s:%d"
	(string_of_inet_addr host) port

let port = ref 0

let speclist = 	  
  [ ("--port", Arg.String (fun x -> port := (int_of_string x)),
     "authentication port") ]

let usage_msg =  "Usage: zkp-check --port <port #>"

let risqrmodn ri n = Bn.mod_ (Bn.mult ri ri) n

let bob input output = 
  printf "handling connection\n%!";
  let id = ref "" in
    try
      Random.self_init ();
      (* 0. Alice sends user id in plain text *)
      (let line1 = input_line input in
	 printf "read line: <%s>\n" line1;
	 sscanf line1 "ZKP%S" (fun n -> id := n));
      printf "Authenticating [%s] \n%!" !id;
      if Config.KeyDict.mem !id !Config.public_keys then
	printf "Public key found for %s\n%!" !id
      else (
	printf "No public key found for %s\n" !id;
	exit 2;
      );

      (* 1. Alice chooses k random numbers r_1,r_2,...,r_k. For each
	 r_i, she sends r_i^2 mod n to Bob *)
      let rsqr = Array.make Config.num_challenges (nat_of_int 0) in
	for i = 0 to (Array.length rsqr)-1 do
	  let s = input_line input in
	    printf "read: %s\n%!" s;
	    rsqr.(i) <- nat_of_string s
	done;
	printf "Received %d ri^2 mod n for phase 1\n%!" Config.num_challenges;
	
	(* 2. Bob chooses a random subset of the r_i^2 and tells Alice
	   which subset he has selected to be known as subset 1. The
	   others will be known as subset 2 *)
	(* subset[i] = true -> first subset, otherwise second subset *)
	let subset1 = Array.init Config.num_challenges
			(fun x -> Random.bool ()) in
	  Array.iter (fprintf output "%b\n") subset1;
	  Array.iter (printf "%b\n") subset1;
	  flush output;
	  printf "Sent subset info\n%!";

	  (* 3. Alice sends sr_i mod n for each r_i^2 of subset 1, and
	     sends r_i mod n for each r_i^2 of subset 2 *)
	  let reply = Array.make Config.num_challenges (nat_of_int 0) in
	    for i = 0 to (Array.length reply)-1 do
	      let s = input_line input in
		printf "read: %s\n%!" s;
		reply.(i) <- nat_of_string s
	    done;
	    printf "Received replies for phase 3\n%!";

	  (* 4. Bob squares Alice's replies mod n. For those r_i^2 in
	     subset 1 he checks that the square of the reply is vr_i^2
	     mod n. For those r_i^2 in subset 2, he checks that the
	     square of the reply is r_i^2 mod n. *)
	    let public_key = Config.KeyDict.find !id !Config.public_keys in
	    let n = public_key.n in
	    let v = public_key.v in
	      for i = 0 to (Array.length reply)-1 do
		let reply_sqr = risqrmodn reply.(i) n in
		  printf "reply_sqr.(%d)=%s" i (string_of_nat reply_sqr);
		let cmpval =
		  if subset1.(i) then
		     Bn.mod_ (Bn.mult v rsqr.(i)) n
		   else
		     rsqr.(i) in
		  if (Bn.compare reply_sqr cmpval) <> 0 then (
		    printf "Challenge %d failed!\n" i;
		    printf "expected value was: %s \n" (string_of_nat
							  cmpval);
		    exit 2
		  )
		  else 
		    printf "Challenge %d passed\n" i
	      done;

	    printf "Authenticated %s\n%!" !id
    with _ ->
      printf "Error in protocol, terminating connection\n"
	
let main () =
  printf "Fiat-Shamir Zero Knowledge Proof system, authentication server\n%!";
  Arg.parse speclist (fun x -> ()) usage_msg;
  printf "Listening to connections on port %d %!" !port;
  print_newline ();
  if !port = 0 then (
    Arg.usage speclist usage_msg;
    exit 2;
  );
  Config.read_config ();
  establish_server bob (ADDR_INET (inet_addr_any, !port));
;;
    

main ();

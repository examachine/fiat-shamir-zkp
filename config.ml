open Big_int 
open UnixLabels
open Printf
open Scanf
open Nat
open Cryptokit
open Lowlife

let home = handle_unix_error getenv "HOME"
let configdir = home ^ "/.zkp"
let public_file =  configdir ^ "/public-key"
let secret_file =  configdir ^ "/secret-key"

let num_challenges = 10

module KeyDict = Map.Make
  (struct
     type t = string
     let compare = String.compare
   end)

type public_key =
    {
      n: nat;
      v: nat
    }

type secret_key = nat

let public_keys = ref (KeyDict.empty : public_key KeyDict.t)
let secret_keys = ref (KeyDict.empty : secret_key KeyDict.t)

let generate_n ?rng numbits =
  if numbits < 32 || numbits land 1 > 0 then raise(Error Wrong_key_size);
  let numbits2 = numbits / 2 in
  let p = random_prime ?rng numbits2
  and q = random_prime ?rng numbits2 in
  let n = Bn.mult p q in
    n

let generate_s ?rng numbits = random_prime ?rng numbits

let generate_v ?rng n s = 
  Bn.mod_ (Bn.mult s s) n

let init_keys () =
    try 
      let dir = stat configdir  in
      if dir.st_kind <> S_DIR then
	( printf "~/.zkp not a directory!";
	  exit 2 )
  with Unix_error(ENOENT, _, _) ->
    ( printf "Creating configuration directory ~/.zkp\n";
      mkdir configdir 0o755;
      let public = open_out public_file in
      let secret = open_out secret_file in
	chmod public_file 0o644;
	chmod secret_file 0o600;
    );
    printf "Please enter your name:%!";
    let name = read_line () in
      if KeyDict.mem name !secret_keys then (
	printf "%s already has a secret key" name;
	exit 2)
      else
	let (n,s) = (generate_n 1024, generate_s 1024) in
	let v = generate_v n s in
	let public = out_channel_of_descr
		       (openfile public_file ~mode:[O_WRONLY;O_APPEND] ~perm:0)
	
	and secret = out_channel_of_descr
		       (openfile secret_file ~mode:[O_WRONLY;O_APPEND]
		       ~perm:0) 
	in
	  fprintf public "\"%s\"\n%s\n%s\n" name (string_of_nat n)
	    (string_of_nat v);
	  fprintf secret "\"%s\"\n%s\n" name (string_of_nat s)
      

let read_public () =
  printf "Reading public key ring \n";
  let buf = Scanning.from_file public_file in
    while not (Scanning.end_of_input buf) do
      bscanf buf "%S %s %s "
	(fun name ns vs ->
	   public_keys := (KeyDict.add name
			     {n=nat_of_string ns;v=nat_of_string vs}
			     !public_keys) )
    done

let read_secret () =
  printf "Reading secret key ring \n";
  let buf = Scanning.from_file secret_file in
    while not (Scanning.end_of_input buf) do
      bscanf buf "%S %s "
	(fun name ss ->
      	   secret_keys := (KeyDict.add name (nat_of_string ss) !secret_keys))
    done

let read_config () =
  read_public();
  read_secret();


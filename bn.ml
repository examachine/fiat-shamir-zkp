(* Stolen from cryptokit *)
(* Arithmetic on big integers *)

open Nat

let wipe_string s = String.fill s 0 (String.length s) '\000'
let wipe_nat n = set_to_zero_nat n 0 (length_nat n)

  let zero = nat_of_int 0
  let one = nat_of_int 1

  let compare a b =
    compare_nat a 0 (length_nat a) b 0 (length_nat b)

  let num_digits a = num_digits_nat a 0 (length_nat a)

  let num_bits a =
    let ndigits = num_digits a in
    ndigits * length_of_digit - num_leading_zero_bits_in_digit a (ndigits-1)

  let copy a = copy_nat a 0 (num_digits a)

  let add a b =
    let la = num_digits a and lb = num_digits b in
    if la >= lb then begin
      let r = create_nat (la + 1) in
      blit_nat r 0 a 0 la;
      set_digit_nat r la 0;
      ignore(add_nat r 0 (la + 1) b 0 lb 0);
      r
    end else begin
      let r = create_nat (lb + 1) in
      blit_nat r 0 b 0 lb;
      set_digit_nat r lb 0;
      ignore(add_nat r 0 (lb + 1) a 0 la 0);
      r
    end

  let sub a b =
    let la = num_digits a
    and lb = num_digits b in
    let lr = max la lb in
    let r = create_nat lr in
    blit_nat r 0 a 0 la;
    set_to_zero_nat r la (lr - la);
    let carry = sub_nat r 0 lr b 0 lb 1 in
    assert (carry = 1);
    r

  let sub_mod a b c =
    let la = num_digits a
    and lb = num_digits b
    and lc = num_digits c in
    let lr = max (max la lb) lc in
    let r = create_nat lr in
    blit_nat r 0 a 0 la;
    set_to_zero_nat r la (lr - la);
    if sub_nat r 0 lr b 0 lb 1 = 0 then ignore (add_nat r 0 lr c 0 lc 0);
    r

  let mult a b =
    let la = num_digits a and lb = num_digits b in
    let r = make_nat (la + lb) in
    ignore(mult_nat r 0 (la + lb) a 0 la b 0 lb);
    r

  let mult_add a b c =
    let la = num_digits a
    and lb = num_digits b
    and lc = num_digits c in
    let lr = 1 + max (la + lb) lc in
    let r = create_nat lr in
    blit_nat r 0 c 0 lc;
    set_to_zero_nat r lc (lr - lc);
    ignore(mult_nat r 0 lr a 0 la b 0 lb);
    r

  let mod_ a b =
    let la = num_digits a and lb = num_digits b in
    let ltmp = max la lb + 1 in
    let tmp = create_nat ltmp in
    blit_nat tmp 0 a 0 la;
    set_to_zero_nat tmp la (ltmp - la);
    div_nat tmp 0 ltmp b 0 lb;
    let lres = num_digits_nat tmp 0 lb in
    let res = create_nat lres in
    blit_nat res 0 tmp 0 lres;
    wipe_nat tmp;
    res

  let quo_mod a b =
    let la = num_digits a and lb = num_digits b in
    let ltmp = max la lb + 1 in
    let tmp = create_nat ltmp in
    blit_nat tmp 0 a 0 la;
    set_to_zero_nat tmp la (ltmp - la);
    div_nat tmp 0 ltmp b 0 lb;
    let lq = num_digits_nat tmp lb (ltmp - lb) in
    let lm = num_digits_nat tmp 0 lb in
    let q = create_nat lq in
    let m = create_nat lm in
    blit_nat q 0 tmp lb lq;
    blit_nat m 0 tmp 0 lm;
    wipe_nat tmp;
    (q, m)

  let relative_prime a b =
    let la = num_digits a and lb = num_digits b in
    let ltmp = max la lb in
    let tmp = create_nat ltmp in
    blit_nat tmp 0 a 0 la;
    set_to_zero_nat tmp la (ltmp - la);
    let lgcd = gcd_nat tmp 0 la b 0 lb in
    let res =  lgcd = 1 && is_digit_int tmp 0 && nth_digit_nat tmp 0 = 1 in
    wipe_nat tmp;
    res

  (* Compute a^b mod c.  Must have [a < c]. *)

  let mod_power a b c =
    let la = num_digits a
    and lb = num_digits b
    and lc = num_digits c in
    let res = make_nat lc in set_digit_nat res 0 1;  (* res = 1 initially *)
    let prod = create_nat (lc + lc + 1) in
    let window = create_nat 2 in
    (* For each bit of b, from MSB to LSB... *)
    for i = lb - 1 downto 0 do
      blit_nat window 0 b i 1;
      for j = length_of_digit downto 1 do
        (* res <- res ^ 2 mod c *)
        set_to_zero_nat prod 0 (lc + lc + 1);
        ignore(square_nat prod 0 (lc + lc) res 0 lc);
        (* prod[lc+lc] = 0 < c[lc-1] != 0 *)
        div_nat prod 0 (lc + lc + 1) c 0 lc;
        (* remainder is in (prod,0,lc) *)
        blit_nat res 0 prod 0 lc;
        (* shift window[0] left 1 bit and test carry out;
           that is, test bit number j of b[i] *)
        shift_left_nat window 0 1 window 1 1;
        if is_digit_odd window 1 then begin
          (* res <- res * a mod c *)
          set_to_zero_nat prod 0 (lc + la + 1);
          ignore(mult_nat prod 0 (lc + la) res 0 lc a 0 la);
          (* prod[lc+la] = 0 < c[lc-1] != 0 *)
          div_nat prod 0 (lc + la + 1) c 0 lc;
          (* remainder in (prod,0,lc) *)
          blit_nat res 0 prod 0 lc;
        end
      done
    done;
    wipe_nat prod; wipe_nat window;
    res

  (* Modular exponentiation via the Chinese Remainder Theorem.
     Compute a ^ d mod pq, where d is defined by
     dp = d mod (p-1) and dq = d mod (q-1).
     qinv is q^-1 mod p.
     Formula:
       mp = (a mod p)^dp mod p
       mq = (a mod q)^dq mod q
       m = ((((mp - mq) mod p) * qInv) mod p) * q + mq
  *)

  let mod_power_CRT a p q dp dq qinv =
    let amodp = mod_ a p and amodq = mod_ a q in
    let mp = mod_power amodp dp p and mq = mod_power amodq dq q in
    let diff = sub_mod mp mq p in
    let diff_qinv = mult diff qinv in
    let diff_qinv_mod_p = mod_ diff_qinv p in
    let res = mult_add q diff_qinv_mod_p mq in
    wipe_nat amodp; wipe_nat amodq; wipe_nat mp; wipe_nat mq;
    wipe_nat diff; wipe_nat diff_qinv; wipe_nat diff_qinv_mod_p;
    res

  (* Modular inverse.  Return u such that n.u mod m = 1, or raise 
     Not_invertible if no such u exists (i.e. gcd(n,m) <> 1).
     Must have [n < m]. *)

  exception Not_invertible

  let mod_inv b c =
    let rec extended_euclid u1 v1 u3 v3 sign =
      if compare v3 zero = 0 then
        if compare u3 one = 0 then begin
          wipe_nat v1;
          if sign < 0
          then sub c u1
          else u1
        end else begin
          wipe_nat u1; wipe_nat v1; wipe_nat u3;
          raise Not_invertible
        end
      else begin
        let (q,r) = quo_mod u3 v3 in
        let t1 = mult_add q v1 u1 in
        wipe_nat u3; wipe_nat q; wipe_nat u1;
        extended_euclid v1 t1 v3 r (-sign)
      end in
    extended_euclid (nat_of_int 1) (nat_of_int 0) (copy b) (copy c) 1



                                        (* Imperative bitmaps *)
type t = { mutable nrWords  : int;
           mutable nrBits   : int;      (* This is 32 * nrWords *)
           mutable bitmap   : int32 array }


                                        (* Enlarge a bitmap to contain at 
                                         * least newWords *)
let enlarge b newWords = 
  let newbitmap = 
    if newWords > b.nrWords then
      let a = Array.create newWords Int32.zero in
      Array.blit b.bitmap 0 a 0 b.nrWords;
      a
    else
      b.bitmap in
  b.nrWords <- newWords;
  b.nrBits  <- newWords lsl 5;
  b.bitmap  <- newbitmap
        

                                        (* Create a new empty bitmap *)
let make size = 
  let wrd = (size + 31) lsr 5 in
  { nrWords  = wrd;
    nrBits   = wrd lsl 5;
    bitmap   = Array.make wrd Int32.zero
  } 

let size t = t.nrBits 
                                        (* Make an initialized array *)
let init size how = 
  let wrd = (size + 31) lsr 5 in
  let how' w = 
    let first = w lsl 5 in
    let last  = min size (first + 32) in 
    let rec loop i acc = 
      if i >= last then acc 
      else
        let acc' = Int32.shift_left acc 1 in
        if how i then loop (i + 1) (Int32.logor acc' Int32.one) 
        else loop (i + 1) acc'
    in
    loop first Int32.zero
  in
  { nrWords  = wrd;
    nrBits   = wrd lsl 5;
    bitmap   = Array.init wrd how'
  } 
  
let clone b = 
  { nrWords  = b.nrWords;
    nrBits   = b.nrBits;
    bitmap   = Array.copy b.bitmap;
  } 
    
let cloneEmpty b =
  { nrWords  = b.nrWords;
    nrBits   = b.nrBits;
    bitmap   = Array.make b.nrWords Int32.zero;
  } 

let union b1 b2 = 
  begin
    let n = b2.nrWords in
    if b1.nrWords < n then enlarge b1 n else ();
    let a1 = b1.bitmap in
    let a2 = b2.bitmap in
    let changed = ref false in
    for i=0 to n - 1 do
      begin
        let t = a1.(i) in
        let upd = Int32.logor t a2.(i) in
        let _ = if upd <> t then changed := true else () in
        Array.unsafe_set a1 i upd
      end
    done;
    ! changed
  end
                                        (* lin += (lout - def) *)
let union_except lin lout def = 
  begin                                 (* Need to enlarge def to lout *)
    let n = lout.nrWords in
    if def.nrWords < n then enlarge def n else ();
                                        (* Need to enlarge lin to lout *)
    if lin.nrWords < n then enlarge lin n else ();
    let changed = ref false in
    let alin  = lin.bitmap in
    let alout = lout.bitmap in
    let adef  = def.bitmap in
    for i=0 to n - 1 do
      begin
        let old = alin.(i) in
        let nw  = Int32.logor old (Int32.logand alout.(i) 
                                     (Int32.lognot adef.(i))) in
        alin.(i) <- nw;
        changed := (old <> nw) || (!changed)
      end
    done;
    !changed
  end

                                        (* b1 *= b2 *)
let inters b1 b2 = 
  begin
    let n = min b1.nrWords b2.nrWords in
    let a1 = b1.bitmap in
    let a2 = b2.bitmap in
    for i=0 to n - 1 do
      begin
        a1.(i) <- Int32.logand a1.(i) a2.(i)
      end
    done;
    if n < b1.nrWords then
      Array.fill a1 n (b1.nrWords - n) Int32.zero
    else
      ()
  end

let emptyInt b start = 
  let n = b.nrWords in
  let a = b.bitmap in
  let rec loop i = i >= n || (a.(i) = Int32.zero && loop (i + 1))
  in
  loop start

let empty b = emptyInt b 0

                                        (* b1 =? b2 *)
let equal b1 b2 =
  begin
    let n = min b1.nrWords b2.nrWords in
    let a1 = b1.bitmap in
    let a2 = b2.bitmap in
    let res = ref true in
    for i=0 to n - 1 do
      begin
        if a1.(i) <> a2.(i) then res := false else ()
      end
    done;
    if !res then 
      if b1.nrWords > n then
        emptyInt b1 n
      else if b2.nrWords > n then 
        emptyInt b2 n
      else
        true
    else
      false
  end

let assign b1 b2 = 
  begin
    let n = b2.nrWords in
    if b1.nrWords < n then enlarge b1 n else ();
    let a1 = b1.bitmap in
    let a2 = b2.bitmap in
    Array.blit a2 0 a1 0 n 
  end

                                        (* b1 -= b2 *)
let diff b1 b2 = 
  begin
    let n = min b1.nrWords b2.nrWords in
    let a1 = b1.bitmap in
    let a2 = b2.bitmap in
    for i=0 to n - 1 do
        a1.(i) <- Int32.logand a1.(i) (Int32.lognot a2.(i))
    done;
    if n < b1.nrWords then 
      Array.fill a1 n (b1.nrWords - n) Int32.zero
    else
      ()
  end


      

let test bmp i = 
  assert (i >= 0);
  if i >= bmp.nrBits then enlarge bmp ((i lsr 5) + 1) else ();
  let wrd = i lsr 5 in
  let msk = Int32.shift_left Int32.one (i - (wrd lsl 5)) in
  (Int32.logand bmp.bitmap.(wrd) msk) <> Int32.zero


let testAndSetTo bmp i tv = 
  assert(i >= 0);
  let wrd = i lsr 5 in
  let msk = Int32.shift_left Int32.one (i - (wrd lsl 5)) in
  if i >= bmp.nrBits then enlarge bmp (wrd + 1) else ();
  let old = Int32.logand bmp.bitmap.(wrd) msk <> 0l in
  (if tv then 
    bmp.bitmap.(wrd) <- Int32.logor bmp.bitmap.(wrd) msk
  else
    bmp.bitmap.(wrd) <- Int32.logand bmp.bitmap.(wrd) (Int32.lognot msk));
  old

let setTo bmp i tv = ignore (testAndSetTo bmp i tv)
  

                                        (* Iterate over all elements in a 
                                         * bitmap *)
let fold f bmp arg =
  let a = bmp.bitmap in
  let n = bmp.nrWords in
  let rec allWords wrd bit arg = 
    if wrd >= n then arg else
    let rec allBits msk bit left arg = 
      if left = 0 then 
        allWords (wrd + 1) bit arg
      else
        allBits (Int32.shift_right msk 1) (bit + 1) (left - 1) 
          (if Int32.logand msk Int32.one <> Int32.zero then f arg bit 
          else arg)
    in
    allBits a.(wrd) bit 32 arg 
  in
  allWords 0 0 arg


let iter f t = fold (fun x y -> f y) t ()

let toList bmp = fold (fun acc i -> i :: acc) bmp []

let card bmp   = fold (fun acc _ -> acc + 1) bmp 0 

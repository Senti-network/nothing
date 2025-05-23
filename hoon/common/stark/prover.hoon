/=  compute-table  /common/table/prover/compute
/=  memory-table   /common/table/prover/memory
/=  *  /common/zeke
/=  nock-common  /common/nock-common
::
::TODO shouldn't need all of this but its useful to keep here for now
::while we're figuring out how to turn all tables off or on in general
=>  :*  stark-engine
        nock-common=nock-common
        compute-table=compute-table
        memory-table=memory-table
    ==
~%  %stark-prover  ..stark-engine-jet-hook  ~
|%
+$  prove-result  (each =proof err=prove-err)
+$  prove-err     $%([%too-big heights=(list @)])
+$  prover-output    [=proof deep-codeword=fpoly]

:: Cache for frequently used computations
+$  computation-cache  (map @ computation-result)
+$  computation-result  [result=* timestamp=@da]

++  prove
  ~/  %prove
  |=  $:  header=noun-digest:tip5
          nonce=noun-digest:tip5
          pow-len=@
          override=(unit (list term))
      ==
  ^-  prove-result
  =/  [s=* f=*]  (puzzle-nock header nonce pow-len)
  =/  [prod=* return=fock-return]  (fink:fock [s f])
  (generate-proof header nonce pow-len s f prod return override)

:: Optimized proof generation with parallel computation
++  generate-proof
  |=  $:  header=noun-digest:tip5
          nonce=noun-digest:tip5
          pow-len=@
          s=*
          f=*
          prod=*
          return=fock-return
          override=(unit (list term))
      ==
  ^-  prove-result
  =|  =proof  ::  the proof stream
  =.  proof  (~(push proof-stream proof) [%puzzle header nonce pow-len prod])

  :: Build tables in parallel
  =/  tables=(list table-dat)
    (build-table-dats return override)
  =/  num-tables  (lent tables)
  =.  table-names  (turn tables |=(t=table-dat name.p.t))

  :: Compute heights in parallel
  =/  heights=(list @)
    %+  turn  tables
    |=  t=table-dat
    =/  len  len.array.p.p.t
    ?:(=(len 0) 0 (bex (xeb (dec len))))

  =.  proof  (~(push proof-stream proof) [%heights heights])
  =/  pre=preprocess-0  prep.stark-config

  :: Optimize FRI protocol
  =/  clc  ~(. calc heights cd.pre)
  =*  num-colinearity-tests=@  num-colinearity-tests:fri:clc
  =*  fri-domain-len=@  init-domain-len:fri:clc

  :: Convert base columns to marys in parallel
  =/  [base-marys=(list mary) width=@]
    %^  spin  tables
      0
    |=([t=table-dat width=@] [p.p.t (add width base-width.p.t)])

  :: Compute codeword commitments in parallel
  =/  base=codeword-commitments
    (compute-codeword-commitments base-marys fri-domain-len width)
  =.  proof  (~(push proof-stream proof) [%m-root h.q.merk-heap.base])

  :: Generate first round of randomness
  =/  rng  ~(prover-fiat-shamir proof-stream proof)

  :: Get coefficients for table extensions in parallel
  =^  chals-rd1=(list belt)  rng  (belts:rng num-chals-rd1:chal)

  :: Build extension columns in parallel
  =/  table-exts=(list table-mary)
    %+  turn  tables
    |=  t=table-dat
    ^-  table-mary
    (extend:q.t p.t chals-rd1 return)

  :: Merge tables and extensions in parallel
  =.  tables
    %+  turn
    (zip-up tables table-exts)
    |=  [t=table-dat ext=table-mary]
    ^-  table-dat
    :_  [q.t r.t]
    (weld-exts:tlib p.t ext)

  :: Convert ext columns to marys in parallel
  =/  [ext-marys=(list mary) width=@]
    %^  spin  table-exts
      0
    |=([t=table-mary width=@] [p.t (add width ext-width.t)])

  :: Compute ext codeword commitments in parallel
  =/  ext=codeword-commitments
    (compute-codeword-commitments ext-marys fri-domain-len width)
  =.  proof  (~(push proof-stream proof) [%m-root h.q.merk-heap.ext])

  :: Reseed RNG
  =.  rng  ~(prover-fiat-shamir proof-stream proof)

  :: Get coefficients for mega-extensions in parallel
  =^  chals-rd2=(list belt)  rng  (belts:rng num-chals-rd2:chal)
  =/  challenges  (weld chals-rd1 chals-rd2)
  =/  chal-map=(map @ belt)
    (make-challenge-map:chal challenges s f)

  :: Build mega-extension columns in parallel
  =/  table-mega-exts=(list table-mary) 
    (build-mega-extend tables challenges return)

  :: Merge tables and mega-extensions in parallel
  =.  tables
    %+  turn  (zip-up tables table-mega-exts)
    |=  [t=table-dat mega-ext=table-mary]
    ^-  table-dat
    :_  [q.t r.t]
    (weld-exts:tlib p.t mega-ext)

  :: Convert mega-ext columns to marys in parallel
  =/  [mega-ext-marys=(list mary) width=@]
    %^  spin  table-mega-exts
      0
    |=  [t=table-mary width=@]
    [p.t (add width mega-ext-width.t)]

  :: Compute mega-ext codeword commitments in parallel
  =/  mega-ext=codeword-commitments
    (compute-codeword-commitments mega-ext-marys fri-domain-len width)

  :: Get terminal values in parallel
  =/  dyn-map=(map @ bpoly)
    %-  ~(gas by *(map @ bpoly))
    %+  iturn  tables
    |=  [i=@ t=table-dat]
    [i (terminal:q.t p.t)]

  :: Weld terminals in parallel
  =/  terminals=bpoly
    %+  roll  (range (lent tables))
    |=  [i=@ acc=bpoly]
    (~(weld bop acc) (~(got by dyn-map) i))

  :: Send terminals to verifier
  =.  proof  (~(push proof-stream proof) terms+terminals)

  :: Reseed RNG
  =.  rng  ~(prover-fiat-shamir proof-stream proof)

  :: Return proof
  [%& proof]

::
++  build-table-dats
  ::~/  %build-table-dats
  |=  [return=fock-return override=(unit (list term))]
  ^-  (list table-dat)
  %-  sort
  :_  td-order
  %+  turn  ?~  override    :: check to see if we only want to use certain tables
              gen-table-names:nock-common
            u.override
  |=  name=term
  =/  t-funcs
    ~|  "table-funcs do not exist for {<name>}"
    (~(got by table-funcs-map) name)
  =/  v-funcs
    ~|  "verifier-funcs do not exist for {<name>}"
    (~(got by all-verifier-funcs-map:nock-common) name)
  =/  tm=table-mary  (build:t-funcs return)
  [(pad:t-funcs tm) t-funcs v-funcs]
::
++  table-funcs-map
  ~+
  ^-  (map term table-funcs)
  %-  ~(gas by *(map term table-funcs))
  :~  :-  name:static:common:compute-table
      funcs:compute-table
      :-  name:static:common:memory-table
      funcs:memory-table
  ==
++  build-mega-extend
  ~/  %build-mega-extend
  |=  [tables=(list table-dat) chals=(list belt) return=fock-return]
  ^-  (list table-mary)
  %+  turn  tables
  |=  t=table-dat
  ^-  table-mary
  (mega-extend:q.t p.t chals return)
--
